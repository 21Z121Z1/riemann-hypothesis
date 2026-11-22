import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalInnerProductLift
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasComplementOfBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedSecondIsometricO1
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ProjSpace GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Points
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM)

namespace GlobalTheory.TautFlag

theorem detUnit_chartSec_eq {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (i j : L.ι) :
    (isFrame_chartSec hL i).detUnit (isFrame_chartSec hL j) inf_le_left inf_le_right = L.g i j := by
  refine (Units.ext ?_ : L.g i j = _).symm
  have e : resM (toMod L) inf_le_right (LB.chartSec hL j) = (L.g i j : Γ(X, L.U i ⊓ L.U j)) •
      (isFrame_chartSec hL i).basis (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) 0 := by
    rw [IsFrame.basis_apply]
    refine ((LB.chartEquiv hL i inf_le_left).symm_apply_apply _).symm.trans ?_
    rw [LB.chartEquiv_symm_apply, LB.chartEquiv_apply]
    congr 1
    exact (resG_resG _ _ _).trans ((resG_resG _ _ _).trans (resG_self _ _))
  rw [IsFrame.val_detUnit, Module.Basis.det_apply, Matrix.det_fin_one, Module.Basis.toMatrix_apply,
    e, map_smul, Module.Basis.repr_self]
  simp

theorem detUnit_eq_g_of_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {F : X.Modules} (φ : F ≅ toMod L)
    (i j : L.ι) {e : Fin 1 → Γ(F, L.U i)} {f : Fin 1 → Γ(F, L.U j)} (h : IsFrame e) (k : IsFrame f)
    (he : e = fun _ => φ.inv.app _ (LB.chartSec hL i)) (hf : f = fun _ => φ.inv.app _ (LB.chartSec hL j)) :
    h.detUnit k inf_le_left inf_le_right = L.g i j := by
  subst he hf
  exact (IsFrame.detUnit_map_iso (isFrame_chartSec hL i) (isFrame_chartSec hL j) φ.inv _ _).trans
    (detUnit_chartSec_eq hL i j)

theorem adapt₁_quot_e (j : Fin 2) : (adapt₁ j).quot.e = fun _ => (grIso₁ seq seq_shortExact isVB_seq₁
    (isVB_freeModule_fin _ 2) (isVB_toMod (O1_isLB ℤ 1))).inv.app _ (LB.chartSec (O1_isLB ℤ 1) j) := by
  have e : (VMetric.stepSeq flag 1).g = quotMap ≫ (grIso₁ seq seq_shortExact isVB_seq₁ (isVB_freeModule_fin _ 2)
    (isVB_toMod (O1_isLB ℤ 1))).inv := (Iso.eq_comp_inv _).2 π_grIso₁
  funext _
  exact (congrArg (fun φ => φ.app _ (t j)) e).trans ((app_app _ _ _ _).symm.trans (congrArg _ (quotMap_app_t_eq_chartSec j)))

theorem g_adapt₁_quot (j j' : Fin 2) :
    (VB.det (flag.gr 1) 1).g (adapt₁ j).quot (adapt₁ j').quot = (O1 ℤ 1).g j j' :=
  detUnit_eq_g_of_iso (O1_isLB ℤ 1) _ j j' _ _ (adapt₁_quot_e j) (adapt₁_quot_e j')

variable {σ : ℤ →+* ℂ}

theorem nsqV_eq_one_add (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ}
    (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j)) : nsqV j y = ((1 + ‖ipVT j y‖ ^ 2 : ℝ) : ℂ) := by
  rcases (by fin_cases j <;> simp : j = 0 ∨ j = 1) with rfl | rfl
  · have r : ev _ σ _ (ratio ℤ 1 0 0) y = 1 := by rw [ev_eq hy, ratio, ratioOn_self, map_one]
    rw [nsqV, r, map_one, mul_one, Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one]
    rfl
  · have r : ev _ σ _ (ratio ℤ 1 1 1) y = 1 := by rw [ev_eq hy, ratio, ratioOn_self, map_one]
    rw [nsqV, r, map_one, mul_one, Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_one,
      add_comm, ← norm_neg]
    rfl

theorem det_quotGram_one_add (b : ℂ) :
    (quotGram (Matrix.fromBlocks (Matrix.of fun (_ _ : Fin 1) => ((1 + ‖b‖ ^ 2 : ℝ) : ℂ))
      (Matrix.of fun (_ _ : Fin 1) => b) (Matrix.of fun (_ _ : Fin 1) => starRingEnd ℂ b) 1)).det =
      (((1 + ‖b‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have h : ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
  have e : starRingEnd ℂ b * b = ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) - 1 := by
    rw [mul_comm, Complex.mul_conj']
    push_cast
    ring
  rw [Complex.ofReal_inv]
  generalize ((1 + ‖b‖ ^ 2 : ℝ) : ℂ) = n at h e
  simp only [quotGram, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.det_unique, Matrix.sub_apply, Matrix.mul_apply, Matrix.inv_subsingleton, Fintype.sum_unique]
  simp
  field_simp
  linear_combination -e

theorem fubini_study_weight_chart_eq (j : Fin 2) {y : CxPts (PSpace.str ℤ 1) σ}
    (hy : y ∈ ptsIn (PSpace.str ℤ 1) σ (chart ℤ 1 j)) :
    ((hermitianTwistingSheaf ℤ 1).φ σ).φ j y = Real.log (1 + ‖ipVT j y‖ ^ 2) := by
  refine (Weight.fsBasis_φ _ _ (iSup_nonzeroLocus_coord ℤ 1) 1 (by simp) _ _).trans (congrArg _ ?_)
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine (Fin.sum_univ_two _).trans (Complex.ofReal_injective (Eq.trans ?_ (nsqV_eq_one_add j hy)))
  rw [nsqV, Complex.mul_conj', Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_pow]
  rfl

theorem isometric_grLB_one : (VMetric.grLB flag 1 stdH.cInf).Isometric (hermitianTwistingSheaf ℤ 1) := by
  refine HermLB.Isometric.symm (HermLB.isometric_of_chart (L := hermitianTwistingSheaf ℤ 1) (M := VMetric.grLB flag 1 stdH.cInf)
    (fun j : Fin 2 => (adapt₁ j).quot) (fun _ => le_rfl)
    (fun x j j' _ _ => congrArg (gm (𝟙 _) x _) (g_adapt₁_quot j j').symm) fun σ j y hy => ?_)
  have e := ((stdH.h.stepMet flag 1).met σ).quot_G (VMetric.stepSeq_shortExact flag 1)
    (flag.isVB (Fin.castSucc 1)) (flag.isVB_gr 1) (adapt₁ j) hy
  have e₂ := e.trans (congrArg quotGram (gram_adapt₁ j hy))
  refine (congrArg (fun M : Matrix (Fin 1) (Fin 1) ℂ => -Real.log M.det.re) e₂).trans
    (Eq.trans ?_ (fubini_study_weight_chart_eq j hy).symm)
  beta_reduce
  rw [nsqV_eq_one_add j hy, det_quotGram_one_add, Complex.ofReal_re, Real.log_inv, neg_neg]

end GlobalTheory.TautFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.UPel.HT.MapComp

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ : G''.left ⟶ G'.left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
    by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

theorem isSquare_unique {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {φ : G'.left ⟶ G.left}
    {a b : (G' ⊗ G').left ⟶ (G ⊗ G).left} (ha : IsSquare φ a) (hb : IsSquare φ b) : a = b := by
  apply pullback.hom_ext
  · exact ha.1.trans hb.1.symm
  · exact ha.2.trans hb.2.symm

theorem exists_isSquare {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (w : φ ≫ G.hom = G'.hom ≫ f) : ∃ φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left, IsSquare φ φ₂ :=
  ⟨_, congrArg (fun z => z.left) (lift_fst (pushPt w (fst G' G')) (pushPt w (snd G' G'))),
    congrArg (fun z => z.left) (lift_snd (pushPt w (fst G' G')) (pushPt w (snd G' G')))⟩

end GlobalTheory.UPel.HT.MapComp

namespace GlobalTheory.UPel.HT

open GlobalTheory.UPel.HT.MapComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

def MapComp.comp {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m₁ : ObjMap o₁ o₂ f) (m₂ : ObjMap o₂ o₃ g) : ObjMap o₁ o₃ (f ≫ g) where
  φ := m₁.φ ≫ m₂.φ
  φ₂ := m₁.φ₂ ≫ m₂.φ₂
  cart := m₁.cart.comp m₂.cart
  sq := isSquare_comp m₁.sq m₂.sq
  act c := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) m₁.pol (lbIso_pull_comp m₂.pol m₁.φ₂ rfl)
  eta y := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

theorem MapComp.cancel {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
    {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (m : ObjMap o₁ o₃ (f ≫ g)) (m₂ : ObjMap o₂ o₃ g) : Nonempty (ObjMap o₁ o₂ f) := by
  have w : m.φ ≫ o₃.A.hom = (o₁.A.hom ≫ f) ≫ g := by rw [m.cart.1.w, Category.assoc]
  set φ := m₂.cart.1.lift m.φ (o₁.A.hom ≫ f) w
  have hφ : φ ≫ m₂.φ = m.φ := m₂.cart.1.lift_fst _ _ _
  have hφ' : φ ≫ o₂.A.hom = o₁.A.hom ≫ f := m₂.cart.1.lift_snd _ _ _
  have n : IsGrpPullback o₁.A o₃.A (f ≫ g) (φ ≫ m₂.φ) := by rw [hφ]; exact m.cart
  obtain ⟨φ₂, sq⟩ := exists_isSquare hφ'
  have e : m.φ₂ = φ₂ ≫ m₂.φ₂ := isSquare_unique m.sq (hφ ▸ isSquare_comp sq m₂.sq)
  have hact : ∀ c, (o₁.act.act c).left ≫ φ = φ ≫ (o₂.act.act c).left := by
    intro c
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.act, Category.assoc, m₂.act, ← Category.assoc, hφ]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w, hφ']
  have heta : ∀ y, (o₁.eta y).left ≫ φ = f ≫ (o₂.eta y).left := by
    intro y
    apply m₂.cart.1.hom_ext
    · rw [Category.assoc, hφ, m.eta, Category.assoc, Category.assoc, m₂.eta]
    · rw [Category.assoc, hφ', ← Category.assoc, Over.w, Category.assoc, Over.w]
      show 𝟙 _ ≫ f = f ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
  exact ⟨{ φ := φ
           φ₂ := φ₂
           cart := m₂.cart.cancel n hφ'
           sq := sq
           act := hact
           pol := LBIso.trans o₁.isLB (pull_isLB o₃.isLB _) (pull_isLB o₂.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m₂.pol φ₂ e))
           eta := heta }⟩

theorem objMap_comp_cancel (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : Obj b N s₁) (o₂ : Obj b N s₂)
    (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃) :
    (Nonempty (ObjMap o₁ o₂ f) → Nonempty (ObjMap o₂ o₃ g) → Nonempty (ObjMap o₁ o₃ (f ≫ g))) ∧
      (Nonempty (ObjMap o₁ o₃ (f ≫ g)) → Nonempty (ObjMap o₂ o₃ g) → Nonempty (ObjMap o₁ o₂ f)) :=
  ⟨fun ⟨m₁⟩ ⟨m₂⟩ => ⟨MapComp.comp m₁ m₂⟩, fun ⟨m⟩ ⟨m₂⟩ => MapComp.cancel m m₂⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianMatrixGreenValue
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame

open scoped ComplexOrder

namespace GlobalTheory.TautDensity

def frameMat (w : ReciprocityTheory.L2DbarEstimates.V 1) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  fromBlocks 1 0 (of fun _ _ => w 0) 1

def gramMat (w : ReciprocityTheory.L2DbarEstimates.V 1) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ :=
  fromBlocks (of fun _ _ => 1 + w 0 * starRingEnd ℂ (w 0)) (of fun _ _ => w 0)
    (of fun _ _ => starRingEnd ℂ (w 0)) 1

theorem gramMat_eq (w : ReciprocityTheory.L2DbarEstimates.V 1) : gramMat w = (frameMat w)ᵀ * 1 * (frameMat w)ᴴᵀ := by
  ext (a | a) (b | b) <;>
    simp [gramMat, frameMat, mul_apply, Subsingleton.elim a 0, Subsingleton.elim b 0]

theorem det_frameMat (w : ReciprocityTheory.L2DbarEstimates.V 1) : (frameMat w).det = 1 := by
  rw [frameMat, det_fromBlocks_zero₁₂]; simp

theorem hasFDerivAt_crd (z : ReciprocityTheory.L2DbarEstimates.V 1) :
    HasFDerivAt (fun w : ReciprocityTheory.L2DbarEstimates.V 1 => w 0)
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : ReciprocityTheory.L2DbarEstimates.V 1 →L[ℂ] ℂ) z :=
  (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : ReciprocityTheory.L2DbarEstimates.V 1 →L[ℂ] ℂ).hasFDerivAt

theorem contDiffAt_frameMat (z : ReciprocityTheory.L2DbarEstimates.V 1) (a b : Fin 1 ⊕ Fin 1) :
    ContDiffAt ℂ 1 (fun w => frameMat w a b) z := by
  rcases a with a | a <;> rcases b with b | b
  exacts [contDiffAt_const, contDiffAt_const,
    (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1) : ReciprocityTheory.L2DbarEstimates.V 1 →L[ℂ] ℂ).contDiff.contDiffAt,
    contDiffAt_const]

theorem mContDiffAt_frameMat (z : ReciprocityTheory.L2DbarEstimates.V 1) : MContDiffAt 1 frameMat z :=
  fun a b => (contDiffAt_frameMat z a b).restrict_scalars ℝ

theorem mdbar_frameMat (z η : ReciprocityTheory.L2DbarEstimates.V 1) : mdbar frameMat z η = 0 := by
  ext a b
  rw [mdbar_apply, dbar_eq_zero ((contDiffAt_frameMat z a b).differentiableAt one_ne_zero)]
  rfl

theorem mdel_frameMat (z ξ : ReciprocityTheory.L2DbarEstimates.V 1) :
    mdel frameMat z ξ = fromBlocks 0 0 (of fun _ _ => ξ 0) 0 := by
  ext a b
  rw [mdel_apply, del_eq_fderiv ((contDiffAt_frameMat z a b).differentiableAt one_ne_zero)]
  rcases a with a | a <;> rcases b with b | b
  · simp [frameMat]
  · simp [frameMat]
  · change fderiv ℂ (fun w : ReciprocityTheory.L2DbarEstimates.V 1 => w 0) z ξ = ξ 0
    rw [(hasFDerivAt_crd z).fderiv]; rfl
  · simp [frameMat]

theorem mContDiffAt_gramMat (z : ReciprocityTheory.L2DbarEstimates.V 1) : MContDiffAt 1 gramMat z := by
  rw [funext gramMat_eq]
  exact ((mContDiffAt_frameMat z).transpose.mul (mContDiffAt_const 1)).mul
    (mContDiffAt_frameMat z).conjTranspose.transpose

theorem posDef_gramMat (w : ReciprocityTheory.L2DbarEstimates.V 1) : (gramMat w).PosDef := by
  rw [gramMat_eq]
  exact posDef_chg ((isUnit_iff_isUnit_det _).2 (by rw [det_frameMat]; exact isUnit_one)) PosDef.one

theorem secondForm_gramMat (z ξ : ReciprocityTheory.L2DbarEstimates.V 1) :
    secondForm gramMat z ξ = of fun _ _ => ξ 0 := by
  have hu : IsUnit (frameMat z).det := by rw [det_frameMat]; exact isUnit_one
  have hi : (frameMat z)⁻¹ = fromBlocks 1 0 (of fun _ _ => -z 0) 1 := by
    refine inv_eq_left_inv ?_
    ext (a | a) (b | b) <;> obtain rfl := Subsingleton.elim a 0 <;>
      obtain rfl := Subsingleton.elim b 0 <;> simp [frameMat, mul_apply]
  rw [secondForm_eq, funext gramMat_eq, conn_changeFrame (H := fun _ => 1) (mContDiffAt_const 1)
    (by simp) (mContDiffAt_frameMat z) hu (mdbar_frameMat z), conn_const, Matrix.zero_mul, zero_add,
    mdel_frameMat, hi, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  simp

theorem ofReal_u (z : ReciprocityTheory.L2DbarEstimates.V 1) :
    ((ArithHeightModel.u z : ℝ) : ℂ) = 1 + z 0 * starRingEnd ℂ (z 0) := by
  rw [Complex.mul_conj, Complex.normSq_apply, ArithHeightModel.u]
  push_cast; ring

theorem inv_of_const (c : ℂ) : (of fun _ _ => c : Matrix (Fin 1) (Fin 1) ℂ)⁻¹ = of fun _ _ => c⁻¹ := by
  ext a b
  simp [Ring.inverse_eq_inv', Subsingleton.elim a 0, Subsingleton.elim b 0]

theorem subGram_gramMat (z : ReciprocityTheory.L2DbarEstimates.V 1) :
    subGram (gramMat z) = of fun _ _ => ((ArithHeightModel.u z : ℝ) : ℂ) := by
  rw [ofReal_u]; rfl

theorem quotGram_gramMat (z : ReciprocityTheory.L2DbarEstimates.V 1) :
    quotGram (gramMat z) = of fun _ _ => ((ArithHeightModel.u z : ℝ) : ℂ)⁻¹ := by
  have h0 : ((ArithHeightModel.u z : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ArithHeightModel.u_pos z).ne'
  rw [quotGram, gramMat, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, ← ofReal_u, inv_of_const]
  ext a b
  simp only [Subsingleton.elim a 0, Subsingleton.elim b 0, Matrix.sub_apply, one_apply_eq, mul_apply,
    Fin.sum_univ_one, of_apply]
  field_simp
  rw [ofReal_u]; ring

theorem density_eq : ∀ v : ReciprocityTheory.L2DbarEstimates.V 1, 2 * diagVal (extTrace (fun w : ReciprocityTheory.L2DbarEstimates.V 1 => (Matrix.fromBlocks (Matrix.of fun _ _ => 1 + w 0 * starRingEnd ℂ (w 0)) (Matrix.of fun _ _ => w 0) (Matrix.of fun _ _ => starRingEnd ℂ (w 0)) 1 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ)) v) (EuclideanSpace.single 0 1) = 1 / Real.pi * (ArithHeightModel.u v ^ 2)⁻¹ := by
  intro v
  change 2 * diagVal (extTrace gramMat v) (EuclideanSpace.single 0 1) = _
  have e : -Complex.I * kappa = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
    rw [kappa, ← mul_div_assoc, neg_mul, Complex.I_mul_I]; simp
  have ht : (secondForm gramMat v (EuclideanSpace.single 0 1) *
      secondFormAdj gramMat v (EuclideanSpace.single 0 1)).trace =
      (((ArithHeightModel.u v ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [secondFormAdj, secondForm_gramMat, subGram_gramMat, quotGram_gramMat, adj,
      ← transpose_nonsing_inv, inv_of_const]
    simp [trace, mul_apply, sq]
  rw [diagVal, extTrace_eq (mContDiffAt_gramMat v) (.of_forall posDef_gramMat), ← mul_assoc, e,
    Complex.re_ofReal_mul, ht, Complex.ofReal_re]
  ring

end GlobalTheory.TautDensity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSpaceAddSignatureExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.SignatureAddition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem coords_gram (B : HSpace E) (x y : B.V) :
    ∑ l, (∑ k, star (B.frame.repr x k) * B.gram k l) * B.frame.repr y l = B.hT x y := by
  conv_rhs => rw [← B.frame.sum_repr x, ← B.frame.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, HSpace.gram, RingHom.id_apply, starRingEnd_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

def middleSymmetricBasisVector (E : Type) [Field E] (c : ℕ) (p : Fin c) : Fin c → E :=
  Pi.single p (if 2 * p.1 + 1 ≤ c then 1 else -1 / 2) +
    Pi.single p.rev (if 2 * p.1 + 1 < c then 1 else if 2 * p.1 + 1 = c then 0 else 1 / 2)

theorem middleSymmetricBasisVectors_gram_antiDiagonal (c : ℕ) (neg : Bool) (p q : Fin c) :
    Examples₂.diagForm c (GlobalTheory.UnitPerp.negFrom c (if neg then c / 2 else (c + 1) / 2)) (middleSymmetricBasisVector E c p) (middleSymmetricBasisVector E c q) =
      antiDiagonalSignGramMatrix c (if neg then -1 else 1) p q := by
  have hp := p.2
  have hq := q.2
  obtain ⟨P, hP⟩ : ∃ P, P = if neg then c / 2 else (c + 1) / 2 := ⟨_, rfl⟩
  have hP1 : c / 2 ≤ P ∧ P ≤ (c + 1) / 2 := by rw [hP]; split_ifs <;> omega
  have hm : 2 * p.1 + 1 = c → (P ≤ p.1 ↔ neg = true) := by
    intro h; rw [hP]; cases neg <;> simp <;> omega
  rw [← hP]
  simp only [middleSymmetricBasisVector, map_add, LinearMap.add_apply, Examples₂.diagForm_single_left, Pi.single_apply, Pi.add_apply,
    GlobalTheory.UnitPerp.negFrom, Examples₂.sgn, antiDiagonalSignGramMatrix, Fin.ext_iff, Fin.val_rev, decide_eq_true_eq]
  generalize p.1 = a at *
  generalize q.1 = b at *
  clear hP
  have e1 : (c - (a + 1) = c - (b + 1)) = (a = b) := propext (by omega)
  have e2 : (a = c - (b + 1)) = (a + b + 1 = c) := propext (by omega)
  have e3 : (c - (a + 1) = b) = (a + b + 1 = c) := propext (by omega)
  simp only [e1, e2, e3]
  by_cases h1 : a = b <;> by_cases h2 : a + b + 1 = c
  · subst h1
    have h : 2 * a + 1 = c := by omega
    simp only [if_pos h.le, if_pos h, if_neg (show ¬ 2 * a + 1 < c by omega), hm h, if_pos h2]
    cases neg <;> simp
  · subst h1
    rcases (show 2 * a + 1 < c ∨ c < 2 * a + 1 by omega) with h | h
    · simp only [if_pos h.le, if_pos h, if_neg (show ¬ P ≤ a by omega), if_pos (show P ≤ c - (a + 1) by omega), if_neg h2]
      simp
    · simp only [if_neg h.not_ge, if_neg h.not_gt, if_neg h.ne', if_pos (show P ≤ a by omega),
        if_neg (show ¬ P ≤ c - (a + 1) by omega), if_neg h2]
      norm_num
  · rcases (show (2 * a + 1 < c ∧ c < 2 * b + 1) ∨ (2 * b + 1 < c ∧ c < 2 * a + 1) by omega) with ⟨h, h'⟩ | ⟨h', h⟩
    · simp only [if_pos h.le, if_pos h, if_neg (show ¬ P ≤ a by omega), if_pos (show P ≤ c - (a + 1) by omega),
        if_neg h'.not_ge, if_neg h'.not_gt, if_neg h'.ne', if_neg h1, if_pos h2]
      norm_num
    · simp only [if_neg h.not_ge, if_neg h.not_gt, if_neg h.ne', if_pos (show P ≤ a by omega),
        if_neg (show ¬ P ≤ c - (a + 1) by omega), if_pos h'.le, if_pos h', if_neg h1, if_pos h2]
      norm_num
  · simp only [if_neg h1, if_neg h2, add_zero, mul_zero]

end Generic

theorem exists_hermitian_space_add_signature (D : D7) (A : HSp D) (p q c : ℕ) (neg : Bool) (hA : A.SigOK) (hs : ∀ τ, A.sig τ = (p, q)) :
    ∃ B : HSp D, Nonempty (HermitianOrthogonalExtensionData A B c (if neg then -1 else 1)) ∧ B.SigOK ∧
      ∀ τ, B.sig τ = (p + (if neg then c / 2 else (c + 1) / 2), q + (if neg then (c + 1) / 2 else c / 2)) := by
  have hc : c = (if neg then c / 2 else (c + 1) / 2) + (if neg then (c + 1) / 2 else c / 2) := by
    split_ifs <;> omega
  have hW := GlobalTheory.UnitPerp.ofKind_stdSpace (E := D.host.E) hc
  set W : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral c (GlobalTheory.UnitPerp.negFrom c (if neg then c / 2 else (c + 1) / 2))
    (if neg then c / 2 else (c + 1) / 2) (if neg then (c + 1) / 2 else c / 2) with hWd
  refine ⟨GlobalTheory.Doubling.hsum A W, ⟨?_⟩, GlobalTheory.Doubling.sigOK_hsum hA hW.2.1, fun τ => ?_⟩
  · refine
      { ι := LinearMap.inl _ _ _
        isom := GlobalTheory.Doubling.isIsomEmb_inl A W
        a := fun k j => (GlobalTheory.Doubling.hsum A W).frame.repr ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V) k
        gram := Matrix.ext fun i j => ?_
        perp := Matrix.ext fun i j => ?_
        rank := rfl }
    · refine Eq.trans (coords_gram (GlobalTheory.Doubling.hsum A W) ((0, middleSymmetricBasisVector D.host.E c i) : A.V × W.V)
        ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V)) ?_
      refine (GlobalTheory.Doubling.orthSum_apply A W _ _).trans ?_
      rw [map_zero, zero_add]
      exact middleSymmetricBasisVectors_gram_antiDiagonal c neg i j
    · refine Eq.trans ?_ ((coords_gram (GlobalTheory.Doubling.hsum A W) ((A.frame i, 0) : A.V × W.V)
        ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V)).trans ?_)
      · have e : frameMat (GlobalTheory.Doubling.hsum A W) A (LinearMap.inl _ _ _) =
            fun k i => (GlobalTheory.Doubling.hsum A W).frame.repr ((A.frame i, 0) : A.V × W.V) k :=
          Matrix.ext fun k i => LinearMap.toMatrix_apply A.frame (GlobalTheory.Doubling.hsum A W).frame _ k i
        rw [e]
        rfl
      · refine (GlobalTheory.Doubling.orthSum_apply A W _ _).trans ?_
        rw [map_zero, map_zero, zero_add]
        rfl
  · show A.sig τ + W.sig τ = _
    rw [hs τ]
    rfl

end GlobalTheory.SignatureAddition

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSchemeFiniteFreeAlgebraAffineExists
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

theorem exists_basis_fin (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B]
    [Module.Finite A B] : ∃ N, Nonempty (Module.Basis (Fin N) A B) := by
  by_cases hA : Nontrivial A
  · exact ⟨_, ⟨Module.finBasis A B⟩⟩
  · rw [not_nontrivial_iff_subsingleton] at hA
    have : Subsingleton B := Module.subsingleton A B
    exact ⟨0, ⟨Module.Basis.empty B⟩⟩

theorem hilbertScheme_exists : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] (r : ℕ), ∃ (H : Scheme.{0}) (h : H ⟶ Spec (CommRingCat.of A)) (U : Scheme.{0}) (u : U ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) h), IsProper h ∧ IsClosedImmersion u ∧ IsFinite (u ≫ pullback.snd _ h) ∧ Flat (u ≫ pullback.snd _ h) ∧ (∀ y, (u ≫ pullback.snd _ h).finrank y = r) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Spec (CommRingCat.of A)) (V : Scheme.{0}) (v : V ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B))) g), IsClosedImmersion v → IsFinite (v ≫ pullback.snd _ g) → Flat (v ≫ pullback.snd _ g) → (∀ y, (v ≫ pullback.snd _ g).finrank y = r) → ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U, IsPullback v w (pullback.map _ g _ h (𝟙 _) f (𝟙 _) (by simp) (by rw [Category.comp_id, hf])) u := by
  intro A B _ _ _ _ _ r
  obtain ⟨N, ⟨e⟩⟩ := exists_basis_fin A B
  let F := GlobalTheory.HilbAff.functor A B r
  choose X x hX hlft hbas huniv using fun σ : Fin r ↪ Fin N => GlobalTheory.T.affineHilbertChart_representable A B N r e σ
  choose W hW _ using fun (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : F.obj (op Z)) =>
    GlobalTheory.T.exists_open_affineHilbertChartBasic_locus A B N r e σ Z y
  have stab : ∀ σ (Z : Scheme.{0}) (g : Z ⟶ X σ), GlobalTheory.HilbAff.Basic A B e σ (F.map g.op (x σ)) := by
    intro σ Z g
    have htop : Set.range (𝟙 (X σ)) ⊆ (W σ (X σ) (x σ) : Set (X σ)) :=
      (hW σ _ _ _ (𝟙 _)).2 (by rw [op_id, F.map_id]; exact hbas σ)
    exact (hW σ _ _ _ g).1 (fun z _ => htop ⟨z, rfl⟩)
  have hrep : F.IsRepresentable := by
    refine GlobalTheory.GeneratorFunctor.isRepresentable_of_charts F (GlobalTheory.T.affineHilbertSchemeFunctor_isSheaf_zariski A B r) X x W ?_ ?_ ?_
    · intro σ Z y Z' a
      rw [hW]
      constructor
      · intro hb
        obtain ⟨g, hg, -⟩ := huniv σ Z' _ hb
        exact ⟨g, hg⟩
      · rintro ⟨g, hg⟩
        rw [← hg]
        exact stab σ Z' g
    · intro σ Z g g' h
      obtain ⟨g₀, -, hu⟩ := huniv σ Z _ (stab σ Z g)
      exact (hu g rfl).trans (hu g' h.symm).symm
    · intro Z y z
      obtain ⟨σ, U, hz, hb⟩ := GlobalTheory.T.exists_affineHilbertChartBasic_neighbourhood A B N r e Z y z
      refine ⟨σ, (hW σ Z y U U.ι).2 hb ?_⟩
      simpa using hz
  let R := F.representableBy
  obtain ⟨U, u, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.affineHilbert_representing_universal_subscheme A B r F.reprX R
  obtain ⟨q1, q2, q3⟩ := GlobalTheory.T.affineHilbertScheme_representing_qc_qs_finiteType A B r F.reprX R
  refine ⟨F.reprX, (R.homEquiv (𝟙 _)).1, U, u, ?_, h1, h2, h3, h4, h5⟩
  rw [IsProper.eq_valuativeCriterion, ValuativeCriterion.eq]
  exact ⟨⟨⟨⟨GlobalTheory.T.affineHilbertScheme_valuativeCriterion_existence A B r F.reprX R, GlobalTheory.T.affineHilbert_valuativeCriterion_uniqueness A B r F.reprX R⟩, q1⟩, q2⟩, q3⟩

end GlobalTheory.HilbAff
end
end

