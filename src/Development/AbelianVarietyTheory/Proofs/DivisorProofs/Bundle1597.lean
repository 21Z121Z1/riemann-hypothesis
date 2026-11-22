import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumFockEquations
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0257

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousCosSqAngleFunction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

open GlobalTheory.Twist (resM resM_resM)

namespace GlobalTheory.CurveDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
  {V L L' : X.Modules} {r : ℕ} (h : Met p σ V r)

theorem exists_smul_frame (c : Chart L 1) {W T : X.Opens} (hW : W ≤ c.U) (hT : T ≤ W)
    (s : Γ(L, T)) : ∃ f : Γ(X, T), s = f • resM L hT (resM L hW (c.e 0)) := by
  refine ⟨(c.isFrame.basis (hT.trans hW)).repr s 0, ?_⟩
  conv_lhs => rw [← (c.isFrame.basis (hT.trans hW)).sum_repr s]
  rw [Fin.sum_univ_one, IsFrame.basis_apply, resM_resM]

theorem form_smul_smul {T : X.Opens} (f g : Γ(X, T)) (a b : Γ(V, T)) (y : CxPts p σ) :
    h.form (f • a) (g • b) y =
      ev p σ T f y * starRingEnd ℂ (ev p σ T g y) * h.form a b y := by
  rw [h.form_smul_left, ← h.conj_form (g • b), h.form_smul_left, map_mul, h.conj_form, mul_assoc]

theorem normSq_form_le {T : X.Opens} (a b : Γ(V, T)) (y : CxPts p σ) :
    ‖h.form a b y‖ ^ 2 ≤ (h.form a a y).re * (h.form b b y).re := by
  have hp := (h.posDef _ y (h.isVB.mem_pick y)).posSemidef
  have e := norm_form_le hp ((h.isVB.pick y).crd p σ a y) ((h.isVB.pick y).crd p σ b y)
  have e₁ := gnorm_sq hp ((h.isVB.pick y).crd p σ a y)
  have e₂ := gnorm_sq hp ((h.isVB.pick y).crd p σ b y)
  calc ‖h.form a b y‖ ^ 2 ≤ _ := pow_le_pow_left₀ (norm_nonneg _) e 2
    _ = _ := by rw [mul_pow, e₁, e₂]; rfl

def frameImg (l : L ⟶ V) (c : Chart L 1) {W : X.Opens} (hW : W ≤ c.U) : Γ(V, W) :=
  l.app W (resM L hW (c.e 0))

theorem frameImg_pos {l : L ⟶ V} (hl : IsSubbundle l) (hL : IsVB L 1) (c : Chart L 1)
    {W : X.Opens} (hW : W ≤ c.U) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W)
    (hc : y ∈ ptsIn p σ c.U) : 0 < (h.form (frameImg l c hW) (frameImg l c hW) y).re := by
  rw [frameImg, ← h.form_restrict hl hL _ _ hy, Met.form_resM _ _ _ _ hy,
    Met.form_frame _ _ hc]
  exact (Complex.pos_iff.1 ((h.restrict hl hL).posDef c y hc).diag_pos).1

def cosRatio (l : L ⟶ V) (l' : L' ⟶ V) (c : Chart L 1) (c' : Chart L' 1) (y : CxPts p σ) : ℝ :=
  ‖h.form (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U))
    (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)) y‖ ^ 2 /
  ((h.form (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U))
      (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)) y).re *
    (h.form (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U))
      (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U)) y).re)

theorem resM_app_eq_smul (l : L ⟶ V) (c : Chart L 1) {U W T : X.Opens} (hW : W ≤ c.U)
    (hT : T ≤ W) (hU : T ≤ U) (s : Γ(L, U)) :
    ∃ f : Γ(X, T), resM V hU (l.app U s) = f • resM V hT (frameImg l c hW) := by
  obtain ⟨f, hf⟩ := exists_smul_frame c hW hT (resM L hU s)
  refine ⟨f, ?_⟩
  rw [← GlobalTheory.Twist.app_resM, hf, Scheme.Modules.Hom.app_smul, GlobalTheory.Twist.app_resM]
  rfl

theorem cosRatio_spec {l : L ⟶ V} {l' : L' ⟶ V} (hl : IsSubbundle l) (hl' : IsSubbundle l')
    (hL : IsVB L 1) (hL' : IsVB L' 1) (c : Chart L 1) (c' : Chart L' 1) {U : X.Opens}
    (s : Γ(L, U)) (s' : Γ(L', U)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U)
    (hc : y ∈ ptsIn p σ c.U) (hc' : y ∈ ptsIn p σ c'.U) :
    ‖h.form (l'.app U s') (l.app U s) y‖ ^ 2 = cosRatio h l l' c c' y *
      (h.form (l.app U s) (l.app U s) y).re * (h.form (l'.app U s') (l'.app U s') y).re := by
  have hyW : y ∈ ptsIn p σ (c.U ⊓ c'.U) := mem_ptsIn_inf.2 ⟨hc, hc'⟩
  have hyT : y ∈ ptsIn p σ (U ⊓ (c.U ⊓ c'.U)) := mem_ptsIn_inf.2 ⟨hy, hyW⟩
  obtain ⟨f, hf⟩ := resM_app_eq_smul l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)
    (inf_le_right : U ⊓ (c.U ⊓ c'.U) ≤ _) inf_le_left s
  obtain ⟨g, hg⟩ := resM_app_eq_smul l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U)
    (inf_le_right : U ⊓ (c.U ⊓ c'.U) ≤ _) inf_le_left s'
  have pos := frameImg_pos h hl hL c (inf_le_left : c.U ⊓ c'.U ≤ c.U) hyW hc
  have pos' := frameImg_pos h hl' hL' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U) hyW hc'
  rw [cosRatio]
  set u := frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)
  set u' := frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U)
  have e₁ : h.form (l'.app U s') (l.app U s) y =
      ev p σ _ g y * starRingEnd ℂ (ev p σ _ f y) * h.form u' u y := by
    rw [← h.form_resM _ _ (inf_le_left : U ⊓ (c.U ⊓ c'.U) ≤ U) hyT, hf, hg, form_smul_smul,
      h.form_resM _ _ _ hyT]
  have e₂ : h.form (l.app U s) (l.app U s) y =
      ev p σ _ f y * starRingEnd ℂ (ev p σ _ f y) * h.form u u y := by
    rw [← h.form_resM _ _ (inf_le_left : U ⊓ (c.U ⊓ c'.U) ≤ U) hyT, hf, form_smul_smul,
      h.form_resM _ _ _ hyT]
  have e₃ : h.form (l'.app U s') (l'.app U s') y =
      ev p σ _ g y * starRingEnd ℂ (ev p σ _ g y) * h.form u' u' y := by
    rw [← h.form_resM _ _ (inf_le_left : U ⊓ (c.U ⊓ c'.U) ≤ U) hyT, hg, form_smul_smul,
      h.form_resM _ _ _ hyT]
  rw [e₁, e₂, e₃, Complex.mul_conj, Complex.mul_conj, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq]
  field_simp

theorem exists_isCosSq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (V L L' : X.Modules) (r : ℕ) (h : Met p σ V r) (l : L ⟶ V) (l' : L' ⟶ V), h.IsCInf →
    IsSubbundle l → IsSubbundle l' → IsVB L 1 → IsVB L' 1 →
    ∃ v : CxPts p σ → ℝ, IsCosSq h l l' v ∧ Continuous v ∧ ∀ y, 0 ≤ v y ∧ v y ≤ 1 := by
  intro k _ X p σ V L L' r h l l' H hl hl' hL hL'
  have hv : IsCosSq h l l' fun y => cosRatio h l l' (hL.pick y) (hL'.pick y) y :=
    fun U t t' y hy => cosRatio_spec h hl hl' hL hL' _ _ t t' hy (hL.mem_pick y) (hL'.mem_pick y)
  refine ⟨_, hv, continuous_iff_continuousAt.2 fun y₀ => ?_, fun y => ?_⟩
  · have hc := hL.mem_pick y₀
    have hc' := hL'.mem_pick y₀
    generalize hL.pick y₀ = c at hc
    generalize hL'.pick y₀ = c' at hc'
    have hyW : y₀ ∈ ptsIn p σ (c.U ⊓ c'.U) := mem_ptsIn_inf.2 ⟨hc, hc'⟩
    have G := H.gram (![frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U),
      frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U)]) hyW
    have c₀₀ : ContinuousAt (fun z => h.form (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U))
      (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)) z) y₀ := (G 0 0).continuousAt
    have c₁₀ : ContinuousAt (fun z => h.form (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U))
      (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)) z) y₀ := (G 1 0).continuousAt
    have c₁₁ : ContinuousAt (fun z => h.form (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U))
      (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U)) z) y₀ := (G 1 1).continuousAt
    have pos := frameImg_pos h hl hL c (inf_le_left : c.U ⊓ c'.U ≤ c.U) hyW hc
    have pos' := frameImg_pos h hl' hL' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U) hyW hc'
    have R := (c₁₀.norm.pow 2).div
      ((Complex.continuous_re.continuousAt.comp c₀₀).mul
        (Complex.continuous_re.continuousAt.comp c₁₁)) (mul_pos pos pos').ne'
    refine R.congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hyW] with z hz
    have e := hv (c.U ⊓ c'.U) (resM L inf_le_left (c.e 0)) (resM L' inf_le_right (c'.e 0)) z hz
    have p₁ := frameImg_pos h hl hL c (inf_le_left : c.U ⊓ c'.U ≤ c.U) hz (mem_ptsIn_inf.1 hz).1
    have p₂ := frameImg_pos h hl' hL' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U) hz (mem_ptsIn_inf.1 hz).2
    change ‖h.form (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U))
      (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)) z‖ ^ 2 =
      cosRatio h l l' (hL.pick z) (hL'.pick z) z *
      (h.form (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U))
        (frameImg l c (inf_le_left : c.U ⊓ c'.U ≤ c.U)) z).re *
      (h.form (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U))
        (frameImg l' c' (inf_le_right : c.U ⊓ c'.U ≤ c'.U)) z).re at e
    simp only [Pi.div_apply, Function.comp_apply, Pi.mul_apply, Pi.pow_apply]
    rw [e]
    field_simp
  · have hc := hL.mem_pick y
    have hc' := hL'.mem_pick y
    have hyW := mem_ptsIn_inf.2 ⟨hc, hc'⟩
    have pos := frameImg_pos h hl hL (hL.pick y) inf_le_left hyW hc
    have pos' := frameImg_pos h hl' hL' (hL'.pick y) inf_le_right hyW hc'
    refine ⟨div_nonneg (sq_nonneg _) (mul_pos pos pos').le, (div_le_one (mul_pos pos pos')).2 ?_⟩
    have := normSq_form_le h (frameImg l (hL.pick y) inf_le_left)
      (frameImg l' (hL'.pick y) inf_le_right) y
    rwa [← h.conj_form, Complex.norm_conj] at this

end GlobalTheory.CurveDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePartZeroNeOfIsVacuumOrientedModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.VacNonzeroReal

variable {D : D7}

theorem continuous_finTmul (e : D.host.E) :
    Continuous fun x : Af D.host.F => (pairA D.host.F 0 x ⊗ₜ[D.host.F] e : AE D) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  have h1 : Continuous fun x : Af D.host.F => pairA D.host.F 0 x :=
    continuous_const.prodMk continuous_id
  have h2 : Continuous fun x : Af D.host.F => pairA D.host.F 0 x • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) :=
    h1.smul (continuous_const : Continuous fun _ : Af D.host.F => ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D))
  refine h2.congr fun x => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem infPart_finTmul (x : Af D.host.F) (e : D.host.E) :
    infPart D (pairA D.host.F 0 x ⊗ₜ[D.host.F] e) = 0 := by
  show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F 0 x ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
  rw [TensorProduct.zero_tmul]

theorem finPart_infTmul (x : Ainf D.host.F) (e : D.host.E) :
    finPart D (pairA D.host.F x 0 ⊗ₜ[D.host.F] e) = 0 := by
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F x 0 ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show (0 : Af D.host.F) ⊗ₜ[D.host.F] _ = 0
  rw [TensorProduct.zero_tmul]

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 1600000 in

theorem decomp_AE (V : AddSubgroup (AE D)) (hV : IsOpen (V : Set (AE D))) (z : AE D) :
    ∃ e : D.host.E, ∃ u ∈ V, infPart D u = 0 ∧ ∃ r : AE D, finPart D r = 0 ∧ z = incA D e + u + r := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, V.zero_mem, map_zero _, 0, map_zero _, by rw [map_zero, add_zero, add_zero]⟩
  | tmul a e =>
    set W : Set (Af D.host.F) := (fun x => (pairA D.host.F 0 x ⊗ₜ[D.host.F] e : AE D)) ⁻¹' V with hW
    have hWo : IsOpen W := hV.preimage (continuous_finTmul e)
    have hO : IsOpen {x : Af D.host.F | a.2 - x ∈ W} := hWo.preimage (continuous_const.sub continuous_id)
    obtain ⟨c, hc⟩ := Formalism.L2.SG.Pf.CondStd.dense_F.exists_mem_open hO
      ⟨a.2, by
        show (pairA D.host.F 0 (a.2 - a.2) ⊗ₜ[D.host.F] e : AE D) ∈ V
        rw [sub_self]
        have : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
        rw [this, TensorProduct.zero_tmul]
        exact V.zero_mem⟩
    refine ⟨algebraMap D.host.F D.host.E c * e, _, hc, infPart_finTmul _ _, _, finPart_infTmul (a.1 - algebraMap D.host.F (Ainf D.host.F) c) e, ?_⟩
    have hinc : incA D (algebraMap D.host.F D.host.E c * e) =
        algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] e := by
      show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c * e) = _
      have h1 : (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c * e) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] algebraMap D.host.F D.host.E c) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have h2 : algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] e =
          (algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [h1, h2, ← Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply']
    rw [hinc, ← TensorProduct.add_tmul, ← TensorProduct.add_tmul]
    congr 1
    refine Prod.ext ?_ ?_
    · show a.1 = algebraMap D.host.F (Ainf D.host.F) c + 0 + (a.1 - algebraMap D.host.F (Ainf D.host.F) c)
      abel
    · show a.2 = algebraMap D.host.F (Af D.host.F) c + (a.2 - algebraMap D.host.F (Af D.host.F) c) + 0
      abel
  | add x y hx hy =>
    obtain ⟨e, u, hu, hu0, r, hr0, hx⟩ := hx
    obtain ⟨e', u', hu', hu0', r', hr0', hy⟩ := hy
    refine ⟨e + e', u + u', V.add_mem hu hu', by rw [map_add, hu0, hu0', add_zero], r + r',
      by rw [map_add, hr0, hr0', add_zero], ?_⟩
    rw [hx, hy, map_add, add_add_add_comm _ r, add_add_add_comm (incA D e) u]

theorem continuous_single {m n : ℕ} (i : Fin m) (j : Fin n) :
    Continuous fun v : AE D => (Matrix.single i j v : Matrix (Fin m) (Fin n) (AE D)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Matrix.single_apply, and_self, if_true]
    exact continuous_id
  · have : ∀ v : AE D, (Matrix.single i j v : Matrix (Fin m) (Fin n) (AE D)) a b = 0 := fun v => by
      rw [Matrix.single_apply, if_neg h]
    simpa only [this] using continuous_const

def singleHom {m n : ℕ} (i : Fin m) (j : Fin n) : AE D →+ Matrix (Fin m) (Fin n) (AE D) where
  toFun v := Matrix.single i j v
  map_zero' := Matrix.single_zero i j
  map_add' x y := Matrix.single_add i j x y

theorem decomp_WO {S T : HSp D} (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) (w : WO S T) :
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ u ∈ U, u.map (infPart D) = 0 ∧
      ∃ r : WO S T, r.map (finPart D) = 0 ∧ w = ratW T S γ + u + r := by
  classical
  have hV : ∀ i j, IsOpen ((U.comap (singleHom i j) : AddSubgroup (AE D)) : Set (AE D)) := fun i j =>
    hU.preimage (continuous_single i j)
  choose e u hu hu0 r hr0 hw using fun i j => decomp_AE _ (hV i j) (w i j)
  refine ⟨Matrix.of e, Matrix.of u, ?_, ?_, Matrix.of r, ?_, ?_⟩
  · rw [Matrix.matrix_eq_sum_single (Matrix.of u)]
    exact U.sum_mem fun i _ => U.sum_mem fun j _ => hu i j
  · ext i j
    simp [hu0 i j]
  · ext i j
    simp [hr0 i j]
  · ext i j
    rw [hw i j]
    rfl

theorem exists_finPart_zero_ne : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO S T → ℂ), IsVacO ψ θ S T sS sT LS LT f → ∃ w : WO S T, w.map (finPart D) = 0 ∧ f w ≠ 0 := by
  intro D ψ θ S T sS sT LS LT f hv
  have hne := GlobalTheory.TwistFactorProof.vac_ne_zero hv
  have hth : IsThetaFunO ψ S T f := hv.2.theta
  obtain ⟨w0, hw0⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨U, hUo, hU⟩ := hth.level
  obtain ⟨γ, u, huU, hu0, r, hr0, rfl⟩ := decomp_WO U hUo w0
  refine ⟨r, hr0, fun hfr => ?_⟩
  have hψ : ∀ a, ψ a ≠ 0 := fun a => by
    have : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    exact left_ne_zero_of_mul_eq_one this
  rw [add_assoc, hth.quasi γ (u + r)] at hw0
  have hfur : f (u + r) ≠ 0 := right_ne_zero_of_mul hw0
  have h2 := congrFun (hU u huU hu0) r
  unfold heisO at h2
  rw [hfr, add_comm r u] at h2
  exact (mul_ne_zero (hψ _) hfur) h2

end GlobalTheory.VacNonzeroReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSmoothPartitionUnityHolAtlas
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem contDiffOn_real_transition (i j : A.ι) :
    ContDiffOn ℝ ∞ (A.e j ∘ (A.e i).symm) ((A.e i).target ∩ (A.e i).symm ⁻¹' (A.e j).source) :=
  (contDiffOn_piLp 2).2 fun a => GlobalTheory.ChartGlue.contDiffOn_real
    ((A.e i).isOpen_inter_preimage_symm (A.e j).open_source) (differentiableOn_euclidean.1 (A.holo i j) a)

theorem exists_smooth_bump [T2Space M] (x : M) :
    ∃ (i : A.ι) (ψ : M → ℝ), A.SmoothOn univ (fun y => (ψ y : ℂ)) ∧ tsupport ψ ⊆ (A.e i).source ∧
      ∀ᶠ y in 𝓝 x, ψ y = 1 := by
  classical
  obtain ⟨i, hxe⟩ := A.cover x
  set e := A.e i with he
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hxe)
  let β : ContDiffBump (e x) := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hcb : Metric.closedBall (e x) (ε / 2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  set C := e.symm '' Metric.closedBall (e x) (ε / 2) with hC
  have hCc : IsCompact C := (isCompact_closedBall (e x) (ε / 2)).image_of_continuousOn
    (e.continuousOn_symm.mono fun y hy => hcb hy)
  have hCsub : C ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (hcb hy)
  let ψ : M → ℝ := fun w => if w ∈ e.source then β (e w) else 0
  have hsupp : Function.support ψ ⊆ C := by
    intro w hw
    simp only [Function.mem_support, ψ] at hw
    split_ifs at hw with hws
    · have : e w ∈ Metric.ball (e x) (ε / 2) := by
        rw [← β.support_eq]; exact hw
      exact ⟨e w, Metric.ball_subset_closedBall this, e.left_inv hws⟩
    · exact absurd rfl hw
  have hts : tsupport ψ ⊆ C := closure_minimal hsupp hCc.isClosed
  refine ⟨i, ψ, ?_, hts.trans hCsub, ?_⟩
  · intro k
    rw [preimage_univ, inter_univ]
    apply contDiffOn_of_locally_contDiffOn
    intro y hy
    by_cases hys : (A.e k).symm y ∈ e.source
    · refine ⟨(A.e k).target ∩ (A.e k).symm ⁻¹' e.source,
        (A.e k).isOpen_inter_preimage_symm e.open_source, ⟨hy, hys⟩, ?_⟩
      have hβ : ContDiff ℝ ∞ (fun y : V n => ((β y : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp β.contDiff
      refine ((hβ.comp_contDiffOn (A.contDiffOn_real_transition k i)).mono inter_subset_right).congr
        fun v hv => ?_
      have hv1 : (A.e k).symm v ∈ e.source := hv.2.2
      simp only [Function.comp, ψ, if_pos hv1]
      rfl
    · refine ⟨(A.e k).target ∩ (A.e k).symm ⁻¹' Cᶜ,
        (A.e k).isOpen_inter_preimage_symm hCc.isClosed.isOpen_compl,
        ⟨hy, fun h => hys (hCsub h)⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℂ))).congr fun v hv => ?_
      have : ψ ((A.e k).symm v) = 0 := by
        by_contra h
        exact hv.2.2 (hsupp h)
      simp [Function.comp, this]
  · have ho : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e x) (ε / 4)) :=
      e.isOpen_inter_preimage Metric.isOpen_ball
    filter_upwards [ho.mem_nhds ⟨hxe, Metric.mem_ball_self (by linarith)⟩] with w hw
    simp only [ψ, if_pos hw.1]
    exact β.one_of_mem_closedBall (Metric.ball_subset_closedBall hw.2)

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory

theorem exists_finite_smooth_partition_holAtlas {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] {n : ℕ}
    (A : GlobalTheory.CxForm.HolAtlas M n) :
    ∃ (N : ℕ) (c : Fin N → A.ι) (χ : Fin N → M → ℝ), (∀ j, A.SmoothOn univ fun y => (χ j y : ℂ)) ∧
      (∀ j, tsupport (χ j) ⊆ (A.e (c j)).source) ∧ ∀ y, ∑ j, χ j y = 1 := by
  classical
  choose E Ψ hΨs hΨt hΨ1 using A.exists_smooth_bump
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M => interior {y | Ψ x y = 1})
    (fun _ => isOpen_interior) (fun y _ => mem_iUnion.2 ⟨y, mem_interior_iff_mem_nhds.2 (hΨ1 y)⟩)
  let p : Fin t.card → M := fun i => (t.equivFin.symm i : M)
  let ψ : Fin t.card → M → ℝ := fun i => Ψ (p i)
  have hsum : ∀ x, ∑ i, ψ i x * ∏ j ∈ Finset.univ with j < i, (1 - ψ j x) =
      1 - ∏ i, (1 - ψ i x) := fun x => by
    rw [Finset.prod_one_sub_ordered]; ring
  refine ⟨t.card, fun i => E (p i), fun i x => ψ i x * ∏ j ∈ Finset.univ with j < i, (1 - ψ j x),
    fun i k => ?_, fun i => (tsupport_mul_subset_left).trans (hΨt (p i)), fun x => ?_⟩
  · refine ((hΨs (p i) k).mul (contDiffOn_prod (t := Finset.univ.filter (· < i))
      fun j _ => (contDiffOn_const (c := (1 : ℂ))).sub (hΨs (p j) k))).congr fun v _ => ?_
    simp [Function.comp, ψ]
  · rw [hsum]
    obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.1 (ht (mem_univ x))
    have h1 : ψ (t.equivFin ⟨u, hu⟩) x = 1 := by
      have : p (t.equivFin ⟨u, hu⟩) = u := by simp [p]
      simp only [ψ, this]
      exact (interior_subset hxu : x ∈ {y | Ψ u y = 1})
    rw [Finset.prod_eq_zero (Finset.mem_univ (t.equivFin ⟨u, hu⟩)) (by rw [h1]; ring)]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFixedFieldPointOfFixedBySubgroup
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.AbVarRed

theorem exists_fixedField_point (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (H : Subgroup (Ω ≃ₐ[K] Ω))
    (A : Over (Sp K)) (_ : LocallyOfFiniteType A.hom) (x : ptOver K Ω ⟶ A)
    (hx : ∀ σ ∈ H, specAut σ ≫ x = x) :
    ∃ y : Sp (IntermediateField.fixedField H) ⟶ A.left,
      spMap (algebraMap (IntermediateField.fixedField H) Ω) ≫ y = x.left := by
  obtain ⟨E, hE1, hE2, -⟩ := GlobalTheory.SS.exists_fieldOfValues A.left Ω x.left
  have hid : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by
    rw [← Spec.map_id]
    congr 1
  have hfix : ∀ c ∈ E, ∀ σ ∈ H, σ c = c := by
    intro c hc σ hσ
    have h1 : spMap (σ : Ω →+* Ω) ≫ x.left = spMap (RingHom.id Ω) ≫ x.left := by
      rw [hid, Category.id_comp]
      exact congrArg CommaMorphism.left (hx σ hσ)
    exact (hE1 _ _).1 h1 c hc
  refine (hE2 (IntermediateField.fixedField H) (algebraMap (IntermediateField.fixedField H) Ω)).1 ?_
  intro c hc
  exact ⟨⟨c, fun σ => hfix c hc σ σ.2⟩, rfl⟩

end GlobalTheory.Published.AbVarRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussVacuumNondegenerateGaussianDualPair
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section
namespace GlobalTheory.GaussVacPair
open GlobalTheory.GaussFockJ GlobalTheory.ThK.EvAt0.PolD

theorem actsD_unique {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ f₂ : SInf F κ}
    (h1 : ActsD (evI F) T f f₁) (h2 : ActsD (evI F) T f f₂) : f₁ = f₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) κ
  ext y
  have hr := hR f
  let x : κ → AF F := fun i => liftA (y i)
  have hx : At (evI F) x := fun c hc => funext fun i => smul_liftA hc (y i)
  have e := (h1 R hr x).unique (h2 R hr x)
  have hRx : R x = R 0 := by
    have := hr.1 0 x hx
    rwa [zero_add] at this
  have hl : (fun i => evI F (x i)) = y := funext fun i => evI_liftA (y i)
  simp only [tens, hl, hRx] at e
  exact mul_right_cancel₀ hR0 e

theorem exists_gauss_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∃ g : SInf F (Fin n × Fin d), M.IsGauss B.ψ B.emb g ∧
      ∃ (Q : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ) (c : ℝ),
        0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ ∀ x, g x = Complex.exp (-(Q x x)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨J₀, hJJ, hJω, hJpos, hJrel⟩ := GlobalTheory.T.exists_positive_complex_structure_darboux_pair F E σ B n d X W M χX χW om r s r' s' hP
  have hsym : ∀ x y : (Fin n × Fin d → mixedEmbedding.mixedSpace F), GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x y = GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) y x := by
    intro x y
    simp only [GlobalTheory.GaussLine.pairInf_apply, mul_comm]
  obtain ⟨Q, c, hc, hQc, hQs, hQJ⟩ := GlobalTheory.T.exists_siegel_fock_form_of_complex_structure (Fin n × Fin d → mixedEmbedding.mixedSpace F) (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) J₀ hsym hJJ hJω hJpos
  obtain ⟨g, hg, hgd⟩ := GlobalTheory.T.exists_schwartz_eq_cexp_neg_form (Fin n × Fin d → mixedEmbedding.mixedSpace F) Q c hc hQc
  refine ⟨g, ⟨fun _ => 1, ?_⟩, Q, c, hc, hQc, hg⟩
  intro u u' hu hu' hrel f f' hf hf'
  have hrel' : ∀ w, u'.map (piInf (B.emb w)) = Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ) := by
    intro w
    rw [hrel w]
    simp
  have key : ∀ v : Matrix (Fin n) (Fin d) (AE F E), At (evI F) v → ∀ h : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ v) g h → ∀ x, h x = GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (Psi M v) g x := by
    intro v hv h hh x
    have h0 := actsD_Phi hψ M (Psi M v) g
    rw [Phi_Psi M hv] at h0
    rw [actsD_unique hh h0, dHeis_eq_dOp]
  have hJ : Psi M u' = J₀ (Psi M u) := hJrel u u' hu hu' hrel'
  have hd : ∀ (w : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) x, GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) w g x =
      -2 * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x w.2 : ℂ)) * g x := by
    intro w x
    rw [GlobalTheory.GaussLine.dHeis, hgd x w.1, hQs w.1 x]
    ring
  ext x
  rw [SchwartzMap.smul_apply, key u' hu' f' hf' x, key u hu f hf x, hJ, hd, hd, hQJ, smul_eq_mul]
  ring

end GlobalTheory.GaussVacPair
end
end

