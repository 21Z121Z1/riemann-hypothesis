import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2572
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2851

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineHeight
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineNull

open GlobalTheory.CurveDens

theorem isCosSq_unique {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {V L L' : X.Modules} {r : ℕ}
    (h : Met p σ V r) {l : L ⟶ V} {l' : L' ⟶ V} (hL : IsVB L 1) (hL' : IsVB L' 1) (hl : IsSubbundle l)
    (hl' : IsSubbundle l') {v v' : CxPts p σ → ℝ} (hv : IsCosSq h l l' v) (hv' : IsCosSq h l l' v') : v = v' := by
  funext y
  obtain ⟨U, t, t', ht, ht', hU⟩ := AdjFlag.exists_frames hL hL' y
  have a := AdjFlag.form_frame_pos (h.restrict hl hL) ht hU
  have b := AdjFlag.form_frame_pos (h.restrict hl' hL') ht' hU
  rw [h.form_restrict hl hL t t hU] at a
  rw [h.form_restrict hl' hL' t' t' hU] at b
  have e := (hv U t t' y hU).symm.trans (hv' U t t' y hU)
  exact mul_right_cancel₀ a.ne' (mul_right_cancel₀ b.ne' e)

theorem part_cosSq_one : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ, (hY.atlas σ).part α ε {y | v y = 1} = 0 := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv α _ ε
  obtain ⟨r, hr, -, h₂⟩ := exists_ratSec_fam5 k B Y q p d hB.toIsArithVar hY.toIsArithVar hB.regular π w E h H flB fl hfl A
  obtain ⟨v', hv', hlt⟩ := h₂ σ
  obtain rfl : v = v' := isCosSq_unique _ (fl.isVB 1) ((flB.pull π).isVB 1) (fl.isSubbundle 1)
    ((flB.pull π).isSubbundle 1) hv hv'
  generalize ((fam5 π w H flB fl A 0).dual.tens (fam5 π w H flB fl A 4)).div hr = D at hlt
  have hset : {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (D.supp : Set Y)} = (offSupp p σ D)ᶜ := by
    ext y
    rw [Set.mem_compl_iff, offSupp, mem_ptsIn]
    exact not_not.symm
  have hA : MeasurableSet {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (D.supp : Set Y)} := by
    rw [hset]
    exact (isOpen_ptsIn _).measurableSet.compl
  refine measure_mono_null (t := {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (D.supp : Set Y)})
    (fun y hy => ?_) ?_
  · rw [hset]
    exact fun hm => (hlt y hm).1.ne hy
  · exact GlueCoverNull.glueMeas_null _ _ hA fun c =>
      ChernNull.chart_null hY.toIsArithVar D.supp.isClosed (CartierDiv.genericPoint_notMem_supp D) σ c

end GlobalTheory.LineNull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLinePullbackForm
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CosSqMeas

open TopologicalSpace Filter Topology
open scoped ComplexOrder

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem exists_sec_form_pos {E F : X.Modules} {n : ℕ} (h : Met p σ E n) (ι : F ⟶ E)
    (hF : IsVB F 1) (hι : IsSubbundle ι) (y : CxPts p σ) :
    ∃ (U : X.Opens) (t : Γ(F, U)), y ∈ ptsIn p σ U ∧
      0 < (h.form (ι.app U t) (ι.app U t) y).re := by
  obtain ⟨hm, s, hs⟩ := hι
  let S : ShortComplex X.Modules := ShortComplex.mk ι (Limits.cokernel.π ι) (Limits.cokernel.condition ι)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel ι, mono_f := hm }
  have : Nonempty X := ⟨y.1 (IsLocalRing.closedPoint ℂ)⟩
  obtain ⟨h₂, -⟩ := VBExt.isVB_and_cls_det_of_shortExact X S 1 s hS hF hs
  obtain rfl : n = 1 + s := h.isVB.rank_unique h₂
  obtain ⟨a, hy⟩ := Met.exists_adapted (p := p) hS hF hs y
  have hpos := (h.posDef_gram_frame (S := S) hS a hy).diag_pos (i := Sum.inl 0)
  refine ⟨a.U, a.e 0, hy, (Complex.pos_iff.1 hpos).1⟩

theorem continuousAt_form {E : X.Modules} {n : ℕ} {h : Met p σ E n} (H : h.IsCInf) {U : X.Opens}
    (s t : Γ(E, U)) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    ContinuousAt (fun z => h.form s t z) y :=
  (H.gram ![s, t] hy 0 1).continuousAt

end GlobalTheory.CosSqMeas

namespace GlobalTheory.CosSqMeas

open TopologicalSpace Filter Topology
open scoped ComplexOrder

theorem measurable_cosSq : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    Measurable v := by
  intro k _ B Y _ _ q p d _ _ π w E h H flB fl _ _ σ v hv
  have Hm : ((h.pull π w).met σ).IsCInf := H.pull π w σ
  refine Continuous.measurable (continuous_iff_continuousAt.2 fun y => ?_)
  obtain ⟨U₁, t₁, hy₁, hp₁⟩ := exists_sec_form_pos ((h.pull π w).met σ) (fl.ι 1) (fl.isVB 1)
    (fl.isSubbundle 1) y
  obtain ⟨U₂, t₂, hy₂, hp₂⟩ := exists_sec_form_pos ((h.pull π w).met σ)
    ((Scheme.Modules.pullback π).map (flB.ι 1)) ((flB.isVB 1).pullback π)
    (SubPull.isSubbundle_pullback B Y π _ E (flB.ι 1) 1 (flB.isVB 1) (flB.isSubbundle 1)) y
  have hy : y ∈ ptsIn p σ (U₁ ⊓ U₂) := mem_ptsIn_inf.2 ⟨hy₁, hy₂⟩
  set m := (h.pull π w).met σ
  set l := fl.ι 1
  set l' := (Scheme.Modules.pullback π).map (flB.ι 1)
  set u₁ := Twist.resM _ (inf_le_left : U₁ ⊓ U₂ ≤ U₁) t₁
  set u₂ := Twist.resM _ (inf_le_right : U₁ ⊓ U₂ ≤ U₂) t₂
  have e₁ : m.form (l.app _ u₁) (l.app _ u₁) y = m.form (l.app U₁ t₁) (l.app U₁ t₁) y := by
    rw [Twist.app_resM, m.form_resM _ _ _ hy]
  have e₂ : m.form (l'.app _ u₂) (l'.app _ u₂) y = m.form (l'.app U₂ t₂) (l'.app U₂ t₂) y := by
    rw [Twist.app_resM, m.form_resM _ _ _ hy]
  have c₁ := Complex.continuous_re.continuousAt.comp (continuousAt_form Hm (l.app _ u₁) (l.app _ u₁) hy)
  have c₂ := Complex.continuous_re.continuousAt.comp (continuousAt_form Hm (l'.app _ u₂) (l'.app _ u₂) hy)
  have c₃ := (continuousAt_form Hm (l'.app _ u₂) (l.app _ u₁) hy).norm.pow 2
  have hp₁' : 0 < (m.form (l.app _ u₁) (l.app _ u₁) y).re := by rw [e₁]; exact hp₁
  have hp₂' : 0 < (m.form (l'.app _ u₂) (l'.app _ u₂) y).re := by rw [e₂]; exact hp₂
  refine (c₃.div (c₁.mul c₂) (mul_pos hp₁' hp₂').ne').congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds hy, c₁.eventually (lt_mem_nhds hp₁'),
    c₂.eventually (lt_mem_nhds hp₂')] with z hz h₁ h₂
  have := hv _ u₁ u₂ z hz
  simp only [Function.comp_apply] at h₁ h₂
  simp only [Pi.div_apply, Pi.mul_apply, Pi.pow_apply, Function.comp_apply]
  rw [this, mul_assoc, mul_div_cancel_right₀ _ (mul_pos h₁ h₂).ne']

end GlobalTheory.CosSqMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagLocallyAdaptedAffineFrameStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_locally_adapted_affine_frame : ∀ {ι : Type} [Fintype ι] {N : ℕ} {T : Scheme.{0}} (g : T ⟶ Sp ℤ)
    (fl' : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback g).obj (Taut.stdE N)) N) (t : T),
    ∃ V : T.Opens, t ∈ V ∧ IsAffineOpen V ∧ ∃ G : ι → GL (Fin N) Γ(T, V), Loc.Adapted g fl' V G := by
  first | exact @GlobalTheory.FlagZ.Loc.exists_adapted | exact GlobalTheory.FlagZ.Loc.exists_adapted | (intros; apply GlobalTheory.FlagZ.Loc.exists_adapted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormReal
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm.OmReal

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder ComplexConjugate

section Point

variable {n : ℕ}

theorem coordVec_expand (w : V n) : w = ∑ a, w a • coordVec a := by
  ext i
  simp [coordVec, EuclideanSpace.single_apply, Pi.single_apply]

theorem sesq_sum_left {α : V n → V n → ℂ} (hα : IsSesq α) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (x : ι → V n) (y : V n) : α (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, c i * α (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hα.smul_left 0 0 y
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_left, hα.smul_left, ih, smul_eq_mul]

theorem sesq_sum_right {α : V n → V n → ℂ} (hα : IsSesq α) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (x : V n) (y : ι → V n) : α x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, conj (c i) * α x (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hα.smul_right 0 x 0
    simpa using this
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hα.add_right, hα.smul_right, ih, smul_eq_mul]

theorem sesq_expand {α : V n → V n → ℂ} (hα : IsSesq α) (x y : V n) :
    α x y = ∑ a, ∑ b, α (coordVec a) (coordVec b) * (x a * conj (y b)) := by
  calc α x y = α (∑ a, x a • coordVec a) (∑ b, y b • coordVec b) := by
        rw [← coordVec_expand x, ← coordVec_expand y]
    _ = _ := by
        rw [sesq_sum_left hα]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sesq_sum_right hα, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        ring

theorem pull_ofValues (L : V n →L[ℂ] V n) {α : V n → V n → ℂ} (hα : IsSesq α) :
    pull L (ofValues α : Alt n) = ofValues (fun ξ η => α (L ξ) (L η)) := by
  simp only [ofValues, sesq_expand hα (L _), AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym, map_sum,
    map_smul, map_mul, (pull_dz L _).1, (pull_dz L _).2, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul,
    Finset.smul_sum, smul_mul_smul_comm, smul_smul]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, c, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]

theorem repr_ofValues (α : V n → V n → ℂ) (S : Finset (Fin (n + n))) :
    (bas n).repr (ofValues α : Alt n) S =
      ∑ a, ∑ b, α (coordVec a) (coordVec b) * (bas n).repr (dz a * dzb b) S := by
  simp [ofValues, map_sum, Finsupp.finset_sum_apply, sym]

theorem dz_mul_dzb (a b : Fin n) : ∃ ε : ℤ, dz a * dzb b =
    (ε : ℂ) • bas n ({finSumFinEquiv (.inl a)} ∪ {finSumFinEquiv (.inr b)}) := by
  obtain ⟨ε, h⟩ := bas_mul (n := n) (S := {finSumFinEquiv (.inl a)}) (T := {finSumFinEquiv (.inr b)})
    (Finset.disjoint_singleton.2 (finSumFinEquiv.injective.ne Sum.inl_ne_inr))
  refine ⟨ε, ?_⟩
  rw [dz, dzb, ← bas_singleton, ← bas_singleton, h, Units.smul_def, Int.cast_smul_eq_zsmul]

theorem isType_ofValues (α : V n → V n → ℂ) : IsType 1 1 (ofValues α : Alt n) := by
  intro S hS
  rw [repr_ofValues] at hS
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  obtain ⟨ε, h⟩ := dz_mul_dzb a b
  have hb' := right_ne_zero_of_mul hb
  rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul] at hb'
  have hS' := (Finsupp.single_apply_ne_zero.1 (right_ne_zero_of_mul hb')).1
  subst hS'
  have ha' := a.2
  constructor
  · rw [Finset.card_eq_one]
    refine ⟨finSumFinEquiv (.inl a), ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
    omega
  · rw [Finset.card_eq_one]
    refine ⟨finSumFinEquiv (.inr b), ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
    omega

theorem isReal_ofValues {α : V n → V n → ℂ} (hα : ∀ ξ η, conj (α ξ η) = -α η ξ) : IsReal (ofValues α : Alt n) := by
  intro S
  have h₁ (a b : Fin n) : swap (dz a * dzb b) = -(dz b * dzb a) := by
    rw [map_mul, (swap_dz a).1, (swap_dz b).2, dz, dzb]
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  have h₂ (a b : Fin n) : conj ((bas n).repr (dz a * dzb b) S) = (bas n).repr (dz a * dzb b) S := by
    obtain ⟨ε, h⟩ := dz_mul_dzb a b
    rw [h, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
    split_ifs <;> simp
  have h₃ : swap (ofValues α : Alt n) = ∑ a, ∑ b, α (coordVec a) (coordVec b) • -(dz b * dzb a) := by
    simp only [ofValues, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym, map_sum, map_smul, h₁]
  rw [repr_ofValues, h₃, Finset.sum_comm]
  simp only [map_sum, map_smul, map_neg, map_mul, Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.neg_apply,
    smul_eq_mul, h₂, hα, mul_neg, neg_mul]

end Point

section Ext

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}

theorem isSesq_extTrace (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) : IsSesq (extTrace K z) := by
  have e : extTrace K z = fun ξ η => kappa * (secondForm K z ξ * secondFormAdj K z η).trace := by
    funext ξ η; exact extTrace_eq h hp ξ η
  have a₁ (ξ ξ' : E) : secondForm K z (ξ + ξ') = secondForm K z ξ + secondForm K z ξ' := by
    simp only [secondForm, blockQS, conn_add_vec, Matrix.mul_add, Matrix.add_mul]
  have a₂ (c : ℂ) (ξ : E) : secondForm K z (c • ξ) = c • secondForm K z ξ := by
    simp only [secondForm, blockQS, conn_smul_vec, Matrix.mul_smul, Matrix.smul_mul]
  have a₃ (η η' : E) : secondFormAdj K z (η + η') = secondFormAdj K z η + secondFormAdj K z η' := by
    simp only [secondFormAdj, adj, a₁, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  have a₄ (c : ℂ) (η : E) : secondFormAdj K z (c • η) = conj c • secondFormAdj K z η := by
    simp only [secondFormAdj, adj, a₂, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  rw [e]
  constructor <;> intros <;>
    simp only [a₁, a₂, a₃, a₄, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      trace_add, trace_smul, smul_eq_mul] <;> ring

theorem conj_extTrace (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (ξ η : E) :
    conj (extTrace K z ξ η) = -extTrace K z η ξ := by
  have hK := hp.self_of_nhds.isHermitian
  have hS := (isHermitian_subGram hK).transpose.inv
  have hQ := (isHermitian_quotGram hK).transpose
  have e : star (secondForm K z ξ * secondFormAdj K z η).trace =
      (secondForm K z η * secondFormAdj K z ξ).trace := by
    rw [← trace_conjTranspose]
    simp only [secondFormAdj, adj, conjTranspose_mul, conjTranspose_conjTranspose, hS.eq, hQ.eq,
      Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have ek : conj kappa = -kappa := by simp [kappa, neg_div, map_ofNat]
  rw [extTrace_eq h hp, extTrace_eq h hp, map_mul, ek, ← e, neg_mul]
  rfl

theorem contDiffAt_trace (hK : MContDiffAt ∞ K z) (hp : (K z).PosDef) (ξ η : E) :
    ContDiffAt ℝ ∞ (fun x => kappa * (secondForm K x ξ * secondFormAdj K x η).trace) z := by
  have hu : IsUnit (K z).det := hp.det_pos.ne'.isUnit
  have hs : IsUnit (subGram (K z)).det := (posDef_subGram hp).det_pos.ne'.isUnit
  have hc : ∀ ζ, MContDiffAt ∞ (fun x => secondForm K x ζ) z := fun ζ => by
    show MContDiffAt ∞ (fun x => quotMap m l * conn K x ζ * incl m l) z
    exact ((mContDiffAt_const _).mul (hK.conn hu (j := ∞) (by simp) ζ)).mul (mContDiffAt_const _)
  have ha : MContDiffAt ∞ (fun x => secondFormAdj K x η) z := by
    show MContDiffAt ∞ (fun x => (subGram (K x))ᵀ⁻¹ * (secondForm K x η)ᴴ * (quotGram (K x))ᵀ) z
    exact ((hK.subGram.transpose.inv (by rwa [det_transpose])).mul
      (hc η).conjTranspose).mul (hK.quotGram hs).transpose
  have hm := (hc ξ).mul ha
  simp only [Matrix.trace, Matrix.diag_apply]
  exact contDiffAt_const.mul (ContDiffAt.sum fun i _ => hm i i)

end Ext

section Var

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
  {S : ShortComplex X.Modules} {r s : ℕ} {h : Met p σ S.X₂ (r + s)}

theorem isRealForm_bcForm (hX : IsRegVar p D) (hS : S.ShortExact) (H : h.IsCInf)
    (f : CxPts p σ → VBExt.AdaptedChart S r s) (hf : ∀ y, y ∈ ptsIn p σ (f y).U) :
    (hX.atlas σ).IsRealForm 1 fun x => (ofValues (h.bcForm (f x.pt) x.1.1 x.pt) : Alt D) := by
  have hd (a : VBExt.AdaptedChart S r s) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
      (ha : y ∈ ptsIn p σ a.U) : MContDiffAt ∞ (fun v => h.gram a.frame (c.e.symm v)) (c.e y) :=
    (H.gram a.frame ha).mContDiffAt c hy
  refine ⟨⟨fun (c : AlgChart p σ D) T v (hv : v ∈ c.e.target) => ?_, fun x x' e => ?_⟩,
    fun x => ⟨isType_ofValues _, isReal_ofValues fun ξ η => ?_⟩⟩
  · have hWo := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (f (c.e.symm v)).U)
    have hm := hWo.mem_nhds (show v ∈ _ from ⟨hv, hf _⟩)
    have hK := hd (f (c.e.symm v)) c (c.e.map_target hv) (hf _)
    rw [c.e.right_inv hv] at hK
    have hp := h.posDef_gram_frame hS (f (c.e.symm v)) (hf _)
    have key : ContDiffAt ℝ ∞ (fun w => ∑ a, ∑ b, kappa *
        (secondForm (fun u => h.gram (f (c.e.symm v)).frame (c.e.symm u)) w (coordVec a) *
          secondFormAdj (fun u => h.gram (f (c.e.symm v)).frame (c.e.symm u)) w (coordVec b)).trace *
        (bas D).repr (dz a * dzb b) T) v :=
      ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => (contDiffAt_trace hK hp _ _).mul contDiffAt_const
    refine (key.congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [hm] with w hw
    have hw₁ : w ∈ ((hX.atlas σ).e c).target := hw.1
    refine (congrArg (fun t => (bas D).repr t T) (dif_pos hw₁)).trans ?_
    change (bas D).repr (ofValues (h.bcForm (f (c.e.symm w)) c (c.e.symm w)) : Alt D) T = _
    rw [repr_ofValues, Met.bcForm_eq hS (f (c.e.symm v)) _ c H (c.e.map_target hw.1) hw.2 (hf _), Met.bcForm]
    simp only [extTrace_eq ((hd _ c (c.e.map_target hw.1) hw.2).of_le (by norm_cast))
      (h.eventually_posDef hS _ c (c.e.map_target hw.1) hw.2)]
    rw [c.e.right_inv hw.1]
  · obtain ⟨⟨c, y⟩, hy⟩ := x
    obtain ⟨⟨c', y'⟩, hy'⟩ := x'
    obtain rfl : y = y' := e
    change AlgChart p σ D at c c'
    change y ∈ c.e.source at hy
    change y ∈ c'.e.source at hy'
    change (ofValues (h.bcForm (f y) c y) : Alt D) =
      pull (fderiv ℂ (c'.e ∘ c.e.symm) (c.e y)) (ofValues (h.bcForm (f y) c' y) : Alt D)
    have ho := ChartGlue.isOpen_over c.e c'.e.open_source
    have hm := ho.mem_nhds (ChartGlue.mem_over c.e hy hy')
    have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
    have hd' := (hd (f y) c' hy' (hf y)).of_le (j := 1) (by norm_cast)
    have hp := h.eventually_posDef hS _ c' hy' (hf y)
    rw [Met.bcForm, Met.bcForm, pull_ofValues _ (isSesq_extTrace hd' hp)]
    refine congrArg (fun α : V D → V D → ℂ => (ofValues α : Alt D)) (funext fun ξ => funext fun η => ?_)
    rw [extTrace_congr (K' := fun v => h.gram (f y).frame (c'.e.symm ((c'.e ∘ c.e.symm) v)))
        (eventually_of_mem hm fun v hv => by simp only [Function.comp_apply, c'.e.left_inv hv.2]),
      extTrace_comp_holo (K := fun v => h.gram (f y).frame (c'.e.symm v)) (e₂ ▸ hd') (e₂ ▸ hp)
        (contDiffAt_euclidean.2 fun i => ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ _ ho
          (differentiableOn_euclidean.1 (c.holo_trans c') i)).contDiffAt hm).of_le (by norm_cast)), e₂]
  · exact conj_extTrace ((hd (f x.pt) x.1.1 x.2 (hf _)).of_le (by norm_cast))
      (h.eventually_posDef hS _ x.1.1 x.2 (hf _)) ξ η

end Var

end GlobalTheory.LineForm.OmReal

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

theorem GlobalTheory.LineForm.isRealForm_omF : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), (hX.atlas σ).IsRealForm 1 (fld _ (omF hX σ h fl)) :=
  fun _ _ _ _ _ _ hX σ _ h H fl =>
    OmReal.isRealForm_bcForm (S := lineSC fl) (r := 1) (s := 1) (h := h.met σ) hX (lineSC_shortExact fl) (H σ)
      (frameAt fl) (mem_frameAt fl)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormSqZero
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open GlobalTheory.HermFrame

namespace GlobalTheory.LineForm

theorem coe_ofValues_mul {n : ℕ} (u v : ReciprocityTheory.L2DbarEstimates.V n → ℂ) :
    ((ofValues (fun ξ η => u ξ * v η) : Ev n) : Alt n) =
      ExteriorAlgebra.ι ℂ (∑ a, u (GlobalTheory.GoodMetric.coordVec a) • Pi.single (Sum.inl a) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) *
      ExteriorAlgebra.ι ℂ (∑ b, v (GlobalTheory.GoodMetric.coordVec b) • Pi.single (Sum.inr b) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) := by
  simp only [ofValues, map_sum, map_smul, Finset.sum_mul_sum, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_smul,
    smul_mul_smul_comm]
  rfl

theorem ofValues_mul_sq {n : ℕ} (u v : ReciprocityTheory.L2DbarEstimates.V n → ℂ) :
    (ofValues (fun ξ η => u ξ * v η) : Ev n) * ofValues (fun ξ η => u ξ * v η) = 0 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, coe_ofValues_mul]
  generalize (∑ a, u (GlobalTheory.GoodMetric.coordVec a) • Pi.single (Sum.inl a) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = x
  generalize (∑ b, v (GlobalTheory.GoodMetric.coordVec b) • Pi.single (Sum.inr b) (1 : ℂ) : Fin n ⊕ Fin n → ℂ) = y
  have h := Subalgebra.mem_center_iff.1 (ι_mul_ι_mem_center x y) (ExteriorAlgebra.ι ℂ y)
  rw [mul_assoc, h, mul_assoc (ExteriorAlgebra.ι ℂ x), ExteriorAlgebra.ι_sq_zero]
  simp

theorem ofValues_extTrace_sq {n : ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ)
    (z : ReciprocityTheory.L2DbarEstimates.V n) : (ofValues (extTrace G z) : Ev n) * ofValues (extTrace G z) = 0 := by
  have e : extTrace G z = fun ξ η => (kappa * extFormAdj G z ξ 0 0) * extForm G z η 0 0 := by
    funext ξ η
    simp [extTrace, Matrix.trace, Matrix.mul_apply, mul_assoc]
  rw [e]
  exact ofValues_mul_sq _ _

theorem omF_mul_self : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), omF hX σ h fl * omF hX σ h fl = 0 := by
  intro k _ X _ p D hX σ E h _ fl
  funext x
  exact ofValues_extTrace_sq _ _

end GlobalTheory.LineForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointTautologicalFrameStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_point_tautological_frame : ∀ (ι : Type) [Fintype ι] (N : ℕ)
    (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) N), Taut.IsTaut ι N fl →
    ∀ (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (g' : T ⟶ Fl ι N) (w : g' ≫ flStr ι N = g) (V : T.Opens) (hV : IsAffineOpen V)
    (G : ι → GL (Fin N) Γ(T, V)), V.ι ≫ g' = hV.isoSpec.hom ≫ flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd G →
    ∀ (a : ι) (l : Fin (N + 1)),
    ∃ s : Fin l → Γ((Scheme.Modules.pullback g').obj ((fl a).F l), V), IsFrame s ∧ ∀ j,
      ((Scheme.Modules.pullback g').map ((fl a).ι l) ≫
        (Scheme.Modules.pullbackComp g' (flStr ι N)).hom.app (Taut.stdE N) ≫
          (Scheme.Modules.pullbackCongr w).hom.app (Taut.stdE N)).app V (s j) =
        Loc.colSecOn g V (G a).1 (Fin.castLE l.is_le j) := by
  first | exact @GlobalTheory.FlagZ.LocTaut.exists_frame_pullback_taut | exact GlobalTheory.FlagZ.LocTaut.exists_frame_pullback_taut | (intros; apply GlobalTheory.FlagZ.LocTaut.exists_frame_pullback_taut <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagStalkColumnSpanStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
open GlobalTheory.Twist (resM)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_stalk_column_span : ∀ (ι : Type) [Fintype ι] (N : ℕ) (τ : ι) (l : ℕ) (y : Fl ι N) (g : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y)), flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = (Fl ι N).fromSpecStalk y → stalkStep ι N τ l y = colSpan (g τ).1 l := by
  first | exact @GlobalTheory.FlagZ.Univ.stalkStep_eq_colSpan | exact GlobalTheory.FlagZ.Univ.stalkStep_eq_colSpan | (intros; apply GlobalTheory.FlagZ.Univ.stalkStep_eq_colSpan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFibreOfLiftedPartialDerivationsStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_fibre_of_lifted_partialDerivations : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ : Type) [Finite σ] (B K : Type) [CommRing B] [IsRegularRing B] [Algebra (MvPolynomial σ Λ) B] [Field K] [Algebra (MvPolynomial σ Λ) K] [Algebra.EssFiniteType (MvPolynomial σ Λ) K], (∀ a : Λ, algebraMap (MvPolynomial σ Λ) K (MvPolynomial.C a) = 0 → a = 0) → (∀ s : σ, ∃ D : Derivation ℤ B B, ∀ x, D (algebraMap (MvPolynomial σ Λ) B x) = algebraMap (MvPolynomial σ Λ) B (MvPolynomial.pderiv s x)) → IsRegularRing (B ⊗[MvPolynomial σ Λ] K) := by
  first | exact @GlobalTheory.regularFibre_of_liftedPartialDerivations | exact GlobalTheory.regularFibre_of_liftedPartialDerivations | (intros; apply GlobalTheory.regularFibre_of_liftedPartialDerivations <;> assumption)
end

