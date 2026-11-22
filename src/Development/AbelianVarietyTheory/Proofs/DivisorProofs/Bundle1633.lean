import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1495
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0186
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1609
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1611
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1608
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaPowFixesOfCommutative
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelChernFormOfGramMatrixEqZero
section
open Set Matrix Filter Topology
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.ChernDel

variable {n : ℕ}

theorem del_del_comm {u : V n → ℂ} {z : V n} (hu : ContDiffAt ℝ 2 u z) (ξ η : V n) :
    del (fun x => del u x ξ) z η = del (fun x => del u x η) z ξ := by
  have h := differentiableAt_fderiv_of_contDiffAt_two hu
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have key : ∀ a b : V n, del (fun x => del u x a) z b = (1 / 2 : ℂ) • (del (fun x => fderiv ℝ u x a) z b -
      Complex.I • del (fun x => fderiv ℝ u x (Complex.I • a)) z b) := by
    intro a b
    simp only [del_apply u]
    rw [del_const_smul _ ((h1 _).fun_sub ((h1 _).fun_const_smul Complex.I)),
      del_sub (h1 _) ((h1 _).fun_const_smul Complex.I), del_const_smul _ (h1 _)]
    rfl
  rw [key, key]
  simp only [del_apply, fderiv_fderiv_apply hu, hs.eq ξ, hs.eq (Complex.I • ξ), smul_eq_mul]
  ring

section Mat

variable {r : Type} [Fintype r] [DecidableEq r]

theorem mdel_conn {H : V n → Matrix r r ℂ} {z : V n} (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (ξ η : V n) :
    mdel (fun x => conn H x ξ) z η = mdel (fun x => conn H x η) z ξ +
      (conn H z ξ * conn H z η - conn H z η * conn H z ξ) := by
  have h1 : MContDiffAt 1 H z := h.of_le one_le_two
  have hu' : IsUnit (H z)ᵀ.det := by rwa [det_transpose]
  have hc : mdel (fun x => mdel H x ξ) z η = mdel (fun x => mdel H x η) z ξ := by
    ext a b; exact del_del_comm (h a b) ξ η
  simp only [conn]
  rw [mdel_mul (h1.transpose.inv hu') (h.mdel (by norm_num) ξ).transpose,
    mdel_mul (h1.transpose.inv hu') (h.mdel (by norm_num) η).transpose,
    mdel_inv h1.transpose hu', mdel_inv h1.transpose hu', mdel_transpose (fun x => mdel H x ξ),
    mdel_transpose (fun x => mdel H x η), hc, mdel_transpose, mdel_transpose]
  simp only [Matrix.neg_mul, Matrix.mul_assoc]
  abel

theorem mdel_curv_comm {H : V n → Matrix r r ℂ} {z : V n} (h : MContDiffAt 3 H z) (hu : IsUnit (H z).det)
    {ξ η : V n} (hξ : conn H z ξ = 0) (hη : conn H z η = 0) (ζ : V n) :
    mdel (fun x => curv H x ξ ζ) z η = mdel (fun x => curv H x η ζ) z ξ := by
  have h2 : MContDiffAt 2 H z := h.of_le (by norm_num)
  have c2 : ∀ a, MContDiffAt 2 (fun x => conn H x a) z := fun a => h.conn hu (by norm_num) a
  have c1 : ∀ a, MContDiffAt 1 (fun x => conn H x a) z := fun a => (c2 a).of_le one_le_two
  have he : (fun x => mdel (fun y => conn H y ξ) x η) =ᶠ[𝓝 z] fun x => mdel (fun y => conn H y η) x ξ +
      (conn H x ξ * conn H x η + -(conn H x η * conn H x ξ)) := by
    filter_upwards [h2.eventually_two, h2.eventually_isUnit hu] with x h3 h4
    rw [mdel_conn h3 h4, sub_eq_add_neg]
  simp only [curv]
  rw [mdel_neg, mdel_neg, mdel_mdbar (c2 ξ), mdel_mdbar (c2 η), ← mdbar_mdel (c2 ξ), ← mdbar_mdel (c2 η),
    mdbar_congr he, mdbar_add ((c2 η).mdel (by norm_num) ξ) (((c1 ξ).mul (c1 η)).add ((c1 η).mul (c1 ξ)).neg),
    mdbar_add ((c1 ξ).mul (c1 η)) ((c1 η).mul (c1 ξ)).neg, mdbar_neg, mdbar_mul (c1 ξ) (c1 η),
    mdbar_mul (c1 η) (c1 ξ), hξ, hη]
  simp

end Mat

theorem delAt_congr {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : delAt α v = delAt β v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  exact congrArg (fun L => L (coordVec a) • bas n S)
    (GlobalTheory.del_congr (f := fun x => (bas n).repr (α x) S) (g := fun x => (bas n).repr (β x) S)
      (h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx))

theorem delAt_sum_smul {ι : Type} [Fintype ι] {v : V n} {u : ι → V n → ℂ} (hu : ∀ i, DifferentiableAt ℝ (u i) v)
    (α : ι → Alt n) :
    delAt (fun x => ∑ i, u i x • α i) v = ∑ c, ∑ i, del (u i) v (coordVec c) • (dz c * α i) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  have : coefwise (fun f => del f v (coordVec c)) (fun x => ∑ i, u i x • α i) =
      ∑ i, del (u i) v (coordVec c) • α i := by
    refine (bas n).ext_elem fun S => ?_
    rw [FormMul.repr_coefwise]
    simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
    rw [del_sum fun i _ => (hu i).mul_const _, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [del_mul (hu i) (differentiableAt_const _), del_const]
    simp
  rw [this, Finset.mul_sum]
  simp only [mul_smul_comm]

theorem delAt_add {v : V n} {F G : V n → Alt n} (hF : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x) S) v)
    (hG : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (G x) S) v) :
    delAt (fun x => F x + G x) v = delAt F v + delAt G v := by
  rw [delAt, delAt, delAt, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_add]
  congr 1
  refine (bas n).ext_elem fun S => ?_
  simp only [map_add, Finsupp.add_apply, FormMul.repr_coefwise]
  rw [del_add (hF S) (hG S), ContinuousLinearMap.add_apply]

theorem delAt_const (α : Alt n) (v : V n) : delAt (fun _ => α) v = 0 := by
  simp [delAt, coefwise]

def closedAt (v : V n) : Subalgebra ℂ (V n → Ev n) where
  carrier := {F | (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x : Alt n) S) v) ∧
    delAt (fun x => (F x : Alt n)) v = 0}
  mul_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · simp only [Pi.mul_apply, Subalgebra.coe_mul, FormMul.repr_mul (F _ : Alt n)]
      exact DifferentiableAt.fun_sum fun p _ => ((hF p.1).mul (hG p.2)).mul_const _
    · obtain ⟨y, hy⟩ := FormMul.delAt_mul hF hG
      simp only [Pi.mul_apply, Subalgebra.coe_mul]
      rw [hy, hF0, hG0, zero_mul, mul_zero, add_zero]
  add_mem' := by
    rintro F G ⟨hF, hF0⟩ ⟨hG, hG0⟩
    refine ⟨fun S => ?_, ?_⟩
    · simp only [Pi.add_apply, Subalgebra.coe_add, map_add, Finsupp.add_apply]
      exact (hF S).add (hG S)
    · simp only [Pi.add_apply, Subalgebra.coe_add]
      rw [delAt_add hF hG, hF0, hG0, add_zero]
  algebraMap_mem' c := ⟨fun S => differentiableAt_const ((bas n).repr (algebraMap ℂ (Ev n) c : Alt n) S),
    delAt_const (algebraMap ℂ (Ev n) c : Alt n) v⟩

theorem mem_closedAt {v : V n} {F : V n → Ev n} : F ∈ closedAt v ↔
    (∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (F x : Alt n) S) v) ∧ delAt (fun x => (F x : Alt n)) v = 0 :=
  Iff.rfl

theorem coeff_charpolyRev_map {R S r : Type} [CommRing R] [CommRing S] [Fintype r] [DecidableEq r] (f : R →+* S)
    (M : Matrix r r R) (j : ℕ) : (M.map f).charpolyRev.coeff j = f (M.charpolyRev.coeff j) := by
  rw [← Polynomial.coeff_map]
  congr 1
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  simp [Matrix.one_apply, apply_ite (Polynomial.map f)]

theorem mem_closedAt_of_symm {v : V n} {u : Fin n × Fin n → V n → ℂ} (hu : ∀ p, DifferentiableAt ℝ (u p) v)
    (hs : ∀ a b c, del (u (a, b)) v (coordVec c) = del (u (c, b)) v (coordVec a)) :
    (fun x => ∑ p, u p x • sym p) ∈ closedAt v := by
  refine mem_closedAt.2 ⟨fun S => ?_, ?_⟩
  · simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, map_sum, map_smul, Finsupp.finset_sum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    exact DifferentiableAt.fun_sum fun p _ => (hu p).mul_const _
  · simp only [AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul]
    rw [delAt_sum_smul hu]
    simp only [Fintype.sum_prod_type]
    set T : Alt n := ∑ c, ∑ a, ∑ b, del (u (a, b)) v (coordVec c) • (dz c * (sym (a, b) : Alt n)) with hT
    have h2 : T = -T := by
      conv_rhs => rw [hT, Finset.sum_comm]
      rw [hT]
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hs a b c, ← smul_neg]
      congr 1
      show dz c * (dz a * dzb b) = -(dz a * (dz c * dzb b))
      rw [← mul_assoc, ← mul_assoc, ← neg_mul]
      congr 1
      exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
    have h3 : (2 : ℂ) • T = 0 := by rw [two_smul]; nth_rewrite 2 [h2]; exact add_neg_cancel T
    exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

variable {r : Type} [Fintype r] [DecidableEq r]

theorem delAt_chernAt_of_conn_eq_zero {H : V n → Matrix r r ℂ} {v : V n} (h : MContDiffAt 3 H v)
    (hu : IsUnit (H v).det) (h0 : ∀ a, conn H v (coordVec a) = 0) (j : ℕ) :
    delAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  have hm : ∀ i k, (fun x => ∑ p : Fin n × Fin n, curv H x (coordVec p.1) (coordVec p.2) i k • sym p) ∈ closedAt v :=
    fun i k => mem_closedAt_of_symm (u := fun p x => curv H x (coordVec p.1) (coordVec p.2) i k)
      (fun p => (h.curv hu (j := 1) (by norm_num) _ _).diff i k)
      fun a b c => congrFun (congrFun (mdel_curv_comm h hu (h0 a) (h0 c) (coordVec b)) i) k
  let M : Matrix r r (closedAt v) := Matrix.of fun i k => ⟨_, hm i k⟩
  have e : (fun w => chernAt H w j) = (kappa ^ j • (-M).charpolyRev.coeff j : closedAt v) := by
    funext w
    let ev : closedAt v →+* Ev n := (Pi.evalRingHom (fun _ => Ev n) w).comp (closedAt v).val.toRingHom
    have e1 := coeff_charpolyRev_map ev (-M) j
    have e2 := coeff_charpolyRev_map (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toRingHom (-curvPoly H w) j
    have e3 : (-M).map ev = (-curvPoly H w).map (MvPolynomial.aeval (R := ℂ) (sym (n := n))).toRingHom := by
      ext i k : 2
      simp only [Matrix.map_apply, Matrix.neg_apply, map_neg]
      congr 1
      simp [M, ev, curvPoly, Fintype.sum_prod_type, Algebra.smul_def]
    rw [e3, e2] at e1
    show kappa ^ j • _ = kappa ^ j • ev _
    rw [← e1]
    rfl
  have := (kappa ^ j • (-M).charpolyRev.coeff j : closedAt v).2
  rw [← e] at this
  exact (mem_closedAt.1 this).2

theorem delAt_chernAt : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (H : V n → Matrix r r ℂ) (s : Set (V n)), IsOpen s → (∀ a b, ContDiffOn ℝ ∞ (fun v => H v a b) s) → (∀ v ∈ s, IsUnit (H v).det) → ∀ (j : ℕ), ∀ v ∈ s, delAt (fun w => (chernAt H w j : Alt n)) v = 0 := by
  intro n r _ _ H s hs hH hu j v hv
  have h3 : MContDiffAt 3 H v := fun a b => ((hH a b).contDiffAt (hs.mem_nhds hv)).of_le (by norm_cast)
  have h2 : MContDiffAt 2 H v := h3.of_le (by norm_num)
  let L : r → r → V n →L[ℂ] ℂ := fun i k => ∑ a, conn H v (coordVec a) i k • EuclideanSpace.proj a
  let A : V n → Matrix r r ℂ := fun w => Matrix.of fun i k => (1 : Matrix r r ℂ) i k + L i k v - L i k w
  have hAv : A v = 1 := by ext i k; simp [A]
  have hAa : ∀ w i k, AnalyticAt ℂ (fun w => A w i k) w := fun w i k => analyticAt_const.sub ((L i k).analyticAt w)
  have hA3 : MContDiffAt 3 A v := fun i k => (hAa v i k).contDiffAt.restrict_scalars ℝ
  have hAu : IsUnit (A v).det := by rw [hAv, det_one]; exact isUnit_one
  have hA0 : ∀ η, mdbar A v η = 0 := fun η => by
    ext a b
    rw [mdbar_apply, GlobalTheory.dbar_eq_zero (hAa v a b).differentiableAt]
    rfl
  have hAd : ∀ c, mdel A v (coordVec c) = -conn H v (coordVec c) := fun c => by
    ext i k
    rw [mdel_apply, del_eq_fderiv (hAa v i k).differentiableAt]
    have : HasFDerivAt (fun w => A w i k) (-L i k) v := (L i k).hasFDerivAt.const_sub _
    rw [this.fderiv]
    simp [L, Pi.single_apply]
  have hK : MContDiffAt 3 (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) v :=
    (hA3.transpose.mul h3).mul hA3.conjTranspose.transpose
  have hKu : IsUnit ((A v)ᵀ * H v * (A v)ᴴᵀ).det := by simpa [hAv] using hu v hv
  have he : (fun w => (chernAt H w j : Alt n)) =ᶠ[𝓝 v]
      fun w => (chernAt (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) w j : Alt n) := by
    filter_upwards [h2.eventually_two, h2.eventually_isUnit (hu v hv), hA3.eventually_isUnit hAu] with w a1 a2 a3
    rw [chernAt_changeFrame (fun x => (A x)ᵀ * H x * (A x)ᴴᵀ) H A w a1 a2 (hAa w) a3
      (Eventually.of_forall fun _ => rfl) j]
  rw [delAt_congr he]
  refine delAt_chernAt_of_conn_eq_zero hK hKu (fun a => ?_) j
  rw [conn_changeFrame (h3.of_le (by norm_num)) (hu v hv) (hA3.of_le (by norm_num)) hAu hA0, hAd, hAv]
  simp

end GlobalTheory.CxForm.ChernDel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneFormSkew
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC

open GlobalTheory.SmoothForms (gelfA)
open Formalism.REAL (GlRel qdet)

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def derEnd {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : Module.End ℂ (SmG σ J) where
  toFun f := ⟨lineDer γ f.1, isSm_lineDer f.2 hγ⟩
  map_add' f f' := Subtype.ext (lineDer_add f.2 f'.2 hγ)
  map_smul' a f := Subtype.ext (lineDer_smul a f.1 γ)

theorem exists_isDer (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} (τ : EmbOver E w) :
    ∃ D, IsDer σ J τ D := by
  classical
  let ρ : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ (SmG σ J) := fun Z =>
    if hZ : ∃ γ, IsLineOf σ J τ Z γ then derEnd (hZ.choose_spec.isRealLine h) else 0
  have hρ : ∀ Z γ, IsLineOf σ J τ Z γ → ∀ f : SmG σ J, (ρ Z f).1 = lineDer γ f.1 := fun Z γ hγ f => by
    have hZ : ∃ γ, IsLineOf σ J τ Z γ := ⟨γ, hγ⟩
    simp only [ρ, dif_pos hZ]
    rw [hγ.unique h hZ.choose_spec]; rfl
  obtain ⟨D, h1, h2⟩ := GlobalTheory.T.lie_algebra_rep_derivation_matrix n (J.map τ.1) (conjTranspose_map h hJ τ.1) (isUnit_det_map hJ τ.1) _ ρ
    (fun X X' hX hX' => by
      obtain ⟨γ, hγ⟩ := exists_isLineOf h hJ hX
      obtain ⟨δ, hδ⟩ := exists_isLineOf h hJ hX'
      obtain ⟨ε, hε⟩ := exists_isLineOf (τ := τ) (Z := X + X') h hJ (by
        rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hX', add_zero])
      refine LinearMap.ext fun f => Subtype.ext ?_
      rw [LinearMap.add_apply, Submodule.coe_add, hρ _ _ hγ, hρ _ _ hδ, hρ _ _ hε]
      exact (GlobalTheory.T.line_derivative_additive F E σ h n J hJ w τ f.1 f.2 X X' γ δ ε hγ hδ).1 hε)
    (fun c X hX => by
      obtain ⟨γ, hγ⟩ := exists_isLineOf h hJ hX
      refine LinearMap.ext fun f => Subtype.ext ?_
      rw [LinearMap.smul_apply, Submodule.coe_smul, hρ _ _ hγ, hρ _ _ (hγ.smul c)]
      funext g
      have hd := ((differentiable_of_isSm f.2 (hγ.isRealLine h) g) (0 * c)).hasDerivAt.scomp (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).mul_const c)
      have := hd.deriv
      simp only [zero_mul, one_mul] at this
      simpa [lineDer, Function.comp_def] using this)
    (fun X X' hX hX' => by
      obtain ⟨γ, hγ⟩ := exists_isLineOf h hJ hX
      obtain ⟨δ, hδ⟩ := exists_isLineOf h hJ hX'
      obtain ⟨ε, hε⟩ := exists_isLineOf (τ := τ) (Z := X * X' - X' * X) h hJ (by
        have e1 := eq_neg_of_add_eq_zero_left hX
        have e2 := eq_neg_of_add_eq_zero_left hX'
        rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.sub_mul, Matrix.mul_assoc,
          Matrix.mul_assoc, e1, e2, Matrix.mul_neg, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, e2,
          Matrix.mul_sub]
        simp [Matrix.mul_assoc])
      refine LinearMap.ext fun f => Subtype.ext ?_
      rw [LinearMap.sub_apply, Submodule.coe_sub, Module.End.mul_apply, Module.End.mul_apply, hρ _ _ hγ, hρ _ _ hδ,
        hρ _ _ hδ, hρ _ _ hγ, hρ _ _ hε]
      exact (GlobalTheory.T.line_derivative_additive F E σ h n J hJ w τ f.1 f.2 X X' γ δ ε hγ hδ).2 hε)
  exact ⟨D, h1, fun Z γ hγ f => by rw [h2 Z (hγ.skew h)]; exact hρ Z γ hγ f⟩

theorem glRel_frame {B : Type} [Ring B] [Algebra ℂ B] {m : ℕ} (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] B)
    (hD : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) {Q : Matrix (Fin n) (Fin m) ℂ} {R : Matrix (Fin m) (Fin n) ℂ}
    (hRQ : R * Q = 1) : GlRel fun a b : Fin m => D (Q * Matrix.single a b (1 : ℂ) * R) := by
  intro a b c d
  have e : ∀ a b c d : Fin m, Q * Matrix.single a b (1 : ℂ) * R * (Q * Matrix.single c d (1 : ℂ) * R) =
      if b = c then Q * Matrix.single a d (1 : ℂ) * R else 0 := fun a b c d => by
    have : Q * Matrix.single a b (1 : ℂ) * R * (Q * Matrix.single c d (1 : ℂ) * R) =
        Q * (Matrix.single a b (1 : ℂ) * (R * Q) * Matrix.single c d 1) * R := by simp only [Matrix.mul_assoc]
    rw [this, hRQ, Matrix.mul_one]
    split_ifs with hbc
    · subst hbc; rw [Matrix.single_mul_single_same, mul_one]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hbc]; simp
  rw [← hD, e, e, map_sub]
  congr 1 <;> split_ifs <;> simp

theorem eq_sum_frame {m : ℕ} {Q : Matrix (Fin n) (Fin m) ℂ} {R : Matrix (Fin m) (Fin n) ℂ} (hQR : Q * R = 1)
    (X : Matrix (Fin n) (Fin n) ℂ) : X = ∑ a, ∑ b, (R * X * Q) a b • (Q * Matrix.single a b (1 : ℂ) * R) := by
  have e : ∑ a, ∑ b, (R * X * Q) a b • (Q * Matrix.single a b (1 : ℂ) * R) =
      Q * (∑ a, ∑ b, Matrix.single a b ((R * X * Q) a b)) * R := by
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e, ← Matrix.matrix_eq_sum_single]
  simp only [← Matrix.mul_assoc, hQR, Matrix.one_mul]
  rw [Matrix.mul_assoc, hQR, Matrix.mul_one]

theorem qdet_mem {B : Type} [Ring B] [Algebra ℂ B] {m : ℕ} (X : Fin m → Fin m → B) (S : Subalgebra ℂ B)
    (hS : ∀ a b, X a b ∈ S) (u : ℂ) : qdet X u ∈ S := by
  unfold qdet Formalism.REAL.qminor
  refine S.sum_mem fun π _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  unfold Formalism.REAL.Tm
  refine S.add_mem ?_ (hS _ _)
  split_ifs
  exacts [S.algebraMap_mem _, S.zero_mem]

theorem gelfA_mem {B : Type} [Ring B] [Algebra ℂ B] {m : ℕ} (X : Fin m → Fin m → B) (S : Subalgebra ℂ B)
    (hS : ∀ a b, X a b ∈ S) (k : ℕ) : gelfA X k ∈ S := by
  unfold gelfA
  refine S.sum_mem fun π _ => S.list_prod_mem fun x hx => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  exact hS _ _

theorem finite_of_gelf (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (D : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)) (hD : ∀ w, IsDer σ J (τ w) (D w))
    (v : SmG σ J) (hv : ∀ w, FiniteDimensional ℂ (Submodule.span ℂ {x | ∃ a ∈ Algebra.adjoin ℂ
      (Set.range (gelfA fun a b => D w (Matrix.single a b 1))), x = a v})) :
    FiniteDimensional ℂ (Submodule.span ℂ {u | ∃ z, IsCentral σ J z ∧ u = dop z v.1}) := by
  classical
  let X : InfinitePlace F → Fin n → Fin n → Module.End ℂ (SmG σ J) := fun w a b => D w (Matrix.single a b 1)
  have hG : ∀ w, GlRel (X w) := fun w => by
    simpa using glRel_frame (D w) (hD w).1 (Q := 1) (R := 1) (Matrix.mul_one _)
  have hc : ∀ w w', w ≠ w' → ∀ a b c d, X w a b * X w' c d = X w' c d * X w a b := fun w w' hne a b c d =>
    GlobalTheory.T.derivations_commute_distinct_places F E σ h n J hJ w (τ w) (D w) (hD w) w' (τ w') (D w') (hD w') hne _ _
  obtain ⟨W, hW, hvW, hs⟩ := GlobalTheory.FiniteOrbit.exists_finiteDimensional_stable (SmG σ J) (InfinitePlace F)
    (fun w => Algebra.adjoin ℂ (Set.range (gelfA (X w)))) (fun w w' hne a ha b hb => by
      have h1 : ∀ c d, a * X w' c d = X w' c d * a := fun c d => by
        have : Algebra.adjoin ℂ (Set.range (gelfA (X w))) ≤ Subalgebra.centralizer ℂ {X w' c d} := by
          refine Algebra.adjoin_le ?_
          rintro _ ⟨k, rfl⟩
          exact gelfA_mem _ _ (fun a b => by rintro _ rfl; exact (hc w w' hne a b c d).symm) k
        exact (this ha _ rfl).symm
      have : Algebra.adjoin ℂ (Set.range (gelfA (X w'))) ≤ Subalgebra.centralizer ℂ {a} := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨k, rfl⟩
        exact gelfA_mem _ _ (fun c d => by rintro _ rfl; exact h1 c d) k
      exact this hb _ rfl) v hv
  let A := Algebra.adjoin ℂ (Set.range fun p : InfinitePlace F × Fin n × Fin n => X p.1 p.2.1 p.2.2)
  have hDA : ∀ w Z, D w Z ∈ A := fun w Z => by
    rw [Matrix.matrix_eq_sum_single Z]
    simp only [map_sum]
    refine A.sum_mem fun a _ => A.sum_mem fun b _ => ?_
    rw [← mul_one (Z a b), ← smul_eq_mul, ← Matrix.smul_single, map_smul]
    exact A.smul_mem (Algebra.subset_adjoin ⟨(w, a, b), rfl⟩) _
  have hword : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ u ∈ A, ∀ f : SmG σ J, l.foldr lineDer f.1 = (u f).1 := fun l => by
    induction l with
    | nil => exact fun _ => ⟨1, A.one_mem, fun f => rfl⟩
    | cons γ l ih =>
      intro hl
      obtain ⟨u, hu, e⟩ := ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
      obtain ⟨w, Z, hZ⟩ := GlobalTheory.T.real_line_is_line_of_place F E σ h n J hJ τ γ (hl γ List.mem_cons_self)
      exact ⟨D w Z * u, A.mul_mem (hDA w Z) hu, fun f => by
        rw [List.foldr_cons, e, Module.End.mul_apply, (hD w).2 Z γ hZ]⟩
  refine Submodule.finiteDimensional_of_le (S₂ := W.map (SmG σ J).subtype) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  choose! u hu he using fun l (hl : l ∈ z.support) => hword l (hz.1 l hl)
  let U := ∑ l ∈ z.support, z l • u l
  have hU : ∀ f : SmG σ J, dop z f.1 = (U f).1 := fun f => by
    rw [LinearMap.sum_apply, Submodule.coe_sum]
    funext g
    simp only [dop, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ← he l hl]
  have hline : ∀ w Z γ, IsLineOf σ J (τ w) Z γ → D w Z * U = U * D w Z := fun w Z γ hγ =>
    LinearMap.ext fun f => Subtype.ext (by
      rw [Module.End.mul_apply, Module.End.mul_apply, (hD w).2 Z γ hγ, ← hU, ← hU, (hD w).2 Z γ hγ]
      exact GlobalTheory.UAut.CentralComm.lineDer_dop_comm F E σ n J z hz f.1 f.2 γ (hγ.isRealLine h))
  have hmem := GlobalTheory.T.centre_generated_by_gelfand GlobalTheory.T.relativeCentre' _ _ n X hG hc U (A.sum_mem fun l hl => A.smul_mem (hu l hl) _) fun w a b => by
    obtain ⟨γ₁, γ₂, h1, h2, e⟩ := exists_lines h hJ (τ w) (Matrix.single a b 1)
    change D w _ * U = U * D w _
    rw [e, map_add, map_smul (D w) Complex.I, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, hline w _ _ h1,
      hline w _ _ h2]
  have key : ∀ a ∈ Algebra.adjoin ℂ (Set.range fun p : InfinitePlace F × ℕ => gelfA (X p.1) p.2), ∀ x ∈ W, a x ∈ W := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hs p.1 _ (Algebra.subset_adjoin ⟨p.2, rfl⟩)
    | algebraMap r => intro x hx; exact W.smul_mem r hx
    | add x y _ _ hx hy => intro f hf; exact add_mem (hx f hf) (hy f hf)
    | mul x y _ _ hx hy => intro f hf; exact hx _ (hy f hf)
  exact ⟨U v, key U hmem v hvW, (hU v).symm⟩

end General

theorem frame_unit_apply {n m : ℕ} {Q : Matrix (Fin n) (Fin m) ℂ} {R : Matrix (Fin m) (Fin n) ℂ} (hRQ : R * Q = 1)
    (p q : Fin m) : R * (Q * Matrix.single p q (1 : ℂ) * R) * Q = Matrix.single p q 1 := by
  have : R * (Q * Matrix.single p q (1 : ℂ) * R) * Q = R * Q * Matrix.single p q (1 : ℂ) * (R * Q) := by
    simp only [Matrix.mul_assoc]
  rw [this, hRQ, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.LeviHC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaLiftOfPurelyInseparableStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_lift_of_purelyInseparable_alt : ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra L Ω'] [Algebra K Ω'] (j : Ω →ₐ[K] Ω'), (∀ y : Ω', ∃ (m : ℕ) (x : Ω), 0 < m ∧ y ^ m = j x ∧ ∀ a b : Ω', (a - b) ^ m = a ^ m - b ^ m) → ∀ (V' : ValuationSubring Ω') (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[L] Ω'), (∀ x, σ' (j x) = j (σ x)) → σ ∈ inertia K (V'.comap (j : Ω →+* Ω')) → σ' ∈ inertia L V' := by
  first | exact @GlobalTheory.inertia_lift_of_purelyInseparable | exact GlobalTheory.inertia_lift_of_purelyInseparable | (intros; apply GlobalTheory.inertia_lift_of_purelyInseparable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertiaPowFixesOfCommutativeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_pow_fixes_of_commutative_alt : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (L : IntermediateField K Ω), FiniteDimensional K L → IsGalois K L → (∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) → ∀ σ ∈ inertia K V, ∃ a : ℕ, ∀ x ∈ L, (σ ^ ((Nat.card (ResidueField R) - 1) * ringChar (ResidueField R) ^ a)) x = x := by
  first | exact @GlobalTheory.TameInertia.inertia_pow_fixes_of_commutative | exact GlobalTheory.TameInertia.inertia_pow_fixes_of_commutative | (intros; apply GlobalTheory.TameInertia.inertia_pow_fixes_of_commutative <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralReTopDegreeDensityDbarEqZeroStatement
section
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_re_topDegreeDensity_dbar_eq_zero : ∀ {n : ℕ} (F : V n → GlobalTheory.CxForm.Alt n), (∀ S, ContDiff ℝ 1 (fun v => (GlobalTheory.CxForm.bas n).repr (F v) S)) → HasCompactSupport F → ∫ v, (GlobalTheory.CxForm.dens (GlobalTheory.CxForm.dbarAt F v)).re = 0 := by
  first | exact @GlobalTheory.CxForm.integral_re_dens_dbarAt_eq_zero | exact GlobalTheory.CxForm.integral_re_dens_dbarAt_eq_zero | (intros; apply GlobalTheory.CxForm.integral_re_dens_dbarAt_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSqLeSumLintegralEnormSqOfPointwiseStatement
section
open IsDedekindDomain NumberField
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_sq_le_sum_lintegral_enorm_sq_of_pointwise : ∀ (E : Type) [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E] (μ : MeasureTheory.Measure E)
    (ι : Type) [Fintype ι] (f : E → ℝ) (g : ι → E → ℂ) (C : ℝ), (∀ a, Continuous (g a)) →
    (∀ x, f x ^ 2 ≤ C * ∑ a, ‖g a x‖ ^ 2) →
    ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) ≤ ENNReal.ofReal C * ∑ a, ∫⁻ x, ‖g a x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound | exact GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound | (intros; apply GlobalTheory.sq_le_sum_enorm_sq_lintegral_bound <;> assumption)
end

