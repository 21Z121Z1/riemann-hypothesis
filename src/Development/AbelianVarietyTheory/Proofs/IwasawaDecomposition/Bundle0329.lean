import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0005
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.IndefiniteReal.PrincipalLevelLattice
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0313
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MSmoothAndSemiPosIff
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
open Set Filter Topology GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.ChartGlue

namespace GlobalTheory.TrueGeo.InducedSemiPos

section BaseChange

variable {k k' : Type} [CommRing k] [CommRing k'] {ρ : k →+* k'} {X Z : Scheme.{0}} {p : X ⟶ Sp k}
  {q : Z ⟶ Sp k'} {j : Z ⟶ X} {σ : k →+* ℂ} {τ : k' →+* ℂ} {D : ℕ} {m : CxPts q τ → CxPts p σ}

theorem exists_chart_levi (H : IsPullback j q p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ j)
    (c : AlgChart p σ D) {z : CxPts q τ} (hz : m z ∈ c.e.source) :
    ∃ c' : AlgChart q τ D, z ∈ c'.e.source ∧
      ∀ (f : CxPts p σ → ℝ) (ξ : Fin D → ℂ), c'.levi (fun w => f (m w)) z ξ = c.levi f (m z) ξ := by
  obtain ⟨c', hz', h, hx⟩ := c.exists_baseChange H hm hz
  have he (w) (h₁ : w ∈ c'.e.source) (h₂ : m w ∈ c.e.source) : c.e (m w) = c'.e w := by
    ext a
    rw [c.apply_eq _ h₂, c'.apply_eq _ h₁, hx, ev_appLE_of_comp hm h _ (c'.source_subset h₁)]
  have ho := isOpen_over c'.e (c.e.open_source.preimage (continuous_of_comp hm))
  refine ⟨c', hz', fun f ξ => ?_⟩
  rw [AlgChart.levi, AlgChart.levi, he z hz' hz]
  refine congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.leviV_congr
    (eventually_of_mem (ho.mem_nhds (mem_over c'.e hz' hz)) fun v hv => ?_) ξ)
  have e := he _ (c'.e.map_target hv.1) hv.2
  rw [c'.e.right_inv hv.1] at e
  have e' : c.e.symm v = m (c'.e.symm v) := by
    conv_lhs => rw [← e]
    exact c.e.left_inv hv.2
  simp only [e']

theorem semiPos_pull_iff (H : IsPullback j q p (spMap ρ)) (hm : ∀ z, (m z).1 = z.1 ≫ j)
    (hs : Function.Surjective m) (R : AnRead p σ D) (R' : AnRead q τ D) {B : LB X} {φ : Weight p σ B}
    {φ' : Weight q τ (B.pull j)} (hφ' : φ'.IsSmooth R')
    (e : ∀ i z, φ'.φ i z = φ.φ (i PUnit.unit) (m z)) :
    φ'.SemiPos R' ↔ φ.SemiPosReg D := by
  have hi {a : B.ι} {z : CxPts q τ} (h : m z ∈ ptsIn p σ (B.U a)) : z ∈ ptsIn q τ ((B.pull j).U fun _ => a) :=
    ptsIn_mono (fun _ hx => mem_iInter.2 fun _ => hx) ((mem_ptsIn_preimage hm).2 h)
  refine ⟨fun h a c y hy ξ => ?_, fun h => hφ'.semiPos_of_exists fun z => ?_⟩
  · obtain ⟨z, rfl⟩ := hs y
    obtain ⟨c', hz', hl⟩ := exists_chart_levi H hm c hy.1
    exact (h.chart hφ' hz' (hi hy.2) ξ).trans_eq
      ((congrArg (c'.levi · z ξ) (funext (e _))).trans (hl _ ξ))
  · obtain ⟨a, ha⟩ := R.cover (m z)
    obtain ⟨c', hz', hl⟩ := exists_chart_levi H hm (R.chart a) ha
    refine ⟨c', _, hz', hi (mem_pick φ.isLB (m z)), fun ξ => ?_⟩
    have h₁ : c'.levi (φ'.φ fun _ => pick φ.isLB (m z)) z ξ = (R.chart a).levi (φ.φ (pick φ.isLB (m z))) (m z) ξ :=
      (congrArg (c'.levi · z ξ) (funext (e _))).trans (hl _ ξ)
    exact le_of_le_of_eq (h _ (R.chart a) _ ⟨ha, mem_pick φ.isLB (m z)⟩ ξ) h₁.symm

end BaseChange

section Power

open Var

variable {F : Type} [Field F] {Y : Var F} {σ : F →+* ℂ} {Δ : Y.Dv} {m : Met Y σ Δ} {k : ℕ}

theorem mSmooth_of_mPow (hk : k ≠ 0) (h : mSmooth Y σ _ (mPow Y σ Δ k m)) : mSmooth Y σ Δ m := by
  have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  refine ⟨fun y hy => ?_, fun g => ?_⟩
  · have h₁ := mem_eqnSet Δ y
    have h₂ := (Met.mem_posSet_iff (CartierDiv.IsEqn.nsmul h₁ k)).1 (h.1 hy)
    rw [mPow_h h₁] at h₂
    exact lt_of_le_of_ne (m.nonneg _ _) fun e => h₂.ne' (by rw [← e, zero_pow hk])
  · refine AnRead.SmoothOn.congr (f := fun y => (k : ℝ)⁻¹ * (mPow Y σ Δ k m).wt (g ^ k) y)
      (fun c => contDiffOn_const.mul ((h.2 (g ^ k)).mono
        (fun _ hz => ⟨trivial, CartierDiv.IsEqn.nsmul hz.2 k⟩) c)) fun y hy => ?_
    rw [wt_mPow hy.2, inv_mul_cancel_left₀ hk']

theorem mPsh_mPow_iff (hk : k ≠ 0) (h : mSmooth Y σ Δ m) :
    mPsh Y σ _ (mPow Y σ Δ k m) 0 ↔ mPsh Y σ Δ m 0 := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)
  have h' : mSmooth Y σ _ (mPow Y σ Δ k m) := Met.SmoothOn.mPow isOpen_univ h k
  have key (c : AlgChart Y.str σ Y.dim) (g : Y.Fnˣ) (y : Y.pts σ) (hy : y ∈ c.e.source) (hg : y ∈ eqnSet σ Δ g) (ξ) :
      c.levi (fun z => (mPow Y σ Δ k m).wt (g ^ k) z + (0 : Y.pts σ → ℝ) z) y ξ =
        k * c.levi (fun z => m.wt g z + (0 : Y.pts σ → ℝ) z) y ξ := by
    simp only [Pi.zero_apply, add_zero]
    rw [AlgChart.levi_congr (isOpen_eqnSet Δ g) hy hg fun z hz => wt_mPow hz k]
    exact AlgChart.levi_const_mul _ (((h.2 g).mono fun _ hz => ⟨trivial, hz⟩).contDiffAt_two
      (isOpen_eqnSet Δ g) hy hg) ξ
  rw [h.mPsh_iff_levi smoothOn_zero, h'.mPsh_iff_levi smoothOn_zero]
  refine ⟨fun H c g y hy hg ξ => ?_, fun H c g y hy hg ξ => ?_⟩
  · have := H c (g ^ k) y hy (CartierDiv.IsEqn.nsmul hg k) ξ
    rw [key c g y hy hg] at this
    exact nonneg_of_mul_nonneg_right this hk'
  · have h₁ := mem_eqnSet Δ y
    rw [h'.levi_frame smoothOn_zero hy (CartierDiv.IsEqn.nsmul h₁ k) hg, key c _ y hy h₁]
    exact mul_nonneg hk'.le (H c _ y hy h₁ ξ)

theorem smooth_psh_of_weight {L : LB Y.X} {r : L.ι → Y.Fnˣ} (hp : Presents Δ L r) {φ : Weight Y.str σ L}
    (hφ : φ.IsSmooth (Y.an σ)) (t : ℝ)
    (h : ∀ i, ∀ y ∈ ptsIn Y.str σ (L.U i), Real.exp (-t) * m.h (r i) y = Real.exp (-φ.φ i y)) :
    mSmooth Y σ Δ m ∧ (mPsh Y σ Δ m 0 ↔ φ.SemiPos (Y.an σ)) := by
  have h₁ (i y) (hy : y ∈ ptsIn Y.str σ (L.U i)) : m.h (r i) y = Real.exp (t - φ.φ i y) := by
    rw [sub_eq_add_neg, Real.exp_add, ← h i y hy, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have h₂ (i y) (hy : y ∈ ptsIn Y.str σ (L.U i)) : m.wt (r i) y = 1 * φ.φ i y + -t := by
    rw [Met.wt, h₁ i y hy, Real.log_exp]
    ring
  have hs : mSmooth Y σ Δ m := Met.smoothOn_of_cover isOpen_univ
    (fun y _ => by
      have hi := mem_pick φ.isLB y
      rw [Met.mem_posSet_iff (ptsIn_subset_eqnSet hp _ hi), h₁ _ y hi]
      exact Real.exp_pos _)
    (fun i => isOpen_ptsIn (L.U i)) (fun y => ⟨_, mem_pick φ.isLB y⟩) (ptsIn_subset_eqnSet hp) fun i =>
    AnRead.SmoothOn.congr (f := fun y => 1 * φ.φ i y + -t)
      (fun c => (contDiffOn_const.mul ((hφ i).mono inter_subset_right c)).add contDiffOn_const)
      fun y hy => h₂ i y hy.2
  refine ⟨hs, ?_⟩
  rw [hs.mPsh_iff_semiPos smoothOn_zero hp]
  refine forall₂_congr fun i c => forall₂_congr fun y hy => forall_congr' fun ξ => ?_
  refine iff_of_eq (congrArg (0 ≤ ·) ((AlgChart.levi_congr (c := (Y.an σ).chart c) (isOpen_ptsIn (L.U i))
    hy.1 hy.2 (g := fun z => 1 * φ.φ i z + -t) (fun z hz => (add_zero _).trans (h₂ i z hz)) ξ).trans ?_))
  refine (congrArg Complex.re (ReciprocityTheory.L2DbarEstimates.Y.leviV_const_mul (hφ.contDiffAt_two hy.1 hy.2) 1 (-t) ξ)).trans ?_
  rw [Complex.ofReal_one, one_mul]
  rfl

end Power

theorem mSmooth_and_semiPos_iff : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced M L k cf → (∀ σ, C.mSmooth Y σ A.D (A.m σ)) ∧ (A.SemiPos ↔ L.SemiPos Y.dim) := by
  intro F _ _ C Y A M L k cf ⟨_, r, hr, hi, _⟩
  obtain rfl := C.eq_std
  have key (σ : F →+* ℂ) : Var.mSmooth Y σ A.D (A.m σ) ∧
      (Var.mPsh Y σ A.D (A.m σ) 0 ↔ (L.φ (σ.comp (algebraMap (𝓞 F) F))).SemiPosReg Y.dim) := by
    obtain ⟨R⟩ := ModelCharts.genSmooth_model F Y M (σ.comp (algebraMap (𝓞 F) F))
    have hm : ∀ z, (bcMap M.pb.w σ z).1 = z.1 ≫ M.j := fun _ => rfl
    let φ : Weight Y.str σ (L.B.pull M.j) :=
      (L.φ (σ.comp (algebraMap (𝓞 F) F))).linComb _ _ (fun _ => bcMap M.pb.w σ) fun _ => hm
    have hφ : φ.IsSmooth (Y.an σ) := ((Weight.isCInf_iff_isSmooth R).1 (L.cInf _)).linComb _ _ _ _ _
    have e (i z) : φ.φ i z = (L.φ _).φ (i PUnit.unit) (bcMap M.pb.w σ z) :=
      (Fintype.sum_unique fun a : PUnit.{1} =>
        ((1 : ℤ) : ℝ) * (L.φ _).φ (i a) (bcMap M.pb.w σ z)).trans (by simp)
    obtain ⟨h₁, h₂⟩ := smooth_psh_of_weight (m := Var.mPow Y σ A.D k (A.m σ)) hr hφ
      (2 * (k : ℕ) * (A.n : ℕ) * A.ci (InfinitePlace.mk σ)) fun i y hy => by
        have h₃ := Var.ptsIn_subset_eqnSet hr i hy
        have h₄ := hi σ y _ i (((r i)⁻¹ : Y.Fnˣ) : Y.Fn) (hm y) (mem_ptsIn.1 hy) (by
          rw [Units.val_inv_eq_inv_val]
          exact (CartierDiv.isEqn_iff_generatesAt_inv.1 h₃).regularAt)
        rw [Units.inv_mul, Base.ratVal_one, norm_one, one_pow, one_mul] at h₄
        rw [e, ← h₄, ← Var.pn_frame h₃]
    have h₅ := mSmooth_of_mPow k.ne_zero h₁
    exact ⟨h₅, (mPsh_mPow_iff k.ne_zero h₅).symm.trans (h₂.trans
      (semiPos_pull_iff M.pb hm (bijective_bcMap M.pb σ).2 R _ hφ e))⟩
  refine ⟨fun σ => (key σ).1, fun h τ => ?_, fun h σ => ⟨(key σ).1, (key σ).2.2 (h _)⟩⟩
  obtain ⟨σ, rfl⟩ : ∃ σ : F →+* ℂ, σ.comp (algebraMap (𝓞 F) F) = τ :=
    ⟨IsFractionRing.lift (K := F) (ModelCharts.injective_emb τ),
      RingHom.ext fun x => IsFractionRing.lift_algebraMap (K := F) (ModelCharts.injective_emb τ) x⟩
  exact (key σ).2.1 (h σ).2

end GlobalTheory.TrueGeo.InducedSemiPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MajAtSmulRightOf
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.MetBase

open Formalism.HermitianLatticesTheory

section Polar

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem fcoord_smul_emb (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x : V) : fcoord b X v (a • x) = v.embedding a • fcoord b X v x := by
  have hv : vecAt b v (a • x) = v.embedding a • vecAt b v x := by
    funext i; simp [vecAt, map_mul]
  simp only [fcoord, hv, Matrix.mulVec_smul]

theorem fcoord_add_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y : V) : fcoord b X v (x + y) = fcoord b X v x + fcoord b X v y := by
  have hv : vecAt b v (x + y) = vecAt b v x + vecAt b v y := by
    funext i; simp [vecAt, map_add]
  simp only [fcoord, hv, Matrix.mulVec_add]

theorem majAt_add_left_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x x' y : V) : majAt b X v (x + x') y = majAt b X v x y + majAt b X v x' y := by
  simp only [majAt, fcoord_add_of b X v x x', Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]

theorem majAt_add_right_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x y y' : V) : majAt b X v x (y + y') = majAt b X v x y + majAt b X v x y' := by
  simp only [majAt, fcoord_add_of b X v y y', Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem majAt_smul_left_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x y : V) : majAt b X v (a • x) y = star (v.embedding a) * majAt b X v x y := by
  simp only [majAt, fcoord_smul_emb, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem majAt_smul_right_of (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a : K) (x y : V) : majAt b X v x (a • y) = v.embedding a * majAt b X v x y := by
  simp only [majAt, fcoord_smul_emb, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem majAt_self_eq (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    majAt b X v x x = (((normAt b X v x) ^ 2 : ℝ) : ℂ) := by
  unfold normAt cnorm majAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  ring

theorem majAt_eq_of_diag {V' ι' : Type} [AddCommGroup V'] [Module K V'] [Fintype ι'] [DecidableEq ι']
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Module.Basis ι' K V')
    (X' : InfinitePlace K → Matrix ι' ι' ℂ) (v : InfinitePlace K) (e : V' →ₗ[K] V)
    (hv : ∃ a : K, star (v.embedding a) ≠ v.embedding a)
    (h : ∀ x, majAt b X v (e x) (e x) = majAt b' X' v x x) (x y : V') :
    majAt b X v (e x) (e y) = majAt b' X' v x y := by
  have hadd : ∀ x y : V', (majAt b X v (e x) (e y) - majAt b' X' v x y) +
      (majAt b X v (e y) (e x) - majAt b' X' v y x) = 0 := by
    intro x y
    have h0 := h (x + y)
    have h1 := h x
    have h2 := h y
    simp only [map_add, majAt_add_left_of, majAt_add_right_of] at h0
    linear_combination h0 - h1 - h2
  obtain ⟨a, ha⟩ := hv
  have h3 := hadd x (a • y)
  simp only [map_smul, majAt_smul_left_of, majAt_smul_right_of] at h3
  have h4 := hadd x y
  have h5 : (v.embedding a - star (v.embedding a)) * (majAt b X v (e x) (e y) - majAt b' X' v x y) = 0 := by
    linear_combination h3 - star (v.embedding a) * h4
  have h6 : v.embedding a - star (v.embedding a) ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_left h6)

end Polar

theorem exists_nonreal {K : Type} [Field K] (v : InfinitePlace K) (hv : v.IsComplex) :
    ∃ a : K, star (v.embedding a) ≠ v.embedding a := by
  by_contra hc
  push_neg at hc
  apply InfinitePlace.not_isReal_iff_isComplex.2 hv
  rw [InfinitePlace.isReal_iff]
  ext a
  simp only [ComplexEmbedding.conjugate_coe_eq]
  exact hc a

end GlobalTheory.Mem.R3.MetBase

namespace GlobalTheory.Mem.R3.MetBase

set_option maxHeartbeats 2000000 in

theorem metric_base_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F →
    ∀ x y, Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) (s0Of R F).XE A3.A.v0 x y := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH
  have hCx := Formalism.IndefR.Links.complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  have h2 : (R.toCx3 F).H2 F.cr false := (hCx.what₂ false).1
  have hE : R.models_HE := hP.char.base.models.HE
  have hn : 0 < RealDat.nP F.lv2 false := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  have hv0 : A3.A.v0 = InfinitePlace.mk D.what₂.embLL := R.hv0
  have hcx : ∃ a : D.what₂.LL, star (A3.A.v0.embedding a) ≠ A3.A.v0.embedding a := by
    haveI := (GlobalTheory.ptField_main D).1
    exact exists_nonreal _ (IsTotallyComplex.isComplex _)
  refine majAt_eq_of_diag _ _ _ _ _ Z.eRR0.toLinearMap hcx ?_
  intro x
  have hR := PrincipalLevelLattice.majorant_at_base_place_eq_inner (R.toCx3 F) F.cr false h2 hn x x

  set w := (R.toCx3 F).iC F.cr false A3.A.μ0 (cpt A3.A.v0.embedding x) with hw
  set z := X0.s.jEE (Z.eRR0 x) with hz
  set u : R.HE.H := Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) w with hu
  have hjE := Z.jEE0 x
  rw [← hz] at hjE
  change _ = PiTensorProduct.lift (R.HE.e u) at hjE
  have hee := Y.tied.base.ee z z
  have hnorm := X0.s.jEE_norm (Z.eRR0 x)
  have hL : Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 x) = ⟪z, z⟫_ℂ := by
    rw [majAt_self_eq, hv0, hnorm, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hK : ⟪z, z⟫_ℂ = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ⟪u, u⟫_ℂ := by
    by_cases hT : R.HE.e (u) = 0
    · have h0 : u = 0 := hE.1 (hT.trans (map_zero _).symm)
      have hz0 : Y.Iz.jE z = 0 := by
        apply Subtype.ext
        rw [hjE, hT, map_zero]
        rfl
      have hz1 : z = 0 := Y.Iz.jE.map_eq_zero_iff.1 hz0
      rw [hz1, h0]
      simp
    · obtain ⟨v, hv⟩ := GlobalTheory.KapRedII.exists_vec_of_ne hT
      rw [hee]
      show ipMT (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 false)⁻¹ • R.ν0) R.fd0 _ _ = _
      rw [hjE, ipMT, LinearEquiv.symm_apply_apply, GlobalTheory.KapRedII.ipM_smul_of_vec _ _ _ _ _ (inv_pos.2 hn) v hv, ← hE.2.2]
  change Formalism.HermitianLatticesTheory.majAt X0.s.RR.b X0.s.RR.X A3.A.v0 (Z.eRR0 x) (Z.eRR0 x) =
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((R.toCx3 F).XE F.cr false) A3.fam3.base3.v0 x x
  rw [hL, hK, hR]
  have hc : ∀ (s : Bool) (c : ℂ), starRingEnd ℂ c = c → Formalism.IndefR.Links.cj s c = c := by
    intro s c h
    cases s <;> simp [Formalism.IndefR.Links.cj, h]
  change _ = _ * Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) ⟪u, u⟫_ℂ
  rw [hc _ _ (inner_conj_symm u u)]
  rfl

end GlobalTheory.Mem.R3.MetBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MiddleStepOneLevelProjectionEqChartProjectionStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.middleStep_oneLevel_projection_eq_chart_projection : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (h1 : 1 ≤ i) (h2 : i + 1 ≤ (I.rec7 l Z).R.m) v (c : ((I.rec7 l Z).mem u).C.cls i), (∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i (le_of_succ_m h2) c) (z' : LdG (I.rec7 l Z) i (le_of_succ_m h2) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).pr v c z' = ((F u).lv i (le_of_succ_m h2)).pr v c z) ∧ ∀ (z : Formalism.L2.Forms.Lk (F u).atT i (le_of_succ_m h2) v c) (z' : LkG (I.rec7 l Z) i (le_of_succ_m h2) (PvG (F u).atT.res v) (clsCrd (I.rec7 l Z) u i (le_of_succ_m h2) c)), z'.1 = z.1 → ((F u).lvC i h1 h2).prk v c z' = ((F u).lv i (le_of_succ_m h2)).prk v c z := by
  first | exact @GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv | exact GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv | (intros; apply GlobalTheory.Mem.Col2.HAt.pr_lvC_eq_lv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelFunctionFieldCompatibility
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ModelFn

open SmallSec

theorem ratVal_eq {Z : Scheme.{0}} [IsIntegral Z] {k : Type} [CommRing k] {q : Z ⟶ Sp k} {σ : k →+* ℂ}
    (y : CxPts q σ) (f : Z.functionField) : ratVal f y = valAt y.1 f := by
  by_cases hf : RegAt (under y) f
  · exact ratVal_eq_valAt y hf
  · rw [ratVal, valAt, dif_neg hf, dif_neg hf]

theorem valAt_comp {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (j : Y ⟶ X) [IsPreimmersion j]
    (hη : j (genericPoint Y) ⤳ genericPoint X) {K : Type} [Field K] (y : Sp K ⟶ Y) (f : X.functionField) :
    valAt (y ≫ j) f = valAt y (fnMap j hη f) := by
  by_cases hf : RegAt (j (below y)) f
  · exact (valAt_fnMap j hη y hf).symm
  · have h₁ : ¬ RegAt (below (y ≫ j)) f := hf
    rw [valAt, valAt, dif_neg h₁, dif_neg (mt (regAt_fnMap_iff j hη).1 hf)]

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y), haveI := M.ar.isIntegral; ∃ ρ : M.X.functionField ≃+* Y.Fn, (∀ (U : M.X.Opens) (hU : genericPoint M.X ∈ U) (hU' : genericPoint Y.X ∈ M.j ⁻¹ᵁ U) (s : Γ(M.X, U)), ρ (fnOf U hU s) = fnOf (M.j ⁻¹ᵁ U) hU' (M.j.app U s)) ∧ M.j (genericPoint Y.X) = genericPoint M.X ∧ (∀ (x : Y.X) (f : M.X.functionField), RegAt (M.j x) f ↔ RegAt x (ρ f)) ∧ (∀ (K : Type) [Field K] (y : Sp K ⟶ Y.X) (f : M.X.functionField), valAt (y ≫ M.j) f = valAt y (ρ f)) ∧ ∀ (σ : F →+* ℂ) (y : Pts Y σ) (y' : CxPts M.p (σ.comp (algebraMap (𝓞 F) F))), y'.1 = y.1 ≫ M.j → ∀ f : M.X.functionField, ratVal f y' = ratVal (ρ f) y := by
  intro F _ _ Y M
  have := M.ar.isIntegral
  have := isPreimmersion_j M
  have hη := j_gen_specializes M
  refine ⟨RingEquiv.ofBijective (fnMap M.j hη) ⟨(fnMap M.j hη).injective, fnMap_surjective M.j hη⟩,
    fun U hU hU' s => fnMap_fnOf M.j hη hU hU' s,
    (hη.antisymm (genericPoint_specializes _)).eq,
    fun x f => (regAt_fnMap_iff M.j hη).symm,
    fun K _ y f => valAt_comp M.j hη y f, fun σ y y' h f => ?_⟩
  rw [ratVal_eq, ratVal_eq, h]
  exact valAt_comp M.j hη y.1 f

end GlobalTheory.TrueGeo.ModelFn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelsSeed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainModels

theorem models_seed : GlobalTheory.Published.DiscreteSeriesExists → ∀ D : D7, HostHyp D → Formalism.IndefR.Seed.ModY D ∧
    ∀ (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL], (∀ x : D.host.E, ∃ y : Ks, algebraMap Ks D.what₂.LL y = D.embE x) →
      ∃ MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ),
        Formalism.IndefR.Seed.ModWAt D.what₂.embLL MW ∧ GlobalTheory.RealGeo.FrameKs Ks MW := by
  intro h D _
  exact exists_models h D

end GlobalTheory.ChainModels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonodromyFreeSumIrreducibles
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp
  GlobalTheory.LocLanglands Module

namespace GlobalTheory.WeilDeligne.IrrDecomp

theorem isIrreducible_of_equiv {G V V' : Type} [Monoid G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (e : V ≃ₗ[ℂ] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (hρ : ρ.IsIrreducible) :
    ρ'.IsIrreducible := by
  have he' : ∀ g v, e.symm (ρ' g v) = ρ g (e.symm v) := fun g v => by
    rw [e.symm_apply_eq, he, e.apply_symm_apply]
  let F : Subrepresentation ρ ≃o Subrepresentation ρ' :=
    { toFun := fun U => ⟨U.toSubmodule.map (e : V →ₗ[ℂ] V'), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ g u, U.apply_mem_toSubmodule g hu, he g u⟩⟩
      invFun := fun U => ⟨U.toSubmodule.map (e.symm : V' →ₗ[ℂ] V), fun g v hv => by
        obtain ⟨u, hu, rfl⟩ := hv
        exact ⟨ρ' g u, U.apply_mem_toSubmodule g hu, he' g u⟩⟩
      left_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      right_inv := fun U => by
        apply Subrepresentation.toSubmodule_injective
        ext v
        simp [Submodule.mem_map_equiv]
      map_rel_iff' := by
        intro U U'
        show U.toSubmodule.map (e : V →ₗ[ℂ] V') ≤ U'.toSubmodule.map (e : V →ₗ[ℂ] V') ↔
          U.toSubmodule ≤ U'.toSubmodule
        exact Submodule.map_le_map_iff_of_injective e.injective _ _ }
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  exact F.symm.isSimpleOrder

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_irr_list (n : ℕ) : ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (a : WDRep h V), finrank ℂ V = n → a.N = 0 →
    ∃ L : List (WD h), (∀ z ∈ L, IsIrrWD z) ∧ WD.mk a = sumList L := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ a hn hN
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · refine ⟨[], by simp, ?_⟩
    show WD.mk a = WD.mk (WDRep.diag h (ι := Fin 0) fun i => i.elim0)
    exact WD.sound ⟨LinearEquiv.ofFinrankEq _ _ (by simp [hn]), fun _ _ => Subsingleton.elim _ _,
      fun _ => Subsingleton.elim _ _⟩
  · haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (hn ▸ hpos)
    have hP : ∃ d, ∃ Q : Submodule ℂ V, (∀ σ, ∀ v ∈ Q, a.ρ σ v ∈ Q) ∧ Q ≠ ⊥ ∧ finrank ℂ Q = d :=
      ⟨_, ⊤, fun _ _ _ => trivial, top_ne_bot, rfl⟩
    obtain ⟨Q, hQs, hQ0, hQd⟩ := Nat.find_spec hP
    have hmin : ∀ Q' : Submodule ℂ V, (∀ σ, ∀ v ∈ Q', a.ρ σ v ∈ Q') → Q' ≠ ⊥ →
        finrank ℂ Q ≤ finrank ℂ Q' := fun Q' hs hne => hQd ▸ Nat.find_min' hP ⟨Q', hs, hne, rfl⟩
    have hirr : (restrictρ a Q hQs).ρ.IsIrreducible := by
      haveI : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ0
      refine { exists_pair_ne := ⟨⊥, ⊤, fun hbt => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
      · exact bot_ne_top (α := Submodule ℂ Q) (congrArg Subrepresentation.toSubmodule hbt)
      · by_cases hU : U.toSubmodule = ⊥
        · exact Or.inl (Subrepresentation.toSubmodule_injective hU)
        · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
          show U.toSubmodule = ⊤
          have hs : ∀ σ, ∀ v ∈ U.toSubmodule.map Q.subtype, a.ρ σ v ∈ U.toSubmodule.map Q.subtype := by
            rintro σ _ ⟨u, hu, rfl⟩
            exact ⟨_, U.apply_mem_toSubmodule σ hu, rfl⟩
          have hr : finrank ℂ (U.toSubmodule.map Q.subtype) = finrank ℂ U.toSubmodule :=
            Submodule.finrank_map_subtype_eq Q U.toSubmodule
          have hpos' : 0 < finrank ℂ U.toSubmodule :=
            Nat.pos_of_ne_zero fun h0 => hU (Submodule.finrank_eq_zero.mp h0)
          have hne : U.toSubmodule.map Q.subtype ≠ ⊥ := fun h0 => by
            rw [h0, finrank_bot] at hr; omega
          have h1 := hmin _ hs hne
          have h2 := Submodule.finrank_le U.toSubmodule
          exact Submodule.eq_top_of_finrank_eq (by omega)
    obtain ⟨T, hQT, hTs⟩ := GlobalTheory.WeilDeligne.PrimDecomp.exists_stable_isCompl E Ω A w h V a Q hQs
    have hiso : ((restrictρ a Q hQs).sum (restrictρ a T hTs)).Iso a := by
      refine ⟨Submodule.prodEquivOfIsCompl Q T hQT, fun σ v => ?_, fun v => ?_⟩
      · simp [map_add]
      · simp [hN]
    have hdim := Submodule.finrank_add_eq_of_isCompl hQT
    have hQpos : 0 < finrank ℂ Q := Nat.pos_of_ne_zero fun h0 => hQ0 (Submodule.finrank_eq_zero.mp h0)
    obtain ⟨L, hL, hT⟩ := ih (finrank ℂ T) (by omega) T (restrictρ a T hTs) rfl rfl
    refine ⟨WD.mk (restrictρ a Q hQs) :: L, ?_, ?_⟩
    · refine List.forall_mem_cons.mpr ⟨?_, hL⟩
      obtain ⟨e, he, -⟩ := WD.iso_std (restrictρ a Q hQs)
      exact ⟨_, (WD.std (restrictρ a Q hQs)).2, (WD.sound (WD.iso_std _)).symm,
        isIrreducible_of_equiv e he hirr⟩
    · rw [show sumList (WD.mk (restrictρ a Q hQs) :: L) =
        WD.lpSum (WD.mk (restrictρ a Q hQs)) (sumList L) from rfl, ← hT, WD.lpSum_mk]
      exact (WD.sound hiso).symm

end GlobalTheory.WeilDeligne.IrrDecomp
end
end

