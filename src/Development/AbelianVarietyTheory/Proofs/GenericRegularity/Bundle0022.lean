import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0007
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0062
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0010
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsCuspFormOfIntegralOverDominantWeight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory

open IntegralCusp in

theorem cusp_of_integral_of_dom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), AllTest Xo c → ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (w : Fin N → Rul Xo c), Dom a n → (∀ i, w i ∈ Formalism.L2.PjFree.cusp Xo c U a n) → ∀ (k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) c.F), 0 < k → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → ∀ g ∈ sec Xo c (k • a) (k * n), g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.aeval w (cf i)) * g ^ i = 0 → g ∈ Formalism.L2.PjFree.cusp Xo c U (k • a) (k * n) := by
  intro E _ _ _ H Dw l Xo c hT r U hU a n N w hD hw k m cf hk hcf g hg heq
  unfold Formalism.L2.PjFree.cusp
  refine ⟨hg, ?_⟩
  simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap]
  intro σ hσ
  unfold Formalism.L2.PjFree.holSub
  refine Submodule.subset_span ?_
  show Formalism.L2.PjFree.IsHolCusp _ _ _
  unfold Formalism.L2.PjFree.IsHolCusp
  intro j
  have hDk : Dom (k • a) (k * n) := by
    unfold Dom at hD ⊢
    refine ⟨fun τ i i' hii' => ?_, hD.2.mul_left k⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Nat.mul_le_mul_left k (hD.1 τ hii')
  have hla : Formalism.L2.PjFree.laU (U σ) (k • a) (k * n) j = k • Formalism.L2.PjFree.laU (U σ) a n j := by
    funext τ i
    rw [laU_nsmul (U σ) a n k hD.2 j τ i]
    simp [Pi.smul_apply]
  have hsec := (hU σ hσ).2.2.2.2.1 (k • a) (k * n) hDk g hg j
  rw [hla] at hsec ⊢
  have hwS : ∀ s, Formalism.L2.PjFree.rdU (U σ) (w s) j ∈ ((U σ).X j).SS (Formalism.L2.PjFree.laU (U σ) a n j) := by
    intro s
    have h1 := hw s
    unfold Formalism.L2.PjFree.cusp at h1
    have h2 := h1.2
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Submodule.mem_comap] at h2
    exact GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub (U σ).X (Formalism.L2.PjFree.laU (U σ) a n) (h2 σ hσ) j
  refine cuspForm_of_integral_over_cuspForms E r ((U σ).X j) (Formalism.L2.PjFree.laU (U σ) a n j) N k m
    (fun s => Formalism.L2.PjFree.rdU (U σ) (w s) j) (fun i => MvPolynomial.map σ (cf i))
    (Formalism.L2.PjFree.rdU (U σ) g j) hwS hk (fun i hi => (hcf i hi).map σ) hsec ?_
  intro x hx
  have : _root_.IsReduced (CAt σ) := inferInstanceAs (_root_.IsReduced ℂ)
  have hy := hT (CAt σ) ((U σ).un j ⟨x, hx⟩)
  have key : ∀ f, Formalism.L2.PjFree.rdU (U σ) f j x = evHom ((U σ).un j ⟨x, hx⟩) hy f := by
    intro f
    unfold Formalism.L2.PjFree.rdU
    simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos hx]
    rfl
  simp only [key]
  have h3 := congrArg (evHom ((U σ).un j ⟨x, hx⟩) hy) heq
  simpa only [map_add, map_mul, map_sum, map_pow, map_zero, evHom_aeval] using h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsTriangularReframeExistsAndUnique
section
noncomputable section

namespace GlobalTheory.Reg.ReframeEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FrameTangent

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S]

def toM {x : Sp S ⟶ Xo.X} {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    TanM x Xo.univ.t.G :=
  mkT (ovT (t := Xo.univ.t) hv) (smT_zero_ovT (t := Xo.univ.t) hv)

theorem comb_iff {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsCombAt x v cf w ↔ (tv (∑ i, cf i • toM (hv i))).left = w := by
  have e := isCombAtG_iff Xo.univ.t x (fun j => ovT (t := Xo.univ.t) (hv j)) cf w
  refine e.trans ?_
  rw [tv_comb]
  rfl

theorem comb_unique {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) {cf : Fin m → S} {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt x v cf w) (h' : IsCombAt x v cf w') : w = w' :=
  ((comb_iff hv cf w).1 h).symm.trans ((comb_iff hv cf w').1 h')

theorem comb_single {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) (i : Fin m) : IsCombAt x v (Pi.single i 1) (v i) := by
  rw [comb_iff hv]
  have : ∑ j, (Pi.single i (1 : S) : Fin m → S) j • toM (hv j) = toM (hv i) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  rw [this]
  rfl

theorem comb_exists [Algebra c.F S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (τ : E →+* ℂ)
    (hv : ∀ j, IsTanAt x (v j)) (he : ∀ j, IsEigAt c τ (v j)) (cf : Fin m → S) :
    ∃ w, IsCombAt x v cf w ∧ IsTanAt x w ∧ IsEigAt c τ w := by
  refine ⟨_, (comb_iff hv cf _).2 rfl, isTanAtG_of (t := Xo.univ.t) _ (tv_zero' _), ?_⟩
  refine (isEigAt_iff τ (tv (∑ i, cf i • toM (hv i)))).2 fun a => ?_
  have hU : ∀ i, actL (x0 := x) Xo.univ.t.act a (toM (hv i)) = algebraMap c.F S (embK c τ a) • toM (hv i) :=
    fun i => tv_injective ((isEigAt_iff τ (ovT (t := Xo.univ.t) (hv i))).1 (he i) a)
  have : actL (x0 := x) Xo.univ.t.act a (∑ i, cf i • toM (hv i)) =
      algebraMap c.F S (embK c τ a) • ∑ i, cf i • toM (hv i) := by
    rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hU, smul_comm]
  exact congrArg tv this

theorem exists_reframe [Algebra c.F S] (y : FrPt Xo c S)
    (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (hg : ∀ τ, IsUnit (g τ).det) :
    ∃ y', Reframe g y y' := by
  choose u hu ht he using fun τ i => comb_exists τ (y.tan τ) (y.eig τ) (fun j => g τ j i)
  refine ⟨⟨y.x, y.x_over, u, ht, he, fun τ w hw hw' => ?_, y.s, y.gen⟩, rfl, hu⟩
  obtain ⟨a, ha, hua⟩ := y.basis τ w hw hw'
  have key : ∀ b w', IsCombAt y.x (u τ) b w' → IsCombAt y.x (y.u τ) ((g τ).mulVec b) w' := fun b w' h =>
    GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x (y.u τ) (y.tan τ) (u τ) (g τ) b w' (hu τ) h
  refine ⟨(g τ)⁻¹.mulVec a, ?_, fun b hb => ?_⟩
  · obtain ⟨w', h1, -, -⟩ := comb_exists τ (ht τ) (he τ) ((g τ)⁻¹.mulVec a)
    have h2 := key _ _ h1
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hg τ), Matrix.one_mulVec] at h2
    show IsCombAt y.x (u τ) ((g τ)⁻¹.mulVec a) w
    rw [comb_unique (y.tan τ) ha h2]
    exact h1
  · rw [← hua _ (key b w hb), Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hg τ), Matrix.one_mulVec]

theorem existsUnique_reframe [Algebra c.F S] (y y' : FrPt Xo c S) (hx : y'.x = y.x) :
    ∃! g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S,
      (∀ τ, IsUnit (g τ).det) ∧ Reframe g y y' := by
  have ht' : ∀ τ i, IsTanAt y.x (y'.u τ i) := fun τ i => hx ▸ y'.tan τ i
  have hb' : ∀ τ w, IsTanAt y.x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt y.x (y'.u τ) a w := by
    rw [← hx]; exact y'.basis
  choose a ha hua using fun τ i => y.basis τ (y'.u τ i) (ht' τ i) (y'.eig τ i)
  choose b hb _ using fun τ i => hb' τ (y.u τ i) (y.tan τ i) (y.eig τ i)
  refine ⟨fun τ => Matrix.of fun j i => a τ i j, ⟨fun τ => ?_, hx, ha⟩, fun g hg => ?_⟩
  · have hm : (Matrix.of fun j i => a τ i j) * (Matrix.of fun j i => b τ i j) = 1 := by
      ext j i
      have h1 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S y.x (y.u τ) (y.tan τ) (y'.u τ)
        (Matrix.of fun j i => a τ i j) (b τ i) (y.u τ i) (ha τ) (hb τ i)
      have h2 := (y.basis τ (y.u τ i) (y.tan τ i) (y.eig τ i)).unique h1 (comb_single (y.tan τ) i)
      have h3 := congrFun h2 j
      rw [Pi.single_apply] at h3
      rw [Matrix.one_apply, ← h3]
      rfl
    exact Matrix.isUnit_det_of_right_inverse hm
  · funext τ
    ext j i
    exact congrFun (hua τ i _ (hg.2.2 τ i)) j

theorem reframe_exists_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), (∀ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, IsUnit (g τ).det) → ∃ y', Reframe g y y') ∧ ∀ y' : FrPt Xo c S, y'.x = y.x → ∃! g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ, IsUnit (g τ).det) ∧ Reframe g y y' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ y => ⟨exists_reframe y, existsUnique_reframe y⟩

end GlobalTheory.Reg.ReframeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NormWcharEqNormBchar
section
open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory.WeightLie

open ReciprocityTheory.ChartRestriction.G GlobalTheory.FrameNormLie

theorem norm_diag_eq_norm_diag {n α : Type} [Fintype n] [DecidableEq n] [Fintype α] {t : n → α} {w : n → ℕ}
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j') {A B : Matrix n n ℂ} (hA : Supp t w A) (hB : Supp t w B)
    (hB0 : ∀ j, B j j ≠ 0) (d : n → ℂ) (hd : ∀ j, d j ≠ 0)
    (h : Aᵀ * (Matrix.diagonal d * A.map (starRingEnd ℂ)) = Bᵀ * (Matrix.diagonal d * B.map (starRingEnd ℂ)))
    (a : n) : ‖A a a‖ = ‖B a a‖ := by
  have hu : IsUnit B.det := by
    rw [PerBor.det_of_support t w hinj B hB, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => hB0 j
  have hi : Supp t w B⁻¹ := PerBor.inv_support t w B hu hB
  have h1 := norm_diag_eq_one hinj (hA.mul hi) d hd (by
    have e : B.map (starRingEnd ℂ) * B⁻¹.map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu]; simp
    have e' : B⁻¹ᵀ * Bᵀ = 1 := by
      rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.transpose_one]
    calc _ = B⁻¹ᵀ * (Aᵀ * (Matrix.diagonal d * A.map (starRingEnd ℂ))) * B⁻¹.map (starRingEnd ℂ) := by
          rw [Matrix.transpose_mul, Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = (B⁻¹ᵀ * Bᵀ) * Matrix.diagonal d * (B.map (starRingEnd ℂ) * B⁻¹.map (starRingEnd ℂ)) := by
          rw [h]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [e, e', Matrix.one_mul, Matrix.mul_one]) a
  rw [Supp.mul_diag hinj hA hi, PerBor.inv_diag t w hinj B hu hB, norm_mul, norm_inv] at h1
  exact (mul_inv_eq_one₀ (norm_ne_zero_iff.2 (hB0 a))).1 h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ}

theorem moveMat_diag_ne {Ψ : Finset (E →+* ℂ)} (q : ℕ) (idx : Fin g ≃ Ψ × Fin r) {b : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) (j : Fin g) : PerBor.moveMat q idx b j j ≠ 0 := by
  rw [PerBor.moveMat_diag _ idx hb]
  split_ifs
  · exact PerMove.bor_diag_ne hb _ _
  · exact inv_ne_zero (PerMove.bor_diag_ne hb _ _)

theorem exists_tri_pair {α : Type} [Fintype α] (X : Data E r) (idx : Fin g ≃ X.Ψ × Fin r) {t : Fin g → α}
    {w : Fin g → ℕ} (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (hs : ∀ b ∈ Bor X.Ψ r, Supp t w (PerBor.moveMat X.p0 idx b)) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    ∃ T T' : Matrix (Fin g) (Fin g) ℂ, Supp t w T ∧ Supp t w T' ∧ (∀ j, T j j ≠ 0) ∧
      (∀ j, T' j j = T j j * (PerBor.moveMat X.p0 idx b j j)⁻¹) ∧
      (∀ v v', (hermForm (Matrix.diagonal (diagXi X idx)) (T *ᵥ perVec X idx x v) (T *ᵥ perVec X idx x v')).im =
        ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v v') : ℚ) : ℝ)) ∧
      ∀ v v', (hermForm (Matrix.diagonal (diagXi X idx)) (T' *ᵥ perVec X idx (rmul (lact γ x) b) v)
        (T' *ᵥ perVec X idx (rmul (lact γ x) b) v')).im =
        ((Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v v') : ℚ) : ℝ) := by
  obtain ⟨x₀, b₀, hb₀, hgr, rfl⟩ :=
    (UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  have hd : IsUnit (PerBor.moveMat X.p0 idx b).det := by
    rw [PerBor.det_of_support t w hinj _ (hs b hb), isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun j _ => moveMat_diag_ne _ idx hb j
  have hm : ∀ b ∈ Bor X.Ψ r, ∀ y v, PerBor.moveMat X.p0 idx b *ᵥ perVec X idx y v = perVec X idx (rmul y b) v :=
    fun b hb y v => (PerBor.moveMat_mulVec X.p0 idx hb X.Gm y v (perVec X idx y v) (perVec X idx (rmul y b) v)
      (fun _ => rfl) (fun _ => rfl)).symm
  have hi : Supp t w (PerBor.moveMat X.p0 idx b)⁻¹ := PerBor.inv_support t w _ hd (hs b hb)
  have he : rmul (lact γ x) b₀ = lact γ (rmul x b₀) := funext fun τ =>
    Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b₀ τ)
  have h2 : ∀ v, (PerBor.moveMat X.p0 idx b₀ * (PerBor.moveMat X.p0 idx b)⁻¹) *ᵥ
      perVec X idx (rmul (lact γ x) b) v = perVec X idx (lact γ (rmul x b₀)) v := fun v => by
    rw [← hm b hb, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_right _ _ hd, hm b₀ hb₀, he]
  refine ⟨PerBor.moveMat X.p0 idx b₀, PerBor.moveMat X.p0 idx b₀ * (PerBor.moveMat X.p0 idx b)⁻¹, hs b₀ hb₀,
    (hs b₀ hb₀).mul hi, moveMat_diag_ne _ idx hb₀, fun j => ?_, fun v v' => ?_, fun v v' => ?_⟩
  · rw [Supp.mul_diag hinj (hs b₀ hb₀) hi, PerBor.inv_diag t w hinj _ hd (hs b hb)]
  · rw [hm b₀ hb₀, hm b₀ hb₀, im_diag_ortho X idx _ hgr]
  · rw [h2, h2, im_diag_ortho X idx _ fun τ => (AR.Up.PairUnfoldPf.gram_lact X hγ _ τ).trans (hgr τ)]

end GlobalTheory.WeightLie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.PinNum

theorem goodAt_of_two_primes {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (l : Level H) {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b)
    (hM : l.M = a * b) (p : ℕ) : l.GoodAt p := by
  have hodd := l.odd
  rw [hM, Nat.odd_mul] at hodd
  have ha3 : 3 ≤ a := by
    have := ha.two_le
    obtain ⟨k, hk⟩ := hodd.1
    omega
  have hb3 : 3 ≤ b := by
    have := hb.two_le
    obtain ⟨k, hk⟩ := hodd.2
    omega
  unfold Level.GoodAt
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  by_cases hp : p.Prime
  swap
  · simpa [Nat.factorization_eq_zero_of_not_prime _ hp] using l.three_le
  have key : ∀ c, 3 ≤ c → c ∣ l.M → ¬ p ∣ c → 3 ≤ l.M / p ^ l.M.factorization p := fun c hc hd hn =>
    hc.trans (Nat.le_of_dvd (Nat.ordCompl_pos p hM0) (Nat.dvd_ordCompl_of_dvd_not_dvd hd hn))
  by_cases h : p ∣ a
  · refine key b hb3 (hM ▸ dvd_mul_left _ _) fun h' => hp.one_lt.ne' ?_
    exact Nat.eq_one_of_dvd_coprimes ((Nat.coprime_primes ha hb).2 hab) h h'
  · exact key a ha3 (hM ▸ dvd_mul_right _ _) h

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have h : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    push_cast
    ring
  exact_mod_cast h

theorem xiR_pos_le_one (D : D7) (Q : Par D) (h : Q.PinHost) : 0 < xiR D ∧ xiR D ≤ 1 := by
  obtain ⟨-, -, h3, -⟩ := h
  have hsq := Q.H.sqrt_neg_disc_sq
  rw [h3] at hsq
  have hd : (1 : ℝ) ≤ Q.H.d := by exact_mod_cast Q.H.d_prime.one_le
  have hn : ‖D.host.φ₀ D.host.sqrtMinusD‖ ^ 2 = Q.H.d := by
    rw [← norm_pow, hsq, norm_neg, Complex.norm_natCast]
  have h1 : 1 ≤ ‖D.host.φ₀ D.host.sqrtMinusD‖ := by
    by_contra hc
    push Not at hc
    nlinarith [norm_nonneg (D.host.φ₀ D.host.sqrtMinusD)]
  have hN : (1 : ℝ) ≤ (Ideal.absNorm D.host.ccK : ℝ) := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hx : xiR D = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * ‖D.host.φ₀ D.host.sqrtMinusD‖) := by
    unfold xiR Formalism.BasicNotions.Host.xi0
    rw [map_div₀, map_mul, map_natCast, map_neg, map_one, norm_div, norm_neg, norm_one, norm_mul,
      Complex.norm_natCast]
  have h2 : (1 : ℝ) ≤ (Ideal.absNorm D.host.ccK : ℝ) * ‖D.host.φ₀ D.host.sqrtMinusD‖ :=
    one_le_mul_of_one_le_of_one_le hN h1
  rw [hx]
  exact ⟨by positivity, (div_le_one (by positivity)).2 h2⟩

theorem numerics_of_pins : ∀ (D : D7) (Q : Par D), Q.Pins → (∀ p : ℕ, p.Prime → Q.l.GoodAt p) ∧ Q.l.A = 1 ∧ Q.l.M' = Q.l.M ∧ 0 < xiR D ∧ xiR D ≤ 1 ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ ∀ j, InR D j → (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ 1 ≤ D.R.r ∧ (Q.Dw j).dim + Nat.card (FlagVar (Q.Dw j)) = WeightFamilies.dimY D j := by
  intro D Q ⟨hH, ⟨hM, hA⟩, _, hD⟩
  have hx := xiR_pos_le_one D Q hH
  refine ⟨fun p _ => goodAt_of_two_primes Q.l (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hM p, hA, ?_,
    hx.1, hx.2, finrank_host D, fun j hj => ?_⟩
  · rw [Level.M', hA, Nat.lcm_one_right]
  · obtain ⟨hp, hq, -⟩ := hD j hj
    have hk := D.R.m_add_three_le_k
    obtain ⟨hj1, hj2⟩ := hj
    refine ⟨?_, ?_, ?_⟩
    · rw [hp, hq]
      simp only [Ranks.sigW, Ranks.r]
      omega
    · unfold Ranks.r
      omega
    · rw [GlobalTheory.FlagDim.dim_add_card_flagVar, finrank_host, Nat.mul_div_cancel_left _ two_pos, hp, hq]
      rfl

end GlobalTheory.PinNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.TieIntegral
section
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem tie_integral : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), PushInvertible Y.t.G Y.t.PP.L → ∀ (T : CDVR) (io : c.F →+* T.Fr) (f₀ : Γ(Y.X, M.U) →+* T.V) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin M.n) (u₀ : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) T.V), (∀ τ, InCell (ix τ) (u₀ τ)) → letI := io.toAlgebra; ∀ z : FrPt Xo c T.Fr, M.Comparison₂ ((algebraMap T.V T.Fr).comp f₀) (fun τ => (u₀ τ).map (algebraMap T.V T.Fr)) z → Integral T io z := by
  intro hS E _ _ _ H Dw l Xo c O _ β Y M hP T io f₀ ix u₀ hu
  letI := io.toAlgebra
  intro z ⟨Λ, hL, hT⟩
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap f₀ ≫ M.hU.fromSpec) Y.t
  have e : spMap ((algebraMap T.V T.Fr).comp f₀) ≫ M.hU.fromSpec =
      spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec := by
    rw [← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  have key : ∀ (g : Sp T.Fr ⟶ Y.X) (n : SABMap Λ.t' Y.t g),
      g = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ M.hU.fromSpec →
      ∃ m2 : SABMap Λ.t' _ (spMap (algebraMap T.V T.Fr)), m2.φ ≫ m.φ = n.φ := by
    intro g n hg
    subst hg
    obtain ⟨m2, h⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n
    exact ⟨m2, h.symm⟩
  obtain ⟨m2, h2⟩ := key _ Λ.m2 e
  exact ⟨_, Λ.t', Λ.m1, m2,
    GlobalTheory.T.framedPoint_vectors_integral_in_cell E H Dw l Xo c O β Y M T io f₀ ix u₀ hu z Λ hL _ m m2 h2,
    GlobalTheory.T.exists_integralGenerator_of_chartPoint_cdvr hS E H Dw l Xo c O β Y M hP T io f₀ z.x z.s Λ hT _ m m2 h2⟩

end GlobalTheory.Reg
end
end

