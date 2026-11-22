import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0663
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0806
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0805
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0814
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0655
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0648
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0667
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0733
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0677
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0647
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0652
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0659
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRxSymm
section
noncomputable section

open scoped NNReal Matrix TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.StdChart

section Gen

variable {R : Type} [CommRing R] {n : ℕ}

def rx : GL (Fin (n + n)) R ≃* GL (Fin n ⊕ Fin n) R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R (finSumFinEquiv (m := n) (n := n)).symm).toMulEquiv

theorem rx_val (g : GL (Fin (n + n)) R) : (rx g).1 = g.1.submatrix finSumFinEquiv finSumFinEquiv := rfl

theorem rx_inv_val (g : GL (Fin (n + n)) R) :
    ((rx g)⁻¹ : GL (Fin n ⊕ Fin n) R).1 = (g⁻¹ : GL (Fin (n + n)) R).1.submatrix finSumFinEquiv finSumFinEquiv := by
  rw [← map_inv]; rfl

theorem continuous_rx [TopologicalSpace R] : Continuous (rx : GL (Fin (n + n)) R → GL (Fin n ⊕ Fin n) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_submatrix _ _)
  · have : (fun g : GL (Fin (n + n)) R => (((rx g)⁻¹ : GL (Fin n ⊕ Fin n) R) : Matrix _ _ R)) =
        fun g => (g⁻¹ : GL (Fin (n + n)) R).1.submatrix finSumFinEquiv finSumFinEquiv := funext rx_inv_val
    rw [this]
    exact (Units.continuous_coe_inv.matrix_submatrix _ _)

theorem continuous_rx_symm [TopologicalSpace R] :
    Continuous (rx.symm : GL (Fin n ⊕ Fin n) R → GL (Fin (n + n)) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_submatrix _ _)
  · have : (fun g : GL (Fin n ⊕ Fin n) R => (((rx.symm g)⁻¹ : GL (Fin (n + n)) R) : Matrix _ _ R)) =
        fun g => (g⁻¹ : GL (Fin n ⊕ Fin n) R).1.submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact (Units.continuous_coe_inv.matrix_submatrix _ _)

theorem form_iff {ι : Type} [Fintype ι] (c : R →+* R) (hc : ∀ x, c (c x) = x) {J : Matrix ι ι R} (hJ : J.map c = J)
    (g : Matrix ι ι R) : Formalism.UG.cT c g * J * g = J ↔ gᵀ * J * g.map c = J := by
  have key : (Formalism.UG.cT c g * J * g).map c = gᵀ * J * g.map c := by
    rw [Matrix.map_mul, Matrix.map_mul, hJ]
    congr 2
    ext i j
    simp [Formalism.UG.cT, hc]
  constructor
  · intro h
    rw [← key, h, hJ]
  · intro h
    have h2 := congrArg (fun M => M.map c) h
    simp only [Matrix.map_mul, hJ] at h2
    have e : (gᵀ).map c = Formalism.UG.cT c g := by ext i j; simp [Formalism.UG.cT]
    have e2 : (g.map c).map c = g := by ext i j; simp [hc]
    rwa [e, e2] at h2

theorem keeps_iff_int {ι : Type} [Fintype ι] [DecidableEq ι] (O : Subring R) (m : GL ι R) :
    (∀ y : ι → R, (∀ i, y i ∈ O) ↔ ∀ i, (m.1 *ᵥ y) i ∈ O) ↔
      ∀ r c, m.1 r c ∈ O ∧ (m⁻¹ : GL ι R).1 r c ∈ O := by
  constructor
  · intro h r c
    have hs : ∀ i, (Pi.single c (1 : R) : ι → R) i ∈ O := fun i => by
      by_cases e : i = c
      · subst e; simp [O.one_mem]
      · simp [e, O.zero_mem]
    refine ⟨by simpa using (h _).1 hs r, ?_⟩
    have h2 := (h (((m⁻¹ : GL ι R).1) *ᵥ Pi.single c 1)).2 (by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hs) r
    simpa using h2
  · intro h y
    have key : ∀ (M : Matrix ι ι R), (∀ r c, M r c ∈ O) → ∀ y : ι → R, (∀ i, y i ∈ O) → ∀ i, (M *ᵥ y) i ∈ O :=
      fun M hM y hy i => O.sum_mem fun j _ => O.mul_mem (hM i j) (hy j)
    refine ⟨key _ (fun r c => (h r c).1) y, fun hy => ?_⟩
    have := key _ (fun r c => (h r c).2) _ hy
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

end Gen

section Sub

variable {R : Type} {n : ℕ}

theorem sub_inj {X Y : Matrix (Fin (n + n)) (Fin (n + n)) R} :
    X.submatrix finSumFinEquiv finSumFinEquiv = Y.submatrix finSumFinEquiv finSumFinEquiv ↔ X = Y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext i j
  have := congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)
  simpa using this

end Sub

section Std

variable (D : D7) {n : ℕ}

theorem sig_sig (x : D.host.E) : D.sp.cm.sig (D.sp.cm.sig x) = x := by
  have h := isCMExt_host D
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ]
  simp

theorem sigR_sigR (z : AE D) : sigR (AF D.host.F) D.sp.cm.sig (sigR (AF D.host.F) D.sp.cm.sig z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    change a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig e) = _
    rw [sig_sig]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigR_inclR (x : D.host.E) :
    sigR (AF D.host.F) D.sp.cm.sig (inclR (AF D.host.F) x) = inclR (AF D.host.F) (D.sp.cm.sig x) := rfl

theorem Jst_map : (GlobalTheory.StdUnn.Jst D n).map D.sp.cm.sig = GlobalTheory.StdUnn.Jst D n := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.StdUnn.Jst, GlobalTheory.StdUnn.blk4, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;>
    simp [Matrix.one_apply] <;> split_ifs <;> simp

theorem JR_map : (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).map (sigR (AF D.host.F) D.sp.cm.sig) =
    JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n) := by
  ext i j
  simp only [Matrix.map_apply, JR, sigR_inclR]
  rw [← Matrix.map_apply (f := D.sp.cm.sig), Jst_map]

theorem J_eq : (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).submatrix finSumFinEquiv finSumFinEquiv =
    Ad.J (AE D) (-1) (Fin n) := by
  have key : ∀ x y, (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).submatrix finSumFinEquiv finSumFinEquiv x y =
      inclR (F := D.host.F) (E := D.host.E) (AF D.host.F) ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) D.host.E) x y) := fun x y => by
    simp only [JR, GlobalTheory.StdUnn.Jst, GlobalTheory.StdUnn.blk4, Matrix.submatrix_apply, Matrix.map_apply, Equiv.symm_apply_apply]
  ext x y
  rw [key]
  rcases x with a | a <;> rcases y with b | b <;> simp [Ad.J, Matrix.one_apply, apply_ite (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))]

variable (χ : (AE D)ˣ →* Circle)

theorem mem_uSub_iff (g : GL (Fin (n + n)) (AE D)) :
    rx g ∈ (adCM D.sp.cm.sig χ).uSub (-1) (Fin n) ↔ g ∈ HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) := by
  change (rx g).1ᵀ * Ad.J (AE D) (-1) (Fin n) * (rx g).1.map (sigR (AF D.host.F) D.sp.cm.sig) = Ad.J (AE D) (-1) (Fin n) ↔
    Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) g.1 * JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n) * g.1 = JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)
  rw [form_iff _ (sigR_sigR D) (JR_map D), ← J_eq, rx_val, ← sub_inj (X := _ * _ * _)]
  have : (g.1ᵀ * JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n) * g.1.map (sigR (AF D.host.F) D.sp.cm.sig)).submatrix finSumFinEquiv finSumFinEquiv =
      (g.1.submatrix finSumFinEquiv finSumFinEquiv)ᵀ * (JR (AF D.host.F) (GlobalTheory.StdUnn.Jst D n)).submatrix finSumFinEquiv finSumFinEquiv *
        (g.1.submatrix finSumFinEquiv finSumFinEquiv).map (sigR (AF D.host.F) D.sp.cm.sig) := by
    rw [← Matrix.submatrix_mul_equiv _ _ finSumFinEquiv finSumFinEquiv finSumFinEquiv,
      ← Matrix.submatrix_mul_equiv _ _ finSumFinEquiv finSumFinEquiv finSumFinEquiv]
    rfl
  rw [this]

def toU (g : GlobalTheory.StdUnn.G D n) : UD D χ n :=
  ⟨rx (matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) g), (mem_uSub_iff D χ _).2 (Subtype.prop (p := (· ∈ HR _ _ _)) g)⟩

theorem toU_val (g : GlobalTheory.StdUnn.G D n) : (toU D χ g).1 = rx (matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) g) := rfl

def ofU (u : UD D χ n) : GlobalTheory.StdUnn.G D n :=
  (⟨rx.symm u.1, (mem_uSub_iff D χ _).1 (by simpa using u.2)⟩ : HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n))

theorem ofU_val (u : UD D χ n) : matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) (ofU D χ u) = rx.symm u.1 := rfl

def Psi (n : ℕ) : GlobalTheory.StdUnn.G D n ≃ₜ* UD D χ n where
  toFun := toU D χ
  invFun := ofU D χ
  left_inv g := matHom_injective _ _ _ (by rw [ofU_val, toU_val]; exact rx.symm_apply_apply _)
  right_inv u := Subtype.ext (by rw [toU_val, ofU_val]; exact rx.apply_symm_apply _)
  map_mul' g h := Subtype.ext (by rw [Subgroup.coe_mul, toU_val, toU_val, toU_val, map_mul, map_mul])
  continuous_toFun := (continuous_rx.comp (isEmbedding_matHom _ _ _).continuous).subtype_mk _
  continuous_invFun := (isEmbedding_matHom _ _ _).continuous_iff.2 (continuous_rx_symm.comp continuous_subtype_val)

theorem Psi_val (g : GlobalTheory.StdUnn.G D n) : (Psi D χ n g).1 = rx (matHom _ D.sp.cm.sig (GlobalTheory.StdUnn.Jst D n) g) := rfl

end Std

end GlobalTheory.CompanionTheory.StdChart

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DivisibilityStatement
section
noncomputable section

open scoped Topology
open Filter Set Metric GlobalTheory.Cont

namespace GlobalTheory.CompanionTheory.DivMult

theorem exists_factor {A : ℂ → ℂ} (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (s₀ : ℂ) :
    ∃ (k : ℕ) (u : ℂ → ℂ) (r M : ℝ), 0 < r ∧ DifferentiableOn ℂ u (ball s₀ r) ∧ (∀ s ∈ ball s₀ r, u s ≠ 0) ∧
      (∀ s ∈ ball s₀ r, A s = (s - s₀) ^ k * u s) ∧ ∀ s ∈ ball s₀ r, ‖(u s)⁻¹‖ ≤ M := by
  have hAn : AnalyticOnNhd ℂ A univ := fun z _ => hA.analyticAt z
  have hnz : ¬∀ᶠ z in 𝓝 s₀, A z = 0 := by
    intro hev
    obtain ⟨w, hw⟩ := hne
    have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s₀)
      (hev.mono fun z hz => by simp [hz])
    exact hw (by simpa using this (mem_univ w))
  obtain ⟨k, g, hg, hg0, hev⟩ := (hA.analyticAt s₀).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnz
  have hpos : 0 < ‖g s₀‖ := norm_pos_iff.mpr hg0
  have hcont : ∀ᶠ z in 𝓝 s₀, ‖g z - g s₀‖ < ‖g s₀‖ / 2 := by
    have h2 : ball (g s₀) (‖g s₀‖ / 2) ∈ 𝓝 (g s₀) := ball_mem_nhds _ (by positivity)
    filter_upwards [hg.continuousAt h2] with z hz
    simpa [dist_eq_norm] using hz
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp (hev.and (hcont.and hg.eventually_analyticAt))
  refine ⟨k, g, r, 2 / ‖g s₀‖, hr, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hball z hz).2.2.differentiableAt.differentiableWithinAt
  · intro z hz h0
    have h1 := (hball z hz).2.1
    rw [h0, zero_sub, norm_neg] at h1
    linarith
  · intro z hz
    simpa [smul_eq_mul] using (hball z hz).1
  · intro z hz
    have h1 := (hball z hz).2.1
    have hlow : ‖g s₀‖ / 2 ≤ ‖g z‖ := by
      have h3 := norm_sub_norm_le (g s₀) (g z)
      rw [norm_sub_rev] at h3
      linarith
    calc ‖(g z)⁻¹‖ = ‖g z‖⁻¹ := norm_inv _
      _ ≤ (‖g s₀‖ / 2)⁻¹ := inv_anti₀ (by positivity) hlow
      _ = 2 / ‖g s₀‖ := inv_div _ _

def glue (h F A : ℂ → ℂ) (R : ℝ) (z : ℂ) : ℂ := if R < z.re then h z else F z / A z

variable {h F A : ℂ → ℂ} {R : ℝ}

theorem glue_eq (he : ∀ z : ℂ, R < z.re → F z = A z * h z) {z : ℂ} (hz : A z ≠ 0) : glue h F A R z = F z / A z := by
  unfold glue
  split_ifs with c
  · rw [he z c, mul_div_cancel_left₀ _ hz]
  · rfl

theorem glue_eventuallyEq (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (he : ∀ z : ℂ, R < z.re → F z = A z * h z) (s : ℂ) :
    glue h F A R =ᶠ[𝓝[≠] s] fun z => F z / A z := by
  have hAn : AnalyticOnNhd ℂ A univ := fun z _ => hA.analyticAt z
  rcases (hA.analyticAt s).eventually_eq_zero_or_eventually_ne_zero with hev | hev
  · exfalso
    obtain ⟨w, hw⟩ := hne
    have := hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s)
      (hev.mono fun z hz => by simp [hz])
    exact hw (by simpa using this (mem_univ w))
  · filter_upwards [hev] with z hz using glue_eq he hz

theorem isMerExt_glue (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (hF : Differentiable ℂ F)
    (he : ∀ z : ℂ, R < z.re → F z = A z * h z) : IsMerExt h univ (glue h F A R) := by
  refine ⟨isRightDomain_univ, fun s _ => ?_, ⟨R, fun z hz => ?_⟩⟩
  · have hm : MeromorphicAt (fun z => F z / A z) s :=
      (hF.analyticAt s).meromorphicAt.div (hA.analyticAt s).meromorphicAt
    exact hm.congr (glue_eventuallyEq hA hne he s).symm
  · have hz' : R < z.re := hz
    simp [glue, hz']

theorem cont_eq_div (hA : Differentiable ℂ A) (hne : ∃ z, A z ≠ 0) (hF : Differentiable ℂ F)
    (he : ∀ z : ℂ, R < z.re → F z = A z * h z) {s : ℂ} (hs : A s ≠ 0) : cont h s = F s / A s := by
  have hM := isMerExt_glue hA hne hF he
  have hE : IsExtAt h s (glue h F A R) := hM.isExtAt (mem_univ s)
  have hcont : ContinuousAt (fun z => F z / A z) s :=
    hF.continuous.continuousAt.div hA.continuous.continuousAt hs
  have ht : Tendsto (glue h F A R) (𝓝[≠] s) (𝓝 (F s / A s)) :=
    Tendsto.congr' (glue_eventuallyEq hA hne he s).symm (hcont.tendsto.mono_left nhdsWithin_le_nhds)
  exact (hE.holValueAt_iff.mpr ht).valueAt.cont_eq

theorem div_multiplier : ResidueKilled.Tr.Div := by
  unfold ResidueKilled.Tr.Div
  intro D T e H A R hA hne hH hHc hmul hbd
  unfold GlobalTheory.EisCont.ContMod GlobalTheory.Cont.Continues
  refine ⟨fun g => ⟨_, isMerExt_glue hA hne (hH g) (fun z hz => hmul z hz g)⟩, fun s₀ => ?_⟩
  obtain ⟨k, u, r, M, hr, hu, hu0, hfac, hM⟩ := exists_factor hA hne s₀
  obtain ⟨C, N, hCN⟩ := hbd (‖s₀‖ + r)
  have hu1 : ContinuousOn (fun x : ℂ × _ => u x.1) (ball s₀ r ×ˢ (univ : Set (Formalism.L2.Theta.GA D T))) :=
    hu.continuousOn.comp continuous_fst.continuousOn (fun x hx => hx.1)
  unfold GlobalTheory.EisCont.RegAt
  refine ⟨k, r, fun s g => H s g * (u s)⁻¹, hr, ?_, ?_, ?_, C * M, N, ?_⟩
  · intro s hs hss g
    have hAs : A s = (s - s₀) ^ k * u s := hfac s hs
    have hus : u s ≠ 0 := hu0 s hs
    have hpow : (s - s₀) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hss)
    have hA0 : A s ≠ 0 := by rw [hAs]; exact mul_ne_zero hpow hus
    show H s g * (u s)⁻¹ = (s - s₀) ^ k * cont (fun z => e z g) s
    rw [cont_eq_div hA hne (hH g) (fun z hz => hmul z hz g) hA0, hAs]
    field_simp
    try ring
  · intro g
    exact (hH g).differentiableOn.mul (hu.inv hu0)
  · exact hHc.continuousOn.mul (hu1.inv₀ (fun x hx => hu0 x.1 hx.1))
  · intro s hs g
    have hs1 : ‖s - s₀‖ < r := by simpa [dist_eq_norm] using hs
    have hs2 := norm_sub_norm_le s s₀
    have hsr : ‖s‖ ≤ ‖s₀‖ + r := by linarith
    have hH1 := hCN s hsr g
    have hM1 := hM s hs
    show ‖H s g * (u s)⁻¹‖ ≤ C * M * GlobalTheory.Grow.height T g ^ N
    calc ‖H s g * (u s)⁻¹‖ = ‖H s g‖ * ‖(u s)⁻¹‖ := norm_mul _ _
      _ ≤ (C * GlobalTheory.Grow.height T g ^ N) * M := mul_le_mul hH1 hM1 (norm_nonneg _) (le_trans (norm_nonneg _) hH1)
      _ = C * M * GlobalTheory.Grow.height T g ^ N := by ring

end GlobalTheory.CompanionTheory.DivMult

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.E45FinalGluing
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem eFinalGlue_of (hCS : ConvStrip) (hCC : ConvComp) (hFS : FactorStep) (hLL : LimLists) (hOS : OneStep)
    (hFL : FactorLim) (hMC : MCloseFacts) (hPE : PairEmb) (hPS : PairSlices) (hST : SliceType) : InfinitesimalCharacterGlue := by
  intro hE3 hSep hLim hGraft hTw hTr hLV hAD hUn hInf E _ _ _ a b W₁ W₂ hW₁ hW₂
  obtain ⟨Ωs₁, hΩs₁, S₁⟩ := hFS hSep E a W₁ hW₁
  obtain ⟨Ωs₂, hΩs₂, S₂⟩ := hFS hSep E b W₂ hW₂
  obtain ⟨Ωf₁, hΩf₁, X₁⟩ := hLL hLim hTw E a Ωs₁ hΩs₁
  obtain ⟨Ωf₂, hΩf₂, X₂⟩ := hLL hLim hTw E b Ωs₂ hΩs₂
  refine ⟨Ωf₁, Ωf₂, hΩf₁, hΩf₂, fun K₁ K₂ hK₁ hK₂ => ?_⟩
  obtain ⟨Θs₁, hΘs₁, F₁⟩ := S₁ K₁ hK₁
  obtain ⟨Θs₂, hΘs₂, F₂⟩ := S₂ K₂ hK₂
  obtain ⟨Θf₁, hΘf₁, P₁⟩ := X₁ Θs₁ hΘs₁
  obtain ⟨Θf₂, hΘf₂, P₂⟩ := X₂ Θs₂ hΘs₂
  refine ⟨Θf₁, Θf₂, hΘf₁, hΘf₂, ?_⟩
  intro D ι _ M m₁ m₂ n₁ n₂ C lam lam₀ f hC hRep hcont hne hL hWL hTy hs1 hs2 ha1 ha2 hi1 hi2 heig hconv hR1 hR2 hgap hlam
  have hfar : ∀ᶠ k in atTop, ∀ τ, MClose (1 / 8) (m₁ k τ) (n₁ τ) ∧ MClose (1 / 8) (m₂ k τ) (n₂ τ) :=
    Filter.eventually_all.2 fun τ => hconv τ (1 / 8) (by norm_num)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hfar
  have h3 := fun k => hE3 E a b D ι M (f k) K₁ K₂ W₁ W₂ (m₁ k) (m₂ k) hK₁ hK₂ hW₁ hW₂ (hcont k) (hL k) (hWL k)
    (hTy k) (hs1 k) (hs2 k) (ha1 k) (ha2 k) (hi1 k) (hi2 k)
  have hone := fun k => hOS E a b ι K₁ K₂ W₁ W₂ Θs₁ Θs₂ Ωs₁ Ωs₂ (f (k + k₀)) (m₁ (k + k₀)) (m₂ (k + k₀)) hW₁ hW₂ F₁ F₂
    (hne _) (hTy _) (hs1 _) (hs2 _) (h3 _).2.2.1 (h3 _).2.2.2.1 (h3 _).2.2.2.2.1 (h3 _).2.2.2.2.2.1
    (h3 _).2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.2.1 (h3 _).2.2.2.2.2.2.2.2.2.1
    (fun τ => hMC.2.1 (1 / 8) _ _ (by norm_num) (hk₀ (k + k₀) (by omega) τ).1 (hgap τ).1)
    (fun τ => hMC.2.1 (1 / 8) _ _ (by norm_num) (hk₀ (k + k₀) (by omega) τ).2 (hgap τ).2)
    (h3 _).2.2.2.2.2.2.2.2.2.2
  choose t₁ t₂ G ψ₁ ψ₂ hr₁ hr₂ hg₁ hg₂ hl₁ hl₂ hG0 hGm hGt hGe hp₁ hp₁0 hc₁ hp₂ hp₂0 hc₂ using hone
  have hB : ∀ n : (E →+* ℂ) → Multiset ℂ, ∃ B : ℝ, ∀ τ, ∀ y ∈ n τ, ‖y‖ ≤ B := fun n => by
    classical
    obtain ⟨B, hB⟩ := ((Finset.univ.biUnion fun τ => (n τ).toFinset).image norm).finite_toSet.bddAbove
    refine ⟨B, fun τ y hy => hB ?_⟩
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Multiset.mem_toFinset]
    exact ⟨y, ⟨τ, hy⟩, rfl⟩
  obtain ⟨B₁, hB₁⟩ := hB n₁
  obtain ⟨B₂, hB₂⟩ := hB n₂
  obtain ⟨φ₁, t₁', s₁, hφ₁, hC₁, hs₁R, hs₁G, hs₁L, hD₁, hI₁, hE₁⟩ := hFL hTr hGraft hInf E Θs₁ Θf₁ Ωs₁ Ωf₁ a t₁ ψ₁
    (fun k => m₁ (k + k₀)) n₁ (B₁ + 1 / 8) P₁ hRep hr₁ hg₁ hl₁ hp₁ hp₁0 hc₁
    (fun k τ => hMC.1 _ _ _ _ (hk₀ (k + k₀) (by omega) τ).1 (hB₁ τ))
    (fun τ ε hε => ((tendsto_add_atTop_nat k₀).eventually (hconv τ ε hε)).mono fun _ h => h.1)
  obtain ⟨φ₂, t₂', s₂, hφ₂, hC₂, hs₂R, hs₂G, hs₂L, hD₂, hI₂, hE₂⟩ := hFL hTr hGraft hInf E Θs₂ Θf₂ Ωs₂ Ωf₂ b
    (fun k => t₂ (φ₁ k)) (fun k => ψ₂ (φ₁ k))
    (fun k => m₂ (φ₁ k + k₀)) n₂ (B₂ + 1 / 8) P₂ hRep (fun k => hr₂ _) (fun k => hg₂ _) (fun k => hl₂ _)
    (fun k => hp₂ _) (fun k => hp₂0 _) (fun k => hc₂ _)
    (fun k τ => hMC.1 _ _ _ _ (hk₀ (φ₁ k + k₀) (by omega) τ).2 (hB₂ τ))
    (fun τ ε hε => (((tendsto_add_atTop_nat k₀).comp hφ₁.tendsto_atTop).eventually (hconv τ ε hε)).mono fun _ h => h.2)
  have hstab : ∀ {N : ℕ} {t : Tr E N}, t.Good → IsStable t.space := fun h => hTr E _ _ (disc_stable (good_disc h))
  have hG' := fun k => hPE E a b ι K₁ K₂ W₁ W₂ (t₁ (φ₁ (φ₂ k))).space (t₁' (φ₂ k)).space (t₂ (φ₁ (φ₂ k))).space (t₂' k).space
    (G (φ₁ (φ₂ k))) hW₁ hW₂ (hstab (hg₁ _)) (hstab (hg₂ _)) (hE₁ _) (hE₂ _) (hG0 _) (hGm _) (hGt _)
  choose G' hG'0 hG'm hG't hG'e using hG'
  have hCC₁ := (hCS E a _ _).1 (hCC E a _ _ φ₂ hC₁ hφ₂)
  have hCC₂ := (hCS E b _ _).1 hC₂
  obtain ⟨F, hF0, hFm, hFt, hFe⟩ := hLV hAD E a b ι (fun k => t₁' (φ₂ k)) t₂' s₁ s₂ K₁ K₂ W₁ W₂ C
    (fun k => lam (φ₁ (φ₂ k) + k₀)) lam₀ G' hK₁ hK₂ hW₁ hW₂ hC hs₁G hs₂G (fun k => hD₁ _) hD₂ hCC₁.1 hCC₂.1 hCC₁.2 hCC₂.2
    hG'0 hG'm hG't (fun k h hh => hG'e k h _ (hGe _ h _ (heig _ h hh)))
    (fun h hh => (hlam h hh).comp ((tendsto_add_atTop_nat k₀).comp (hφ₁.comp hφ₂).tendsto_atTop))
  obtain ⟨i, hi⟩ : ∃ i, F i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hF0 (funext hcon)
  obtain ⟨x, hx⟩ : ∃ x, F i x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hi (funext hcon)
  have hsl := hPS E a b _ _ (F i) (hFm i)
  have hn₁ : sl₁ (F i) x.2 ≠ 0 := fun h => hx (by
    have := congrFun (hsl.1 x.2).2 x.1
    rw [h] at this
    exact this.symm)
  have hn₂ : sl₂ (F i) x.1 ≠ 0 := fun h => hx (by
    have := congrFun (hsl.2 x.1).2 x.2
    rw [h] at this
    exact this.symm)
  have hb₁ : s₁.space ≠ ⊥ := fun h => hn₁ (by simpa [h] using (hsl.1 x.2).1)
  have hb₂ : s₂.space ≠ ⊥ := fun h => hn₂ (by simpa [h] using (hsl.2 x.1).1)
  exact ⟨s₁, s₂, F, hs₁G, hs₂G, hUn E a s₁ n₁ hs₁G hb₁ hI₁ hR1, hUn E b s₂ n₂ hs₂G hb₂ hI₂ hR2, hs₁L, hs₂L,
    hI₁, hI₂, hF0, hFm, hFt, hFe⟩

theorem eFinalGlue : PositivityTheory.Rg.BcB.SpectralAccumulation.InfinitesimalCharacterGlue :=
  have hPS := GlobalTheory.T.pair_slices
  have hP1 := GlobalTheory.T.pair_first_step hPS
  have hP2 := GlobalTheory.T.pair_second_step hPS
  have hCE := GlobalTheory.T.capacity_equivalence
  have hDI := GlobalTheory.T.discrete_infimum
  have hTI := GlobalTheory.T.topological_infimum
  have hIE := GlobalTheory.T.infimum_of_equality
  have hCS := GlobalTheory.T.convergence_strip
  have hCC := GlobalTheory.T.convergence_composition
  have hMC := GlobalTheory.T.closure_facts_alt
  eFinalGlue_of hCS hCC GlobalTheory.T.factor_induction (GlobalTheory.T.limit_lists hCS GlobalTheory.T.convergence_shift hCC)
    (GlobalTheory.T.single_gluing hPS GlobalTheory.T.pair_restriction GlobalTheory.T.pair_finite_dimensional GlobalTheory.T.slice_type hP1 hP2 GlobalTheory.T.hull_generation hCE)
    (GlobalTheory.T.factor_limit hCC (GlobalTheory.T.limit_trees hCC) (GlobalTheory.T.leaf_bound_alt hDI hTI hIE) (GlobalTheory.T.convergence_infimum hDI hTI) hIE hCE hMC)
    hMC (GlobalTheory.T.pair_embedding hPS hP1 hP2) hPS GlobalTheory.T.slice_type

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPullbackFirstBlock
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HtPull

open GlobalTheory.CompanionTheory.PcB (blockMatrix_multiply blockMatrix_one)
open GlobalTheory.StdUnn.Model

def leviBl {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (a : GL (Fin ρ) R) : GL (Fin n) R :=
  ⟨bl hn a.1 0 0 1, bl hn (a⁻¹).1 0 0 1,
    by rw [blockMatrix_multiply]; simp [blockMatrix_one], by rw [blockMatrix_multiply]; simp [blockMatrix_one]⟩

theorem det_leviBl {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) (a : GL (Fin ρ) R) :
    Matrix.GeneralLinearGroup.det (leviBl hn a) = Matrix.GeneralLinearGroup.det a := by
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply, leviBl, bl]
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem blockMatrix_zero {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n) :
    bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  simp only [bl, Matrix.fromBlocks_zero, Matrix.submatrix_zero, Pi.zero_apply]

theorem blkA_blk4 {R : Type} {k : ℕ} (a b c d : Matrix (Fin k) (Fin k) R) : blkA (blk4 a b c d) = a := by
  ext i j
  simp [blkA, blk4, Matrix.toBlocks₁₁]

theorem isHt_blockPull : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (ι : G D ρ →* G D n), Continuous ι →
  (∀ (h : G D ρ) (a b c d : Mx D ρ ρ), mat h = blk4 a b c d →
    mat (ι h) = blk4 (bl hn a 0 0 1) (bl hn b 0 0 0) (bl hn c 0 0 0) (bl hn d 0 0 1)) →
  ∀ H : G D n → ℝ≥0, IsHt H → IsHt (fun h : G D ρ => H (ι h)) := by
  intro D n ρ p hn ι hc hblk H hH
  refine ⟨hH.1.comp hc, fun g => hH.2.1 _, ?_⟩
  intro q hq a ha g
  obtain ⟨b, d, hm⟩ := GlobalTheory.StdUnn.LeftInvSect.siegelParabolicUnn_matrix_blockUpperTriangular hq
  rw [ha] at hm
  have hι := hblk q a.1 b 0 d hm
  rw [blockMatrix_zero] at hι
  have hqP : ι q ∈ P D n := GlobalTheory.CompanionTheory.SwUnf.SmallCell.mem_siegelParabolic_of_lowerLeft_entries_eq_zero hι
  have hA : blkA (mat (ι q)) = (leviBl hn a).1 := by
    rw [hι, blkA_blk4]
    rfl
  show H (ι (q * g)) = _ * H (ι g)
  rw [map_mul, hH.2.2 _ hqP (leviBl hn a) hA, det_leviBl]

end GlobalTheory.CompanionTheory.HtPull

end
end

