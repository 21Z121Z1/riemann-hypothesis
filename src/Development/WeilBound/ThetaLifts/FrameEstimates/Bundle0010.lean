import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0006
import Development.WeilBound.ThetaLifts.FrameEstimates.LinDerA
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0008
import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0003
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConst

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LinDer
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace LinDerPf

section Cx

variable {ι : Type} [Fintype ι] {d : ℕ}

def adj (J : ι → Matrix (Fin d) (Fin d) ℂ) : (ι → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] (ι → Matrix (Fin d) (Fin d) ℂ) where
  toFun x w := ((J w)⁻¹ * (x w)ᵀ * J w).map star
  map_add' x y := by
    funext w
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, Pi.add_apply, Matrix.map_apply, Matrix.add_apply,
      star_add]
  map_smul' r x := by
    funext w
    ext i j
    simp only [Matrix.transpose_smul, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.map_apply,
      Matrix.smul_apply, star_smul, RingHom.id_apply, star_trivial]

omit [Fintype ι] in
theorem adj_iff {J : ι → Matrix (Fin d) (Fin d) ℂ} (hJ : ∀ w, IsUnit (J w).det) (Y : ι → Matrix (Fin d) (Fin d) ℂ) :
    adj J Y = -Y ↔ ∀ w, (Y w)ᵀ * J w + J w * (Y w).map star = 0 := by
  rw [funext_iff]
  refine forall_congr' fun w => ?_
  change ((J w)⁻¹ * (Y w)ᵀ * J w).map star = -Y w ↔ _
  have e : ((J w)⁻¹ * (Y w)ᵀ * J w).map star = -Y w ↔ (J w)⁻¹ * (Y w)ᵀ * J w = -(Y w).map star := by
    simp only [← Matrix.ext_iff, Matrix.map_apply, Matrix.neg_apply]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [star_eq_iff_star_eq, star_neg, eq_comm]
  rw [e, add_eq_zero_iff_eq_neg, ← Matrix.mul_neg]
  constructor
  · intro h
    rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hJ w)]
  · intro h
    rw [Matrix.mul_assoc, h, Matrix.nonsing_inv_mul_cancel_left _ _ (hJ w)]

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
theorem mainM {J : ι → Matrix (Fin d) (Fin d) ℂ} (hJ : ∀ w, IsUnit (J w).det) :
    ∃ (m : ℕ) (Y : Fin m → ι → Matrix (Fin d) (Fin d) ℂ) (c : Fin m → (ι → Matrix (Fin d) (Fin d) ℂ) →ₗ[ℝ] ℝ),
      (∀ i w, (Y i w)ᵀ * J w + J w * (Y i w).map star = 0) ∧ ∀ Z Z' : ι → Matrix (Fin d) (Fin d) ℂ,
      (∀ w, (Z' w)ᵀ * J w + J w * (Z' w).map star = 0) →
      (∀ w (t : ℝ), NormedSpace.exp ((t : ℂ) • Z w) = NormedSpace.exp ((t : ℂ) • Z' w)) →
      ∃ s : Fin m → ℝ → ℝ, (∀ i, s i 0 = 0) ∧ (∀ i, HasDerivAt (s i) (c i Z) 0) ∧
        ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ w, NormedSpace.exp ((t : ℂ) • Z w) =
          (List.ofFn fun i => NormedSpace.exp ((s i t : ℂ) • Y i w)).prod := by
  let a : (ι → Matrix (Fin d) (Fin d) ℂ) →L[ℝ] (ι → Matrix (Fin d) (Fin d) ℂ) := LinearMap.toContinuousLinearMap (adj J)
  have ha : ∀ x y, a (x * y) = a y * a x := fun x y => by
    funext w
    change ((J w)⁻¹ * (x w * y w)ᵀ * J w).map (starRingEnd ℂ) =
      ((J w)⁻¹ * (y w)ᵀ * J w).map (starRingEnd ℂ) * ((J w)⁻¹ * (x w)ᵀ * J w).map (starRingEnd ℂ)
    rw [← Matrix.map_mul, Matrix.transpose_mul]
    congr 1
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hJ w)]
  have h1 : a 1 = 1 := by
    funext w
    change ((J w)⁻¹ * (1 : Matrix (Fin d) (Fin d) ℂ)ᵀ * J w).map (starRingEnd ℂ) = 1
    rw [Matrix.transpose_one, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hJ w), Matrix.map_one _ (map_zero _) (map_one _)]
  have hx : ∀ (t : ℝ) (x : ι → Matrix (Fin d) (Fin d) ℂ) w,
      NormedSpace.exp (t • x) w = NormedSpace.exp ((t : ℂ) • x w) := fun t x w => by
    rw [Pi.coe_exp, Pi.smul_apply, Complex.coe_smul]
  obtain ⟨m, Y, c, hY, h⟩ := main (a := a) ha h1
  refine ⟨m, Y, c, fun i => (adj_iff hJ _).1 (hY i), fun Z Z' hZ e => ?_⟩
  obtain ⟨s, s0, sd, se⟩ := h Z fun t => by
    have e' : NormedSpace.exp (t • Z) = NormedSpace.exp (t • Z') := funext fun w => by rw [hx, hx, e]
    rw [e']
    refine gr_exp ha h1 ?_
    rw [map_smul, ← smul_neg]
    exact congrArg _ ((adj_iff hJ _).2 hZ)
  refine ⟨s, s0, sd, se.mono fun t ht w => ?_⟩
  rw [← hx, ht, Pi.list_prod_apply, List.map_ofFn]
  congr 2
  funext i
  exact hx _ _ _

end Cx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}

omit [NumberField E] in
theorem uat_prod {W : Spc F E d} (l : List (UA σ W.J)) (hl : ∀ g ∈ l, g ∈ UAt σ W (evI F)) :
    l.prod ∈ UAt σ W (evI F) := by
  induction l with
  | nil =>
    intro c _
    change c • ((1 : Matrix (Fin d) (Fin d) (AE F E)) - 1) = 0
    rw [sub_self, smul_zero]
  | cons x l ih =>
    intro c hc
    have h1 := hl x (by simp) c hc
    have h2 := ih (fun g hg => hl g (by simp [hg])) c hc
    rw [List.prod_cons]
    change c • (mat x * mat l.prod - 1) = 0
    have e : mat x * mat l.prod - 1 = mat x * (mat l.prod - 1) + (mat x - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one, sub_add_sub_cancel]
    rw [e, smul_add, ← Matrix.mul_smul, h1, h2, Matrix.mul_zero, add_zero]

omit [NumberField E] in
theorem mat_prod {J : Matrix (Fin d) (Fin d) E} (p : AE F E →+* ℂ) (l : List (UA σ J)) :
    (mat l.prod).map p = (l.map fun g => (mat g).map p).prod := by
  induction l with
  | nil => exact Matrix.map_one _ (map_zero _) (map_one _)
  | cons x l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih, ← Matrix.map_mul]
    rfl

theorem uat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {W : Spc F E d} {u v : UA σ W.J}
    (hu : u ∈ UAt σ W (evI F)) (hv : v ∈ UAt σ W (evI F))
    (e : ∀ w, (mat u).map (piInf (τ w)) = (mat v).map (piInf (τ w))) : u = v := by
  refine Subtype.ext (Units.ext ?_)
  change mat u = mat v
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_)
  · have e1 : c • (mat u - mat v) = 0 := by
      rw [← sub_sub_sub_cancel_right _ _ 1, smul_sub, hu c hc, hv c hc, sub_zero]
    exact congrFun (congrFun e1 i) j
  · rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (e w) i) j)

end LinDerPf

open LinDerPf in
theorem linDer_of (hG : LineGen) (hX : LineEx) : LinDer := by
  intro F E _ _ _ _ _ σ h τ d W hW
  have hJ : ∀ w, IsUnit (W.J.map (τ w).1).det := fun w => by
    have e : (W.J.map (τ w).1).det = (τ w).1 W.J.det := (RingHom.map_det (τ w).1 W.J).symm
    rw [e]
    exact ((map_ne_zero (τ w).1).2 hW.2).isUnit
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (GL (Fin d) (AE F E)) := inferInstance
  have : IsTopologicalGroup (UA σ W.J) := inferInstance
  obtain ⟨m, Y, c, hY, hm⟩ := mainM hJ
  choose β hβ hβY _ using fun i => hX F E σ h τ d W hW (Y i) (hY i)
  refine ⟨m, β, c, hβ, fun f f' hf γ hγ Z hZ g => ?_⟩
  obtain ⟨Z', hZ', hZZ⟩ := hG F E σ h τ d W hW γ hγ
  obtain ⟨s, s0, sd, se⟩ := hm Z Z' hZ' fun w t => (hZ w t).symm.trans (hZZ w t)
  have h1 := chain f m β (fun i => (hβ i).1) f' (fun i => (hf i).1) (fun i => (hf i).2) (fun _ => g)
    continuousAt_const s (fun i => c i Z) sd s0 0 (hasDerivAt_const _ _)
  rw [zero_add] at h1
  refine h1.congr_of_eventuallyEq (se.mono fun t ht => ?_)
  have e : γ (Multiplicative.ofAdd t) = (List.ofFn fun i => β i (Multiplicative.ofAdd (s i t))).prod := by
    refine uat_ext h τ (hγ.2 _) (uat_prod _ fun x hx => ?_) fun w => ?_
    · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact (hβ i).2 _
    · rw [hZ w t, ht w, mat_prod, List.map_ofFn]
      congr 2
      funext i
      exact (hβY i w _).symm
  simp only [e]

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LineEx
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ExponentialLineExistence

open GlobalTheory.CompanionTheory.CMAdele

section Cx

variable {d : ℕ}

theorem exp_line_add (Y : Matrix (Fin d) (Fin d) ℂ) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • Y) = NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y) := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _), Complex.ofReal_add, add_smul]

theorem exp_map_star (A : Matrix (Fin d) (Fin d) ℂ) :
    (NormedSpace.exp A).map star = NormedSpace.exp (A.map star) := by
  have e : ∀ B : Matrix (Fin d) (Fin d) ℂ, B.map star = Bᴴᵀ := fun B => rfl
  rw [e, e, Matrix.exp_transpose, Matrix.exp_conjTranspose]

set_option backward.isDefEq.respectTransparency false in
theorem exp_semiconj {J A B : Matrix (Fin d) (Fin d) ℂ} (h : SemiconjBy J A B) :
    NormedSpace.exp (-B) * J * NormedSpace.exp A = J :=
  open scoped Matrix.Norms.Operator in h.exp_neg_mul_mul_exp_eq_self

set_option backward.isDefEq.respectTransparency false in
theorem continuous_exp_mat : Continuous (NormedSpace.exp : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) :=
  open scoped Matrix.Norms.Operator in NormedSpace.exp_continuous

theorem exp_unitary {J Y : Matrix (Fin d) (Fin d) ℂ} (h : Yᵀ * J + J * Y.map star = 0) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Y))ᵀ * J * (NormedSpace.exp ((t : ℂ) • Y)).map star = J := by
  have h1 : SemiconjBy J (((t : ℂ) • Y).map star) (-((t : ℂ) • Y)ᵀ) := by
    have e : ((t : ℂ) • Y).map star = (t : ℂ) • Y.map star := by
      ext i j
      simp
    rw [SemiconjBy, e, Matrix.transpose_smul, Matrix.mul_smul, neg_mul, Matrix.smul_mul, ← smul_neg,
      eq_neg_of_add_eq_zero_right h]
  have h2 := exp_semiconj h1
  rwa [neg_neg, Matrix.exp_transpose, ← exp_map_star] at h2

end Cx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | add x y hx hy => simp only [map_add, hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul, piInf_tmul, h.2.2.2, star_mul', show star (InfinitePlace.Completion.extensionEmbedding w (a.1 w)) = _ from
      Complex.conj_eq_iff_im.2 (im_extension h.1 w _)]

theorem map_incM {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (piInf_tmul τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

theorem continuous_realAd : Continuous (realAd F) := by
  refine Continuous.prodMk (f := fun t => (realAd F t).1) (g := fun _ => (0 : Af F)) ?_ continuous_const
  refine continuous_pi fun w => ?_
  refine (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.isInducing.continuous_iff.2 ?_
  have e : (InfinitePlace.Completion.extensionEmbedding w) ∘ (fun t => (realAd F t).1 w) = fun t : ℝ => (t : ℂ) :=
    funext fun t => GlobalTheory.CompanionTheory.RealAdeleComponent.extensionEmbedding_evInf_realAd w t
  exact e ▸ Complex.continuous_ofReal

theorem exists_section (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ s : (InfinitePlace F → ℂ) → AE F E, Continuous s ∧ (∀ z, At (evI F) (s z)) ∧ ∀ z w, piInf (τ w) (s z) = z w := by
  classical
  choose x hx hx' using fun w : InfinitePlace F =>
    GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ (Pi.single w 1)
  choose y hy hy' using fun w : InfinitePlace F =>
    GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ (Pi.single w Complex.I)
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine ⟨fun z => ∑ w, (realAd F (z w).re • x w + realAd F (z w).im • y w), ?_, fun z c hc => ?_, fun z w => ?_⟩
  · have hr : ∀ (a : AE F E) (f : (InfinitePlace F → ℂ) → ℝ), Continuous f → Continuous fun z => realAd F (f z) • a :=
      fun a f hf => ((continuous_realAd (F := F)).comp hf).smul (continuous_const (y := a))
    refine continuous_finsetSum _ fun w _ => Continuous.add (hr _ _ ?_) (hr _ _ ?_)
    · exact Complex.continuous_re.comp (continuous_apply (A := fun _ => ℂ) w)
    · exact Complex.continuous_im.comp (continuous_apply (A := fun _ => ℂ) w)
  · rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [smul_add, smul_comm c, smul_comm c, hx w c hc, hy w c hc, smul_zero, smul_zero, add_zero]
  · rw [map_sum, Finset.sum_eq_single w]
    · rw [map_add, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, hx', hy',
        Pi.single_eq_same, Pi.single_eq_same, mul_one, Complex.re_add_im]
    · intro v _ hv
      rw [map_add, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, hx', hy',
        Pi.single_eq_of_ne hv.symm, Pi.single_eq_of_ne hv.symm, mul_zero, mul_zero, add_zero]
    · simp

variable {d : ℕ}

theorem mat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {u v : Matrix (Fin d) (Fin d) (AE F E)}
    (hf : ∀ c : AF F, evI F c = 0 → c • u = c • v) (e : ∀ w, u.map (piInf (τ w)) = v.map (piInf (τ w))) : u = v := by
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_)
  · rw [smul_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (hf c hc) i) j)
  · rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (e w) i) j)

omit [NumberField E] in
theorem at_iff {u : Matrix (Fin d) (Fin d) (AE F E)} :
    At (evI F) (u - 1) ↔ ∀ c : AF F, evI F c = 0 → c • u = c • (1 : Matrix (Fin d) (Fin d) (AE F E)) :=
  forall_congr' fun c => forall_congr' fun _ => by rw [smul_sub, sub_eq_zero]

theorem exists_matSection (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) :
    ∃ S : (InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) → Matrix (Fin d) (Fin d) (AE F E), Continuous S ∧
      (∀ z (c : AF F), evI F c = 0 → c • S z = c • (1 : Matrix (Fin d) (Fin d) (AE F E))) ∧
      ∀ z w, (S z).map (piInf (τ w)) = z w := by
  obtain ⟨s, hs, hA, hp⟩ := exists_section h τ
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine ⟨fun z => Matrix.of fun i j => (1 : Matrix (Fin d) (Fin d) (AE F E)) i j +
    s fun w => z w i j - (1 : Matrix (Fin d) (Fin d) ℂ) i j, ?_, fun z c hc => ?_, fun z w => ?_⟩
  · refine continuous_matrix fun i j => continuous_const.add (hs.comp (continuous_pi fun w => ?_))
    exact ((continuous_apply w).matrix_elem i j).sub continuous_const
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply]
    rw [smul_add, hA _ c hc, add_zero]
  · ext i j
    have e := congrFun (congrFun (Matrix.map_one (n := Fin d) (piInf (τ w)) (map_zero _) (map_one _)) i) j
    rw [Matrix.map_apply] at e
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [map_add, hp, e, add_sub_cancel]

end ExponentialLineExistence

open ExponentialLineExistence in
theorem lineEx_of : LineEx := by
  intro F E _ _ _ _ _ σ h τ d W _ Y hY
  obtain ⟨S, hS, hf, hp⟩ := exists_matSection h τ d
  let g : ℝ → Matrix (Fin d) (Fin d) (AE F E) := fun t => S fun w => NormedSpace.exp ((t : ℂ) • Y w)
  have gp : ∀ t w, (g t).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y w) := fun t w => hp _ w
  have gf : ∀ t (c : AF F), evI F c = 0 → c • g t = c • (1 : Matrix (Fin d) (Fin d) (AE F E)) := fun t => hf _
  have gc : Continuous g := hS.comp (continuous_pi fun w =>
    continuous_exp_mat.comp (Complex.continuous_ofReal.smul continuous_const))
  have g0 : g 0 = 1 := mat_ext h τ (gf 0) fun w => by
    rw [gp, Matrix.map_one _ (map_zero _) (map_one _), Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
  have ga : ∀ s t, g (s + t) = g s * g t := fun s t => mat_ext h τ
    (fun c hc => by rw [gf _ c hc, ← Matrix.smul_mul, gf _ c hc, Matrix.smul_mul, Matrix.one_mul, gf _ c hc])
    fun w => by rw [Matrix.map_mul, gp, gp, gp, exp_line_add]
  have gu : ∀ t, (g t)ᵀ * incM F W.J * (g t).map (cA σ) = incM F W.J := fun t => mat_ext h τ
    (fun c hc => by
      have e : ∀ u : Matrix (Fin d) (Fin d) (AE F E), c • u.map (cA σ) = (c • u).map (cA σ) := fun u => by
        ext i j
        simp only [Matrix.smul_apply, Matrix.map_apply, map_smul]
      rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, gf _ c hc, Matrix.transpose_smul,
        Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← Matrix.mul_smul, e, gf _ c hc, ← e,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_smul, Matrix.mul_one])
    fun w => by
      have e : ((g t).map (cA σ)).map (piInf (τ w)) = ((g t).map (piInf (τ w))).map star := by
        ext i j
        exact piInf_cA h _ _
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_incM, e, gp]
      exact exp_unitary (hY w) t
  let G : ℝ → GL (Fin d) (AE F E) := fun t =>
    ⟨g t, g (-t), by rw [← ga, add_neg_cancel, g0], by rw [← ga, neg_add_cancel, g0]⟩
  let γ : Multiplicative ℝ →* UA σ W.J :=
    { toFun := fun t => ⟨G t.toAdd, gu _⟩
      map_one' := Subtype.ext (Units.ext g0)
      map_mul' := fun s t => Subtype.ext (Units.ext (ga _ _)) }
  refine ⟨γ, ⟨?_, fun t => at_iff.2 (gf _)⟩, fun w t => gp t w, fun γ' hγ' hG => ?_⟩
  · refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact gc.comp continuous_toAdd
    · exact (gc.comp continuous_neg).comp continuous_toAdd
  · refine MonoidHom.ext fun t => Subtype.ext (Units.ext ?_)
    refine mat_ext h τ (u := mat (γ' t)) (v := g t.toAdd) (fun c hc => ?_) fun w => ?_
    · rw [at_iff.1 (hγ'.2 t) c hc, gf _ c hc]
    · rw [gp]
      exact hG w t.toAdd

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.SigRapid
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section

variable {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
  {r s r' s' : ℕ}

theorem exists_soFin (hF : SoFin) (hp : IsPair B M χX χW om r s r' s') {m : ℕ} (φ : Fin m → (Fin n × Fin d → Af F) → ℂ)
    (hφ : ∀ j, φ j ∈ SB _) : ∃ ψ : Fin m → (Fin n × Fin d → Af F) → ℂ, (∀ j, ψ j ∈ soFin B M) ∧
      ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ →
        ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (ψ j) := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (soCoeff (B := B) M φ)
  let P := Submodule.linearProjOfIsCompl _ _ hQ
  let ψ : Fin m → (Fin n × Fin d → Af F) → ℂ := fun j => ∑ i, (P (Pi.single j 1) : Fin m → ℂ) i • φ i
  have hψ : ∀ j, ψ j ∈ soFin B M := fun j =>
    ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hφ i), (P (Pi.single j 1)).2⟩
  have key : ∀ w : Fin m → SInf F (Fin n × Fin d), ∑ j, pureA F (w j) (φ j) ∈ M.So B.ψ B.τ₁ →
      ∑ j, pureA F (w j) (φ j) = ∑ j, pureA F (w j) (ψ j) := fun w hw => by
    obtain ⟨m', f', χ, hχ, e⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).1 _ hw
    have hmem : ∀ x, (fun j => w j x) ∈ soCoeff (B := B) M φ := fun x f₀ => by
      have e2 : ∑ j, w j x • φ j = ∑ i, f' i x • χ i := by
        funext y
        obtain ⟨z, hz1, hz2⟩ : ∃ z : Fin n × Fin d → AdeleRing (𝓞 F) F,
            (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = x ∧ (fun i => (z i).2) = y :=
          ⟨fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i),
            funext fun i => RingEquiv.apply_symm_apply _ _, rfl⟩
        have := congrFun e z
        simp only [Finset.sum_apply, pureA, hz1, hz2] at this
        simpa [Finset.sum_apply] using this
      have e3 : pureA F f₀ (∑ i, f' i x • χ i) = ∑ i, f' i x • pureA F f₀ (χ i) := by
        funext z; simp [pureA, Finset.mul_sum, Finset.sum_apply]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [e2, e3]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ((hχ i).2 f₀)
    funext z
    set x : Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1
    have e4 : (fun j => w j x) = ∑ j, w j x • (P (Pi.single j 1) : Fin m → ℂ) := by
      have a1 : (P (fun j => w j x) : Fin m → ℂ) = fun j => w j x :=
        congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hQ ⟨_, hmem x⟩)
      have a2 : (fun j => w j x) = ∑ j, w j x • (Pi.single j 1 : Fin m → ℂ) := by
        funext i; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [← a1, a2]
      simp
    have e5 : ∀ i, w i x = ∑ j, w j x * (P (Pi.single j 1) : Fin m → ℂ) i := fun i => by
      simpa [Finset.sum_apply] using congrFun e4 i
    simp only [Finset.sum_apply, pureA, ψ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show w i (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1) = _ from e5 i, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
  exact ⟨ψ, hψ, key⟩

theorem polData_sum (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ PolData B M) :
    ∃ (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ),
      (∀ i, f i ∈ M.Pol B.ψ B.emb) ∧ (∀ i, φ i ∈ SB _) ∧ Φ = ∑ i, pureA F (f i) (φ i) := by
  obtain ⟨m, c, x, rfl⟩ := Submodule.mem_span_set'.1 hΦ
  choose f hf χ h1 h2 h3 using fun i => (x i).2
  refine ⟨m, fun i => c i • f i, fun i => FiniteAdelicSupportCompactness.pf (χ i), fun i => Submodule.smul_mem _ _ (hf i),
    fun i => FiniteAdelicSupportCompactness.pf_mem ⟨h1 i, ((h2 i).and hp.good.std).mono fun v hv => hv.1.trans hv.2⟩,
    Finset.sum_congr rfl fun i _ => ?_⟩
  rw [h3 i, FiniteAdelicSupportCompactness.pure_eq]
  funext z
  simp [pureA, mul_assoc]

variable (B W) in

def Nice (f : UA σ W.J → ℂ) : Prop := LeftInv f ∧ UMG W f ∧ SmoothFin W B.emb f

theorem nice_zero : Nice B W (0 : UA σ W.J → ℂ) :=
  ⟨fun _ _ _ => rfl, ⟨0, {0}, rfl, by
    rintro _ rfl
    exact ⟨continuous_const, ⟨0, fun h => by simp⟩, fun γ _ => ⟨0, rfl, fun h => hasDerivAt_const _ _⟩⟩⟩,
    Set.univ, univ_mem, fun _ _ _ _ => rfl⟩

theorem Nice.lin (hU : UMGLin) (hc : IsCMExt F E σ) (hJ : EpsHerm σ W.J) {f f' : UA σ W.J → ℂ} (h : Nice B W f)
    (h' : Nice B W f') (a b : ℂ) : Nice B W (a • f + b • f') := by
  refine ⟨fun γ hγ x => ?_, hU F E σ hc B.emb d W hJ f f' h.2.1 h'.2.1 a b, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, h.1 γ hγ x, h'.1 γ hγ x]
  · obtain ⟨U, hU1, hu⟩ := h.2.2
    obtain ⟨U', hU1', hu'⟩ := h'.2.2
    refine ⟨U ∩ U', inter_mem hU1 hU1', fun u hm h1 x => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, hu u hm.1 h1 x, hu' u hm.2 h1 x]

theorem nice_sum (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hp : IsPair B M χX χW om r s r' s')
    {𝓕} (hD : Dom M om 𝓕) {m : ℕ} (f : Fin m → SInf F (Fin n × Fin d)) (φ : Fin m → (Fin n × Fin d → Af F) → ℂ)
    (hf : ∀ i, f i ∈ M.Pol B.ψ B.emb) (hφ : ∀ i, φ i ∈ 𝓕) (hsb : ∀ i, φ i ∈ SB _) :
    Nice B W (M.I om (∑ i, pureA F (f i) (φ i))) := by
  obtain ⟨hJ, -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  have e : M.I om (∑ i, pureA F (f i) (φ i)) = ∑ i, M.I om (pureA F (f i) (φ i)) :=
    funext fun h => ((dom_sum hB hp hD f φ hφ hsb).2.2 h).trans (Finset.sum_apply _ _ _).symm
  rw [e]
  refine Finset.sum_induction _ _ (fun a b ha hb => by simpa using ha.lin hU hp.base.cm hJ hb 1 1) nice_zero fun i _ => ?_
  exact ⟨(hI F E σ B n d X W M χX χW om r s r' s' hp _ (pureA_mem _ (hsb i))).1,
    hG F E σ B n d X W M χX χW om r s r' s' hp 𝓕 hD _ (hφ i) (hsb i) _ (hf i)⟩

end

theorem sig_nice (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hT : TriplePair) (hW : DomWeil)
    (hS : DomSoU) (hF : SoFin) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W}
    {om' : Rep σ G.V' G.W} (ht' : IsTriple B G X om om') {f : UA σ G.W.J → ℂ} (hf : f ∈ PositivityTheory.ThKEnd.Sig B G om om') :
    Nice B G.W f := by
  obtain ⟨h1, h2, h3⟩ := hT F E σ B a a' G X om om' ht'
  obtain ⟨Φ, hΦ, Φ', hΦ', rfl⟩ := hf
  obtain ⟨hJ, -, -⟩ := hE F E σ B h1.base _ G.W _ _ (Or.inr h1.skew)
  obtain ⟨m, f, φ, c1, c2, rfl⟩ := polData_sum h1 hΦ
  obtain ⟨m', f', φ', c1', c2', rfl⟩ := polData_sum h2 hΦ'.1
  obtain ⟨ψ, hψ, hk⟩ := exists_soFin hF h2 φ' c2'
  rw [hk f' hΦ'.2]
  have n1 := nice_sum hB hU hE hG hI h1 (hW F E σ B _ _ _ _ _ _ _ om _ _ _ _ h1 (Or.inl h3)) f φ c1 c2 c2
  have n2 := nice_sum hB hU hE hG hI h2 (dom_of_domSoU hS h2) f' ψ c1' hψ fun i => (hψ i).1
  simpa [sub_eq_add_neg] using n1.lin hU h1.base.cm hJ n2 1 (-1)

theorem sigRapid_of (hB : ThetaBasic) (hU : UMGLin) (hE : EpsOf) (hG : IUMG) (hI : IInv) (hT : TriplePair) (hW : DomWeil)
    (hS : DomSoU) (hF : SoFin) (hC : CuspRapid) : PositivityTheory.ThKEnd.Orth.SigRapid := by
  intro F E _ _ _ _ _ σ B a a' G X om om' ht' f hf hc
  obtain ⟨n1, n2, n3⟩ := sig_nice hB hU hE hG hI hT hW hS hF ht' hf
  obtain ⟨h1, -, -⟩ := hT F E σ B a a' G X om om' ht'
  obtain ⟨hJ, -, -⟩ := hE F E σ B h1.base _ G.W _ _ (Or.inr h1.skew)
  refine ⟨?_, n1, hC F E σ h1.base.cm B.emb _ G.W hJ f n1 n2 n3 hc⟩
  obtain ⟨k, S, hS1, hS2⟩ := n2
  exact (hS2 f hS1).1

end PositivityTheory.ThKEst

end
end

