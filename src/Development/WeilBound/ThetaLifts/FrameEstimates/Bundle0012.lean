import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0006
import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0007
import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0005
import Development.WeilBound.CoreStatements.LocalThetaKernels.LinearIndependentOfNotMem
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0008
import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
import Development.WeilBound.ThetaLifts.FrameEstimates.ContinuousMixedSymm
import Development.WeilBound.ThetaLifts.FrameEstimates.RankIffRight

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.SchrAddPt
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace levelStructure

open LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem schr_add_pt (ψ : AddChar (AF F) ℂ) (w δ : Pt F κ) (Φ : (κ → AF F) → ℂ) :
    schr ψ (w + δ) Φ = ψ (⅟(2 : AF F) * (δ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ δ.2)) • schr ψ w (schr ψ δ Φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (w.1 ⬝ᵥ δ.2) * invOf_mul_self (2 : AF F)

theorem lc_fin {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) :
    IsLocallyConstant fun a : Af F => ψ ((0, a) : Ainf F × Af F) :=
  GlobalTheory.CompanionTheory.AdelicHeis.isLocallyConstant_fin (ψ.compAddMonoidHom (AddMonoidHom.inr (Ainf F) (Af F)))
    (hψ.1.comp (continuous_const.prodMk continuous_id)) fun _ => GlobalTheory.CompanionTheory.AdelicHeis.norm_eq_one ψ hψ.1 hψ.2.1 _

theorem fst_zero {a : AF F} (h : e0 F * a = a) : a.1 = 0 := by
  rw [← h, finiteAdeleIdempotentOfF_mul_self]

theorem fix_near {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    ∀ᶠ u in 𝓝 (0 : Pt F κ), e0 F • u = u → ∀ f, schr ψ u (pureA F f g) = pureA F f g := by
  have hc : Continuous fun u : Pt F κ => ((fun i => (u.1 i).2, fun i => (u.2 i).2) : (κ → Af F) × (κ → Af F)) :=
    (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp continuous_fst)).prodMk
      (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp continuous_snd))
  have h := (hc.tendsto 0).eventually
    (eventually_fix _ (lc_fin hψ) ψ.map_zero_eq_one (⅟(2 : AF F)).2 hg)
  filter_upwards [h] with u key hu f
  funext x
  have h1 : ∀ i, (u.1 i).1 = 0 := fun i => fst_zero (congrFun (congrArg Prod.fst hu) i)
  have h2 : ∀ i, (u.2 i).1 = 0 := fun i => fst_zero (congrFun (congrArg Prod.snd hu) i)
  have p : ψ (x ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2)) = ψ ((0, ((fun i => (x i).2) ⬝ᵥ fun i => (u.2 i).2) +
      (⅟(2 : AF F)).2 * ((fun i => (u.1 i).2) ⬝ᵥ fun i => (u.2 i).2)) : Ainf F × Af F) := by
    rw [← dot_snd, ← dot_snd]
    refine congrArg ψ (Prod.ext ?_ rfl)
    change (x ⬝ᵥ u.2).1 + (⅟(2 : AF F)).1 * (u.1 ⬝ᵥ u.2).1 = 0
    rw [dot_fst _ _ h2, dot_fst _ _ h2, mul_zero, add_zero]
  have q : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + u.1) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (u.1 i).1) = _
    rw [h1 i, add_zero]
  simp only [schr, pureA]
  rw [p, q, mul_left_comm]
  exact congrArg _ (key fun i => (x i).2)

theorem schr_near {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F))
    {K : Set (Pt F κ)} (hK : IsCompact K) : ∀ᶠ δ in 𝓝 (0 : Pt F κ), e0 F • δ = δ → ∀ c ∈ K, ∀ w, e0 F • w = e0 F • c →
      ∀ f, schr ψ (w + δ) (pureA F f g) = schr ψ w (pureA F f g) := by
  have h1 : ∀ᶠ δ in 𝓝 (0 : Pt F κ), ∀ c ∈ K, ψ (e0 F * (⅟(2 : AF F) * (δ.1 ⬝ᵥ c.2 - c.1 ⬝ᵥ δ.2))) = 1 := by
    refine hK.eventually_forall_of_forall_eventually fun c _ => ?_
    have hc : Continuous fun z : Pt F κ × Pt F κ => ⅟(2 : AF F) * (z.1.1 ⬝ᵥ z.2.2 - z.2.1 ⬝ᵥ z.1.2) := by
      unfold dotProduct; fun_prop
    filter_upwards [((lc_fin hψ).comp_continuous (continuous_snd.comp hc)).eventually_eq (0, c)] with z hz
    rw [finiteAdeleIdempotentOfF_mul_self]
    refine hz.trans ?_
    simp only [Function.comp, Prod.fst_zero, Prod.snd_zero, zero_dotProduct, dotProduct_zero, sub_zero, mul_zero]
    exact ψ.map_zero_eq_one
  filter_upwards [h1, fix_near hψ hg] with δ h1 h2 hδ c hc w hw f
  have e : ⅟(2 : AF F) * (δ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ δ.2) = e0 F * (⅟(2 : AF F) * (δ.1 ⬝ᵥ c.2 - c.1 ⬝ᵥ δ.2)) := by
    have a1 : e0 F • δ.1 = δ.1 := congrArg Prod.fst hδ
    have a2 : e0 F • δ.2 = δ.2 := congrArg Prod.snd hδ
    have b1 : e0 F • w.1 = e0 F • c.1 := congrArg Prod.fst hw
    have b2 : e0 F • w.2 = e0 F • c.2 := congrArg Prod.snd hw
    have c1 : δ.1 ⬝ᵥ w.2 = e0 F * (δ.1 ⬝ᵥ c.2) := by
      conv_lhs => rw [← a1, smul_dotProduct, ← dotProduct_smul, b2, dotProduct_smul, smul_eq_mul]
    have c2 : w.1 ⬝ᵥ δ.2 = e0 F * (c.1 ⬝ᵥ δ.2) := by
      conv_lhs => rw [← a2, dotProduct_smul, ← smul_dotProduct, b1, smul_dotProduct, smul_eq_mul]
    rw [c1, c2]; ring
  rw [schr_add_pt, h2 hδ f, e, h1 c hc, one_smul]

open Classical in
theorem ev_adm (y : κ → AF F) : (LinearMap.proj y : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (y i).2) •
    (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => ?_⟩
  exact mul_comm _ _

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isFin_of (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    {u : UA σ J} (hu : ∀ w, (mat u).map (piInf (τ w)) = 1) : IsFin u := by
  refine Matrix.ext fun i j => ?_
  have h0 : ∀ w, piInf (τ w) ((mat u - 1) i j) = 0 := fun w => by
    have : (mat u - 1).map (piInf (τ w)) = 0 := by
      rw [Matrix.map_sub _ (map_sub _), hu, Matrix.map_one _ (map_zero _) (map_one _), sub_self]
    exact congrFun (congrFun this i) j
  have := GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ h τ ((1 - e0 F) • (mat u - 1) i j) ((at_iff _).2 (by
    rw [smul_smul, mul_sub, mul_one, show e0 F * e0 F = e0 F from finiteAdeleIdempotentOfF_mul_self _, sub_self, zero_smul])) fun w => by
      rw [Algebra.smul_def, map_mul, h0, mul_zero]
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

theorem coef_near {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {g : (Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _) {C : Set (Ten F E n d)} (hC : IsCompact C) :
    ∀ᶠ u in 𝓝 (1 : UA σ W.J), IsFin u → ∀ z : Ten F E n d, (∃ c ∈ C, At (evI F) (z - c)) → ∀ f,
      schr ψ (M.co.e (z * (mat u)ᵀ)) (pureA F f g) = schr ψ (M.co.e z) (pureA F f g) := by
  have := ring_AE F E
  have : IsModuleTopology (AF F) (Ten F E n d) := inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hV := schr_near hψ hg (hC.image he)
  have hm : Continuous fun z : UA σ W.J × Ten F E n d => M.co.e (z.2 * (mat z.1 - 1)ᵀ) :=
    he.comp (continuous_snd.matrix_mul
      (((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).sub continuous_const).matrix_transpose)
  have h1 := hC.eventually_forall_of_forall_eventually (x₀ := (1 : UA σ W.J))
    (P := fun u c => M.co.e (c * (mat u - 1)ᵀ) ∈ _) fun c _ => hm.continuousAt.preimage_mem_nhds (by
      rwa [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, Matrix.transpose_zero, Matrix.mul_zero, map_zero])
  filter_upwards [h1] with u h1 hu z hz f
  obtain ⟨c, hc, hz⟩ := hz
  rw [at_iff, smul_sub, sub_eq_zero] at hz
  have hu' : e0 F • (mat u - 1)ᵀ = (mat u - 1)ᵀ := by rw [← Matrix.transpose_smul, hu]
  have e : z * (mat u)ᵀ = z + c * (mat u - 1)ᵀ := by
    rw [← hu', Matrix.mul_smul, ← Matrix.smul_mul, ← hz, Matrix.smul_mul, ← Matrix.mul_smul, hu', Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]
  rw [e, map_add]
  exact h1 c hc (by rw [← map_smul, ← Matrix.mul_smul, hu']) _ ⟨c, hc, rfl⟩ _ (by rw [← map_smul, ← map_smul, hz]) f

end levelStructure

open levelStructure in

theorem level_of (hC : CoefEq) (hF : FourierInj) (hB : CoefBd) : Level := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ
  by_cases h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0
  · exact ⟨Set.univ, univ_mem, fun u _ _ f => by rw [h0, map_zero]⟩
  push Not at h0
  obtain ⟨f₀, h0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hy : pureA F f₀ φ y ≠ 0 := hy
  have hs := IsUWeilPair.isUSplitting hp.weil
  have mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f =>
    Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨p, C, -, hCc, hb⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0
  have h1 := coef_near M hp.base.std hφ hCc
  have := LatticeQuotientMeasure.ring_AE F E
  have hi : Continuous fun u : UA σ W.J => u⁻¹ :=
    ((continuous_inv (G := GL (Fin d) (AE F E))).comp continuous_subtype_val).subtype_mk fun u => (u⁻¹).2
  have h2 := (hi.tendsto' 1 1 inv_one).eventually h1
  have hc : Continuous fun u : UA σ W.J => ‖om (1, u) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ :=
    ((((hs.cont _ (ev_adm y) _ (mem f₀)).comp (continuous_const.prodMk continuous_id)).div_const _).sub
      continuous_const).norm
  have h3 := pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by
    change ‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2
    rw [map_one, Module.End.one_apply, div_self hy]
    norm_num))
  refine ⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩
  have hu := isFin_of hp.base.cm B.emb hu
  have key : ∀ (f : SInf F (Fin n × Fin d)) x, om (1, u) (pureA F f φ) x * (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) =
      pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y) := by
    intro f x
    refine hF F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), ParityOfCoefficients.mat_one_inv, Matrix.one_mul]
    by_cases a : ∃ c ∈ C, At (evI F) (z - c)
    · unfold coef
      rw [h2 hu.inv z a]
    by_cases a' : ∃ c ∈ C, At (evI F) (z * (mat u⁻¹)ᵀ - c)
    · unfold coef
      rw [← h1 hu _ a', Matrix.mul_assoc, ← Matrix.transpose_mul, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1,
        Matrix.transpose_one, Matrix.mul_one]
    have b := hb f f₀ z
    have b' := hb f f₀ (z * (mat u⁻¹)ᵀ)
    rw [maj, if_neg a, mul_zero, norm_le_zero_iff] at b
    rw [maj, if_neg a', mul_zero, norm_le_zero_iff] at b'
    rw [b, b']
  have h4 : (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) ≠ 0 := fun h => by
    have := key f₀ y
    rw [h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self] at this
    exact hy this
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (1, u) (pureA F f φ) = c • pureA F f φ :=
    ⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y), fun f => funext fun x => by
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩
  have h5 : ∀ k : ℕ, om (1, u ^ k) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul]; exact congrArg (· (pureA F f₀ φ)) (map_one om)
    | succ k ih =>
      rw [pow_succ, show ((1, u ^ k * u) : UA σ X.J × UA σ W.J) = (1, u ^ k) * (1, u) from by simp, map_mul,
        Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']
  have h6 : c = 1 := PositivityTheory.ThKH.Locrep.eq_one_of_pow_near fun k => by
    have := h3 hu k
    rwa [Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one] at this
  intro f
  rw [hc, h6, one_smul]

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.ThetaSumNeg
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

theorem sq_iff {a P L : ℝ≥0∞} : a ^ 2 ≤ P ^ 2 * L ↔ a ≤ P * L ^ (1 / 2 : ℝ) := by
  have e : L = (L ^ (1 / 2 : ℝ)) ^ 2 := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]; norm_num
  conv_lhs => rw [e, ← mul_pow]
  exact ⟨fun h => (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h, fun h => by gcongr⟩

theorem latSum_mono {τ : ∀ w : InfinitePlace F, EmbOver E w} {C C' : Set (Ten F E n d)} (hC : C ⊆ C') (N : ℕ) (S)
    (g : UA σ X.J) (h : UA σ W.J) : latSum τ C N S g h ≤ latSum τ C' N S g h := by
  refine ENNReal.tsum_le_tsum fun x => ENNReal.ofReal_le_ofReal ?_
  by_cases hx : ∃ c ∈ C, At (evI F) (mat g⁻¹ * incM F x.1 * (mat h⁻¹)ᵀ - c)
  · obtain ⟨c, h1, h2⟩ := hx
    unfold maj
    rw [if_pos ⟨c, h1, h2⟩, if_pos ⟨c, hC h1, h2⟩]
  · conv_lhs => unfold maj
    rw [if_neg hx]
    exact sq_maj_nonneg _ _ _ _

variable (B om) in

def Qb (N : ℕ) (Φ : SInf F (Fin n × Fin d) → Fn F n d) : Prop :=
  (∀ f, Φ f ∈ schA F (Fin n × Fin d)) ∧ ∃ (p : Seminorm ℂ (SInf F (Fin n × Fin d))) (C : Set (Ten F E n d)), Continuous p ∧
    IsCompact C ∧ ∀ f g h, ‖theta om (Φ f) g h‖ₑ ^ 2 ≤ ENNReal.ofReal (p f) ^ 2 * latSum B.emb C N (fullRank E n d) g h

theorem qb_zero (N : ℕ) : Qb B om N fun _ => 0 :=
  ⟨fun _ => zero_mem _, 0, ∅, continuous_const, isCompact_empty, fun f g h => by simp [theta, thetaSum]⟩

theorem Qb.add (hp : IsPair B M χX χW om r s r' s') {N : ℕ} {Φ Ψ : SInf F (Fin n × Fin d) → Fn F n d} (h1 : Qb B om N Φ)
    (h2 : Qb B om N Ψ) : Qb B om N fun f => Φ f + Ψ f := by
  obtain ⟨a1, p, C, b1, c1, d1⟩ := h1
  obtain ⟨a2, q, C', b2, c2, d2⟩ := h2
  refine ⟨fun f => add_mem (a1 f) (a2 f), p + q, C ∪ C', (b1.add b2 : Continuous fun f => p f + q f), c1.union c2,
    fun f g h => sq_iff.2 ?_⟩
  have e1 := sq_iff.1 ((d1 f g h).trans (mul_le_mul_right (latSum_mono (C' := C ∪ C') Set.subset_union_left N _ g h) _))
  have e2 := sq_iff.1 ((d2 f g h).trans (mul_le_mul_right (latSum_mono (C' := C ∪ C') Set.subset_union_right N _ g h) _))
  rw [theta_add hp (a1 f) (a2 f), Seminorm.add_apply, ENNReal.ofReal_add (apply_nonneg p f) (apply_nonneg q f), add_mul]
  exact (enorm_add_le _ _).trans (add_le_add e1 e2)

theorem Qb.smul (hp : IsPair B M χX χW om r s r' s') {N : ℕ} {Φ : SInf F (Fin n × Fin d) → Fn F n d} (h1 : Qb B om N Φ)
    (c : ℂ) : Qb B om N fun f => c • Φ f := by
  obtain ⟨a1, p, C, b1, c1, d1⟩ := h1
  refine ⟨fun f => Submodule.smul_mem _ _ (a1 f), ‖c‖₊ • p, C, (continuous_const.mul b1 : Continuous fun f => ‖c‖ * p f), c1,
    fun f g h => sq_iff.2 ?_⟩
  have e1 := sq_iff.1 (d1 f g h)
  rw [theta_smul hp c (a1 f), enorm_mul, show (‖c‖₊ • p) f = ‖c‖ * p f from rfl, ENNReal.ofReal_mul (norm_nonneg c),
    ofReal_norm, mul_assoc]
  exact mul_le_mul_right e1 _

theorem qb_sum (hp : IsPair B M χX χW om r s r' s') {N : ℕ} {ι : Type} (S : Finset ι)
    {Φ : ι → SInf F (Fin n × Fin d) → Fn F n d} (h : ∀ i, Qb B om N (Φ i)) : Qb B om N fun f => ∑ i ∈ S, Φ i f := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using qb_zero N
  | insert a S ha ih => simpa [Finset.sum_insert ha] using (h a).add hp ih

theorem thetaSum_neg {κ : Type} (Φ : (κ → AF F) → ℂ) : thetaSum F (fun x => Φ (-x)) = thetaSum F Φ := by
  unfold thetaSum
  rw [← (Equiv.neg (κ → F)).tsum_eq]
  refine tsum_congr fun ξ => congrArg Φ (funext fun i => ?_)
  simp

theorem theta_neg (hP : Parity) (hp : IsPair B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F _) (g h) :
    theta om (fun x => Φ (-x)) g h = theta om Φ g h := by
  obtain ⟨e, c, he, hc, h1⟩ := hP F E σ B n d X W M χX χW om r s r' s' hp
  have hc0 : c ≠ 0 := fun h0 => by simp [h0] at hc
  have hs := (IsUWeilPair.isUSplitting hp.weil).pres (g, h) Φ hΦ
  have hcomm : g * e = e * g := Subtype.ext (Units.ext (by
    change mat g * mat e = mat e * mat g
    rw [he]; simp))
  have e1 : om (g, h) (om (e, 1) Φ) = om (e, 1) (om (g, h) Φ) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk, hcomm, mul_one,
      one_mul]
  rw [h1 Φ hΦ, h1 _ hs, map_smul] at e1
  unfold theta
  rw [smul_right_injective _ hc0 e1, thetaSum_neg]

set_option maxHeartbeats 800000 in
open scoped Classical in

theorem qb_piece (hP : Parity) (hS : CoefSum) (hE : CoefEq) (hB : CoefBd) (hp : IsPair B M χX χW om r s r' s') (N : ℕ)
    {φ : (Fin n × Fin d → Af F) → ℂ} (hφ : φ ∈ SB _)
    (h0 : ∀ (f : SInf F (Fin n × Fin d)) (μ : Measure (Fin n × Fin d → AF F)), μ.IsAddHaarMeasure → ∀ z : Ten F E n d,
      (z.map (piW (B.τ₁.comp σ))).rank ≠ n → coef F B.ψ μ (pureA F f φ) (fun x => pureA F f φ (-x)) (M.co.e z) = 0) :
    Qb B om N fun f => pureA F f φ := by
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨c, hc, h1⟩ := theta_mul_le hS hE hp μ hμ
  have hφ' : (fun y => φ (-y)) ∈ SB (Fin n × Fin d → Af F) :=
    ⟨hφ.1.comp_continuous continuous_neg, hφ.2.comp_homeomorph (Homeomorph.neg _)⟩
  obtain ⟨p, C, hpc, hC, h2⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ _ hφ' N
  let P : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)
  have hPf : ∀ f : SInf F (Fin n × Fin d), (fun x => pureA F f φ (-x)) = pureA F (P f) fun y => φ (-y) := fun f => by
    funext x
    unfold pureA
    congr 1
    exact congrArg f (funext fun i => map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1)
  let q : Seminorm ℂ (SInf F (Fin n × Fin d)) := p + p.comp P.toLinearMap
  have hq : Continuous q := (hpc.add (hpc.comp P.continuous) : Continuous fun f => p f + p (P f))
  refine ⟨fun f => pureA_mem f hφ, NNReal.mk √c (Real.sqrt_nonneg c) • q, C,
    (continuous_const.mul hq : Continuous fun f => √c * q f), hC, fun f g h => ?_⟩
  have hm := pureA_mem f hφ
  have e := h1 _ hm _ (ParityOfCoefficients.neg_mem_schA hm) g h
  rw [theta_neg hP hp hm] at e
  refine sq_le_of_coef hc (apply_nonneg q f) e (fun x hx => h0 f μ hμ _ fun hr => hx ?_) fun x => ?_
  · rw [Matrix.map_mul, Matrix.map_mul, ThKEst.W.incM_piW] at hr
    have hr2 := ThKEst.W.rank_of_mul _ _ _ hr
    exact ThKEst.W.rank_of_map (B.τ₁.comp σ).toRingHom x hr2
  · rw [hPf]
    refine (h2 f (P f) _).trans (mul_le_mul_of_nonneg_right ?_ (sq_maj_nonneg _ _ _ _))
    have a1 := apply_nonneg p f
    have a2 := apply_nonneg p (P f)
    change p f * p (P f) ≤ (p f + p (P f)) * (p f + p (P f))
    nlinarith

end

theorem sqSo_of' (hF : SoFin) (hC : SoCut) (hP : Parity) (hS : CoefSum) (hE : CoefEq) (hB : CoefBd) : SqSo := by
  classical
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨m, c, χ, hχ, e⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hp).2.2.2 φ hφ
  have key : Qb B om N fun f => ∑ i, c i • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (χ i) := qb_sum hp _ fun i => Qb.smul hp (c := c i) <| by
    obtain ⟨k, ξ, e1, hξ⟩ := hC F E σ B n d X W M χX χW om r s r' s' hp _ (hχ i).2.2
    have hstd : ∀ᶠ u in cofinite, χ i u = ThKEst.W.stdF _ u := ((hχ i).2.1.and hp.good.std).mono fun v hv => hv.1.trans hv.2
    have hg : ThKEst.W.Good (χ i) := ⟨(hχ i).1, hstd⟩
    have e2 : (fun f : SInf F (Fin n × Fin d) => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (χ i)) =
        fun f : SInf F (Fin n × Fin d) => ∑ j, pureA F f (ThKEst.W.pf (Function.update (χ i) B.v₁ (ξ j))) := funext fun f => by
      conv_lhs => rw [← Function.update_eq_self B.v₁ (χ i), ThKEst.W.pure_update (v := B.v₁) f hstd, e1]
      have e3 : ∀ j, pureA F f (ThKEst.W.pf (Function.update (χ i) B.v₁ (ξ j))) =
          tens (evFin F B.v₁) (ξ j) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update (χ i) B.v₁ 1)) := fun j =>
        ThKEst.W.pure_update (v := B.v₁) f hstd (ξ j)
      rw [Finset.sum_congr rfl fun j _ => e3 j]
      funext x
      rw [Finset.sum_apply]
      unfold tens
      rw [Finset.sum_apply, Finset.sum_mul]
    rw [e2]
    refine qb_sum hp _ fun j => qb_piece hP hS hE hB hp N (ThKEst.W.pf_mem (hg.update (hξ j).1.1)) fun f μ hμ z hz => ?_
    rw [← ThKEst.W.pure_eq, ThKEst.W.pure_update (v := B.v₁) f hstd]
    refine (hξ j).2 _ ⟨fun x z hz => ?_, ?_⟩ μ hμ z hz
    · have h1 := (ThKEst.W.at_iff (v := B.v₁) z).1 hz
      have h2 : z = fun i => GlobalTheory.EmbChart.atPlace B.v₁ (evFin F B.v₁ (z i)) := funext fun i =>
        (congrFun h1 i).symm.trans (ThKEst.W.ep_mul (v := B.v₁) (z i))
      rw [h2]
      exact ThKEst.W.indep_pure (v := B.v₁) f (χ i) x _
    · rw [← ThKEst.W.pure_update (v := B.v₁) f hstd]
      exact ThKEst.W.pure_mem f (hg.update (hξ j).1.1)
  obtain ⟨-, p, C, h1, h2, h3⟩ := key
  exact ⟨p, C, h1, h2, fun f g h => by rw [e f]; exact h3 f g h⟩

end PositivityTheory.ThKEst

end
end

