import Development.WeilBound.ThetaLifts.SmallCones.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
import Development.WeilBound.ThetaLifts.SmallCones.Bundle0002

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.LineInt
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField.mixedEmbedding
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.HeisSchA PositivityTheory.ThKCT.Ad PositivityTheory.ThKEst
open GlobalTheory.Doubling (absE)

namespace Line

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def soSub (B : Base F E) (M : Model σ X W) : Submodule ℂ ((Fin n × Fin d → Af F) → ℂ) where
  carrier := soFin B M
  zero_mem' := ⟨zero_mem _, fun f => by rw [GlobalTheory.ThK.Dbl.Dense.pureA_zero]; exact zero_mem _⟩
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, fun f => by rw [GlobalTheory.ThK.Dbl.Dense.pureA_add]; exact add_mem (ha.2 f) (hb.2 f)⟩
  smul_mem' c a ha := ⟨Submodule.smul_mem _ _ ha.1, fun f => by
    rw [GlobalTheory.ThK.Dbl.Dense.pureA_smul]; exact Submodule.smul_mem _ _ (ha.2 f)⟩

theorem contract {B : Base F E} {M : Model σ X W} (hM : M.IsGood B.ψ) {Φ : Fn F n d} (hΦ : Φ ∈ M.So B.ψ B.τ₁)
    (x : Fin n × Fin d → mixedSpace F) : (fun y : Fin n × Fin d → Af F => Φ fun i => pt (x i) (y i)) ∈ soSub B M := by
  induction hΦ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨f, φ, h1, h2, h3, rfl⟩ := h
    have : GlobalTheory.ThK.Dbl.Dense.pf φ ∈ soSub B M := ⟨GlobalTheory.ThK.Dbl.Dense.pf_mem ⟨h1, by
      filter_upwards [h2, hM.std] with v a b using a.trans b⟩, fun f' => Submodule.subset_span ⟨f', φ, h1, h2, h3, rfl⟩⟩
    convert Submodule.smul_mem _ (f x) this using 1
    exact funext fun y => pureA_pt f (GlobalTheory.ThK.Dbl.Dense.pf φ) x y
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

theorem exists_so {B : Base F E} {M : Model σ X W} (hM : M.IsGood B.ψ) {ι : Type} [Fintype ι]
    (φ : ι → (Fin n × Fin d → Af F) → ℂ) : ∃ φ' : ι → (Fin n × Fin d → Af F) → ℂ, (∀ i, φ' i ∈ soFin B M) ∧
      ∀ g : ι → SInf F (Fin n × Fin d), ∑ i, pureA F (g i) (φ i) ∈ M.So B.ψ B.τ₁ →
        ∑ i, pureA F (g i) (φ i) = ∑ i, pureA F (g i) (φ' i) := by
  obtain ⟨q, hq⟩ := (soSub B M).subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  refine ⟨fun i => q (φ i), fun i => (q (φ i)).2, fun g hg => funext fun w => ?_⟩
  let x : Fin n × Fin d → mixedSpace F := fun i => evI F (w i)
  have h1 : ∑ i, g i x • φ i ∈ soSub B M := by
    convert contract hM hg x using 1
    funext y
    simp only [Finset.sum_apply, pureA_pt, Pi.smul_apply, smul_eq_mul]
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hq ⟨_, h1⟩)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_sum, map_smul, LinearMap.id_apply, Submodule.coe_sum,
    Submodule.coe_smul] at h2
  have h3 := congrFun h2 fun i => (w i).2
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3 ⊢
  exact h3.symm

theorem dom_int {M : Model σ X W} {om : Rep σ X W} (hom : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F _)
    {𝓕 : Set ((Fin n × Fin d → Af F) → ℂ)} (hD : Dom M om 𝓕) {ι : Type} [Fintype ι] {φ : ι → (Fin n × Fin d → Af F) → ℂ}
    (h1 : ∀ i, φ i ∈ SB _) (h2 : ∀ i, φ i ∈ 𝓕) {α : Type} [MeasurableSpace α] (μ : Measure α) (g : ι → α → SInf F (Fin n × Fin d))
    (t : α → ℝ) (ht0 : ∀ l, 0 ≤ t l)
    (hg : ∀ q : Seminorm ℂ (SInf F (Fin n × Fin d)), Continuous q → ∀ i, Integrable (fun l => q (g i l) * t l) μ) (h : UA σ W.J) :
    ∫⁻ l, (∫⁻ x in M.dom, ‖theta om (∑ i, pureA F (g i l) (φ i)) x h‖ₑ ∂M.μ) * ENNReal.ofReal (t l) ∂μ < ⊤ := by
  choose p k G hp hG hG' hb using fun i => hD _ (h2 i)
  obtain ⟨l₀, -, hl₀⟩ := exists_adm_eq_thetaSum_of_locallyCompact F (Fin n × Fin d)
  refine lt_of_le_of_lt (lintegral_mono (g := fun l => ∑ i, ENNReal.ofReal (p i (g i l) * t l) *
    (ENNReal.ofReal ((ht h : ℝ) ^ k i) * ∫⁻ x in M.dom, G i x ∂M.μ)) fun l => ?_) ?_
  · refine (mul_le_mul_left (lintegral_mono (g := fun x => ∑ i, ENNReal.ofReal (p i (g i l) * (ht h : ℝ) ^ k i) * G i x)
      fun x => ?_) _).trans (le_of_eq ?_)
    · refine le_trans (le_of_eq ?_) ((enorm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hb i (g i l) x h))
      rw [theta, ← hl₀ _ (hom _ _ (Submodule.sum_mem _ fun i _ => pureA_mem _ (h1 i))), map_sum, map_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => hl₀ _ (hom _ _ (pureA_mem _ (h1 i)))
    · rw [lintegral_finsetSum _ fun i _ => (hG i).const_mul _, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [lintegral_const_mul _ (hG i), ENNReal.ofReal_mul (apply_nonneg _ _), ENNReal.ofReal_mul (apply_nonneg _ _)]
      ring
  · rw [lintegral_finsetSum' _ fun i _ => (hg _ (hp i) i).aemeasurable.ennreal_ofReal.mul_const _]
    refine ENNReal.sum_lt_top.2 fun i _ => ?_
    have hc := ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := (ht h : ℝ) ^ k i)) (hG' i)
    rw [lintegral_mul_const' _ _ hc.ne]
    exact ENNReal.mul_lt_top (hg _ (hp i) i).lintegral_lt_top hc

end Line

open Line

theorem lineInt_of (hS : Slice) (hI : SchInt) (hT : TateAbs) : LineInt := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he v₀ z₀ hz₀ hu τ hτ μ hμ z ν hz hν Ψ hΨ
  obtain ⟨κ, _, φ, g, h1, h2, h3, h4⟩ := nice hS hT hB hM hM₁ he hz₀ hu τ
    (by rcases hτ with rfl | rfl; exacts [fun _ => rfl, cA_cA hB.cm]) μ hμ hz hΨ
  beta_reduce at h3
  refine ⟨fun om₁ hom hD h₁ => ?_, ?_⟩
  · rcases hD with hD | ⟨hD, hso⟩
    · simp only [h3]
      exact dom_int hom hD h1 h1 μ (fun i l => g i l) _ (fun l => by positivity) h4 h₁
    · obtain ⟨φ', hφ', h5⟩ := exists_so hM₁ φ
      have h6 : ∀ a, e (M.co.rho B.ψ (τ a • incM F v₀) Ψ) = ∑ i, pureA F (g i a) (φ' i) := fun a => by
        rw [h3, h5 _ (h3 a ▸ hso _)]
      simp only [h6]
      exact dom_int hom hD (fun i => (hφ' i).1) hφ' μ (fun i l => g i l) _ (fun l => by positivity) h4 h₁
  obtain ⟨-, -, _, -, -, _, -⟩ := ideleTop F E
  let c : (AE F E)ˣ → ℂ := fun l => (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z
  have hc : Continuous c := (continuous_subtype_val.comp hν).mul
    ((Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE)).pow z)
  choose f hf using fun i => hI _ _ μ (fun l : (AE F E)ˣ => c l • g i l) (hc.smul ((h2 i).comp Units.continuous_val)) fun k j =>
    (h4 _ ((schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm (k, j)) i).congr (.of_forall fun l => by
      simp only [map_smul_eq_mul, c, norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, NNReal.norm_eq]
      exact mul_comm _ _)
  refine ⟨∑ i, pureA F (f i) (φ i), Submodule.sum_mem _ fun i _ => pureA_mem _ (h1 i), fun l₁ hl₁ => ?_⟩
  choose T hT using fun i => hl₁ _ (h1 i)
  have e1 : (fun l : (AE F E)ˣ => l₁ (e (M.co.rho B.ψ (τ l.1 • incM F v₀) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) =
      fun l => ∑ i, T i (c l • g i l) := funext fun l => by
    rw [h3, map_sum, mul_assoc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hT, map_smul, smul_eq_mul, mul_comm]
  rw [e1]
  refine ⟨integrable_finsetSum _ fun i _ => (hf i (T i)).1, ?_⟩
  rw [integral_finsetSum _ fun i _ => (hf i (T i)).1, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hT, (hf i (T i)).2]

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.SoKill
section
noncomputable section

namespace PositivityTheory.ThKCT.So

open Filter Topology NumberField IsDedekindDomain Matrix GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.CompanionTheory.Ar.RT.Move GlobalTheory.LatVac PositivityTheory.KCo GlobalTheory.ThK
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField Classical.propDecidable

theorem kill_set {X : Type} [TopologicalSpace X] (N : Submodule ℂ (X → ℂ)) (Z : Set X)
    (h : ∀ Y ∉ Z, ∃ (m : X → ℂ) (c : ℂ), IsLocallyConstant m ∧ m Y ≠ c ∧ ∀ Φ ∈ SB X, (fun y => (m y - c) * Φ y) ∈ N) :
    ∀ Φ ∈ SB X, (∀ Y ∈ Z, Φ Y = 0) → Φ ∈ N := by
  classical
  choose! m c hm hne hN using h
  have key : ∀ s : Finset X, (∀ Y ∈ s, Y ∉ Z) → ∀ Φ ∈ SB X, (∀ y, Φ y ≠ 0 → ∃ Y ∈ s, m Y y = m Y Y) → Φ ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ Φ _ h0
      have : Φ = 0 := funext fun y => by by_contra e; simpa using h0 y e
      rw [this]; exact zero_mem _
    | insert Y s hY ih =>
      intro hs Φ hΦ h0
      have hY1 := hs Y (Finset.mem_insert_self _ _)
      have hU : IsClopen {y | m Y y = m Y Y} := (hm Y hY1).isClopen_fiber _
      have h1 := hN Y hY1 _ (Submodule.smul_mem _ (m Y Y - c Y)⁻¹ (indicator_mem hU hΦ))
      have h2 := ih (fun Z hZ => hs Z (Finset.mem_insert_of_mem hZ)) _ (indicator_mem hU.compl hΦ) fun y hy => by
        have hy1 : y ∈ {y | m Y y = m Y Y}ᶜ := Set.mem_of_indicator_ne_zero hy
        rw [Set.indicator_of_mem hy1] at hy
        obtain ⟨Z, hZ, e⟩ := h0 y hy
        rcases Finset.mem_insert.1 hZ with rfl | hZ
        · exact (hy1 e).elim
        · exact ⟨Z, hZ, e⟩
      convert add_mem h1 h2 using 1
      funext y
      by_cases hy : y ∈ {y | m Y y = m Y Y}
      · have e : m Y y = m Y Y := hy
        have : y ∉ {y | m Y y = m Y Y}ᶜ := fun h => h hy
        simp only [Pi.add_apply, Pi.smul_apply, Set.indicator_of_mem hy, Set.indicator_of_notMem this, e, smul_eq_mul]
        rw [mul_inv_cancel_left₀ (sub_ne_zero.2 (hne Y hY1)), add_zero]
      · simp [Set.indicator_of_notMem hy, Set.indicator_of_mem (show y ∈ {y | m Y y = m Y Y}ᶜ from hy)]
  intro Φ hΦ h1
  have hK : IsCompact {y | Φ y ≠ 0} :=
    hΦ.2.isCompact.of_isClosed_subset (hΦ.1.isClopen_fiber 0).compl.1 subset_closure
  obtain ⟨s, hs, hc⟩ := hK.elim_nhds_subcover (fun Y => {y | m Y y = m Y Y}) fun Y hY =>
    ((hm Y fun e => hY (h1 Y e)).isOpen_fiber _).mem_nhds rfl
  refine key s (fun Y hY e => hs Y hY (h1 Y e)) Φ hΦ fun y hy => ?_
  simpa using hc hy

theorem rank_ne_iff {k : Type} [Field k] {n d : ℕ} (C : Matrix (Fin n) (Fin d) k) : C.rank ≠ n ↔ ∃ p, p ≠ 0 ∧ p ᵥ* C = 0 := by
  have h := LinearMap.finrank_range_add_finrank_ker Cᵀ.mulVecLin
  rw [Module.finrank_fin_fun, ← Matrix.rank, Matrix.rank_transpose] at h
  have : C.rank ≠ n ↔ LinearMap.ker Cᵀ.mulVecLin ≠ ⊥ := by
    rw [Ne, Ne, ← Submodule.finrank_eq_zero]
    omega
  rw [this, Submodule.ne_bot_iff]
  refine exists_congr fun p => ?_
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, and_comm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ}

theorem eigen_kill_set (h : IsCMExt F E σ) (hψ : IsStd ψ) (hX : X.J.det ≠ 0) (hW : W.J.det ≠ 0) {t : E →ₐ[F] Fv F v} {ι}
    (hι : M.IsLinBar ψ t 1 1 ι) (l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (A : Set (Matrix (Fin n) (Fin d) (AE F E) × ℂ)) (hA : ∀ a ∈ A, At (evFin F v) a.1 ∧ a.1.map (piW (t.comp σ)) = 0)
    (hl : ∀ a ∈ A, ∀ φ ∈ SB _, l (locRho M ψ v a.1 φ) = a.2 * l φ) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Fv F v))
    (hz : ∀ x, At (evFin F v) x → x.map (piW t) = 0 → (∀ a ∈ A, ψ (sy σ X W x a.1) = a.2) → ι φ (coB σ X W t x) = 0) :
    l φ = 0 := by
  choose xo a1 a2 a3 using exists_coB h t hX hW
  have hb := hι.bij
  have key := kill_set ((SB _ ⊓ LinearMap.ker l).map ι) {Y | ∀ a ∈ A, ψ (sy σ X W (xo Y) a.1) = a.2} (fun Y hY => ?_) _ (hb.1 hφ)
    fun Y hY => by rw [← a3 Y]; exact hz _ (a1 Y) (a2 Y) hY
  · obtain ⟨φ', h', e⟩ := key
    rw [← hb.2.1 h'.1 hφ e]
    exact h'.2
  simp only [Set.mem_setOf_eq, not_forall] at hY
  obtain ⟨⟨u, c⟩, ha, hne⟩ := hY
  obtain ⟨hu, h1⟩ := hA _ ha
  let m : Matrix (Fin n) (Fin d) (Fv F v) → ℂ := fun y => ψ (sy σ X W (xo y) u)
  have hm : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ι (locRho M ψ v u φ) = fun y => m y * ι φ y := fun φ hφ => funext fun y => by
    have := mult' M hψ hι hu h1 (a1 y) (a2 y) hφ
    rwa [a3] at this
  haveI : T2Space (Matrix (Fin n) (Fin d) (Fv F v)) := inferInstanceAs (T2Space (Fin n → Fin d → Fv F v))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin d) (Fv F v)) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin d → Fv F v))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin d) (Fv F v)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin d → Fv F v))
  refine ⟨m, c, lc_of_mul m fun Φ hΦ => ?_, hne, fun Φ hΦ => ?_⟩
  · obtain ⟨φ', h', rfl⟩ := hb.2.2 hΦ
    rw [← hm φ' h']
    exact hb.1 (locRho_mem M hψ u h')
  · obtain ⟨φ', h', rfl⟩ := hb.2.2 hΦ
    refine ⟨locRho M ψ v u φ' - c • φ', ⟨sub_mem (locRho_mem M hψ u h') (Submodule.smul_mem _ _ h'), ?_⟩, ?_⟩
    · change l _ = 0
      rw [map_sub, map_smul, hl _ ha φ' h', smul_eq_mul, sub_self]
    · rw [map_sub, map_smul, hm φ' h']
      funext y
      simp [sub_mul]

include M in
theorem sy_smul (x u : Matrix (Fin n) (Fin d) (AE F E)) (a : AF F) : sy σ X W x (a • u) = a * sy σ X W x u := by
  simp only [sy, M.co.form, map_smul, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_sub]

theorem map_vec (π : AE F E →+* Fv F v) (t : E → Fv F v) (ht : ∀ x, π (inclR (F := F) (AF F) x) = t x) (ε : AE F E) (p : Fin n → E)
    (q : Fin d → E) : (ε • incM F (vecMulVec p q)).map π = π ε • vecMulVec (fun i => t (p i)) fun j => t (q j) := by
  ext i j
  simp [incM, vecMulVec_apply, ht]

theorem trace_vec {k : Type} [Field k] (C : Matrix (Fin n) (Fin d) k) (p : Fin n → k) (q : Fin d → k) :
    (Cᵀ * vecMulVec p q).trace = p ⬝ᵥ C *ᵥ q := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem piW_inc (t : E →ₐ[F] Fv F v) (x : E) : piW t (inclR (F := F) (AF F) x) = t x := by
  show splitProj t (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = t x
  have : compFin F E v ((1 : AF F) ⊗ₜ[F] x) = 1 ⊗ₜ[F] x :=
    congrArg (· ⊗ₜ[F] x) (map_one (evFin F v))
  rw [this, splitProj_tmul, one_mul]

theorem at_lift (c : Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)) : At (evFin F v) (liftV v c • u) := fun a ha => by
  rw [smul_smul, ← smul_eq_mul, at_liftV v c a ha, zero_smul]

theorem so_le (hM : M.IsGood ψ) (t : E →ₐ[F] Fv F v) {Ψ} (h : Ψ ∈ M.So ψ t) : Ψ ∈ schA F (Fin n × Fin d) := by
  refine (Submodule.span_le.2 ?_ : M.So ψ t ≤ _) h
  rintro _ ⟨f, φ, h1, h2, -, rfl⟩
  obtain ⟨g, hg, e⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_eq_pureA M ψ hM φ h1 h2
  rw [e f]
  exact Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem so_kill (hL : LinEx) {B : Base F E} {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (hM : M.IsGood B.ψ) (t : E →ₐ[F] Fv F v) (L : Fn F n d →ₗ[ℂ] ℂ) (S : Set ((Fin n → E) × (Fin d → E) × Fv F v))
    (hS : ∀ a ∈ S, ∀ ε : AE F E, At (evFin F v) ε → piW t ε = 1 → piW (t.comp σ) ε = 0 → ∀ c : Fv F v, ∀ Φ ∈ schA F _,
      L (M.co.rho B.ψ (liftV v c • ε • incM F (vecMulVec a.1 a.2.1)) Φ) = B.ψ (liftV v (a.2.2 * c)) * L Φ)
    (hz : ∀ C : Matrix (Fin n) (Fin d) (Fv F v), (∀ a ∈ S, (fun i => t (a.1 i)) ⬝ᵥ C *ᵥ (fun j => t (a.2.1 j)) = a.2.2) →
      ∃ p, p ≠ 0 ∧ p ᵥ* C = 0) : ∀ Φ ∈ M.So B.ψ t, L Φ = 0 := by
  refine fun Φ hΦ => (Submodule.span_le (p := LinearMap.ker L)).2 ?_ hΦ
  rintro _ ⟨f, φ, h1, h2, ⟨hv, ι, hι, h3⟩, rfl⟩
  obtain ⟨r, hr, er⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_at M B.ψ hM φ h2 f v
  have hsch : ∀ φ' ∈ SB (Fin n × Fin d → Fv F v), tens (evFin F v) φ' r ∈ schA F (Fin n × Fin d) := fun φ' h' => by
    have e := er (Function.update φ v φ') fun w hw => Function.update_of_ne hw _ _
    rw [Function.update_self] at e
    obtain ⟨g, hg, e'⟩ := GlobalTheory.CompanionTheory.Ar.RT.Inj.pure_eq_pureA M B.ψ hM (Function.update φ v φ') (fun w => by
      by_cases hw : w = v
      · subst hw
        simpa using h'
      · rw [Function.update_of_ne hw]
        exact h1 w) (by
      filter_upwards [h2, Filter.eventually_cofinite_ne v] with w h h'
      rw [Function.update_of_ne h', h])
    rw [← e, e' f]
    exact Submodule.subset_span ⟨f, g, hg, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, er φ fun _ _ => rfl]
  let l : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun φ' => L (tens (evFin F v) φ' r)
      map_add' := fun a b => by
        have e : tens (evFin F v) (a + b) r = tens (evFin F v) a r + tens (evFin F v) b r := funext fun _ => add_mul _ _ _
        rw [e, map_add]
      map_smul' := fun c a => by
        have e : tens (evFin F v) (c • a) r = c • tens (evFin F v) a r := funext fun _ => mul_assoc _ _ _
        rw [e, map_smul]
        rfl }
  obtain ⟨ε, e0, e1, e2⟩ := exists_pair hB.cm t 1 0
  have hat : ∀ (c : Fv F v) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) (liftV v c • u) := at_lift
  refine eigen_kill_set M hB.cm hB.std (det_herm hX) (det_skew hW) hι l
    {b | ∃ a ∈ S, ∃ c : Fv F v, b = (liftV v c • ε • incM F (vecMulVec a.1 a.2.1), B.ψ (liftV v (a.2.2 * c)))} ?_ ?_ hv
    fun x hx h0 hc => h3 _ ?_
  · rintro _ ⟨a, -, c, rfl⟩
    refine ⟨hat _ _, ?_⟩
    rw [← smul_assoc, map_vec _ _ (piW_inc _), Algebra.smul_def, map_mul, e2, mul_zero, zero_smul]
  · rintro _ ⟨a, ha, c, rfl⟩ φ' h'
    change L (tens _ (locRho M B.ψ v _ φ') r) = _ * L _
    rw [← rho_tens M B.ψ (hat _ _) φ' hr, hS a ha ε e0 e1 e2 c _ (hsch φ' h')]
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, B.ψ (liftV v s₀) ≠ 1 := by
    by_contra e
    push Not at e
    exact GlobalTheory.PsiNontriv.psiV_ne_one B.ψ hB.std v (AddChar.ext _ _ e)
  obtain ⟨p, hp, e⟩ := hz (X.J.map t * x.map (piW (t.comp σ)) * (W.J.map t)ᵀ) fun a ha => by
    have k1 := (hL F E σ B n d X W M _ _ _ _ hB hX hW v t).2 x (ε • incM F (vecMulVec a.1 a.2.1)) hx h0
    rw [map_vec _ _ (piW_inc _), e1, one_smul, trace_vec] at k1
    rw [← k1]
    by_contra hne
    set b := evFin F v (sy σ X W x (ε • incM F (vecMulVec a.1 a.2.1)))
    have k2 := hc _ ⟨a, ha, s₀ / (b - a.2.2), rfl⟩
    simp only at k2
    rw [sy_smul M, mul_comm, mul_liftV] at k2
    have k3 : b * (s₀ / (b - a.2.2)) = s₀ + a.2.2 * (s₀ / (b - a.2.2)) := by
      have := sub_ne_zero.2 hne
      field_simp
      ring
    rw [k3, map_add, AddChar.map_add_eq_mul] at k2
    refine hs₀ ((mul_eq_right₀ fun e0 => ?_).1 k2)
    have := GlobalTheory.StdCharFromIsStd.norm_psi hB.std (liftV v (a.2.2 * (s₀ / (b - a.2.2))))
    rw [e0, norm_zero] at this
    exact zero_ne_one this
  refine (rank_ne_iff _).2 ⟨p, hp, ?_⟩
  rw [coB_eq, Matrix.neg_mul, Matrix.neg_mul, Matrix.vecMul_neg, e, neg_zero]

end PositivityTheory.ThKCT.So

end
end

