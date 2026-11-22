import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.Bundle0002
import Development.WeilBound.ThetaLifts.SmallCones.Bundle0003

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ConeBasic
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Basic

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W}
  {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}

theorem mat_mul' {J : Matrix (Fin n) (Fin n) E} (g h : UA σ J) : mat (g * h) = mat g * mat h := rfl

theorem mat_one' {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mulVec {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {x y : Fin n → AE F E} (h : mat g *ᵥ x = y) :
    mat g⁻¹ *ᵥ y = x := by
  rw [← h, Matrix.mulVec_mulVec, ← mat_mul', inv_mul_cancel, mat_one', Matrix.one_mulVec]

theorem pair_pres (hp : IsPair B M χX χW om r s r' s') (x) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) : om x Φ ∈ schA F _ :=
  (IsUWeilPair.isUSplitting hp.weil).pres x Φ hΦ

theorem pair_cont (hp : IsPair B M χX χW om r s r' s') {l} (hl : l ∈ (adeleClass F).adm (Fin n × Fin d)) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : Continuous fun x => l (om x Φ) :=
  (IsUWeilPair.isUSplitting hp.weil).cont l hl Φ hΦ

theorem pair_adm (hp : IsPair B M χX χW om r s r' s') (x) {l} (hl : l ∈ (adeleClass F).adm (Fin n × Fin d)) :
    l ∘ₗ om x ∈ (adeleClass F).adm (Fin n × Fin d) :=
  (IsUWeilPair.isUSplitting hp.weil).adm x l hl

theorem om_mul (om : Rep σ X W) (x y) (Φ) : om x (om y Φ) = om (x * y) Φ := by rw [map_mul]; rfl

theorem rho_om (hp : IsPair B M χX χW om r s r' s') (g h) (a : Fin n → AE F E) (b : Fin d → AE F E) (c : AE F E) {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    M.co.rho B.ψ (c • Matrix.vecMulVec a b) (om (g, h) Φ) =
      om (g, h) (M.co.rho B.ψ (c • Matrix.vecMulVec (mat g⁻¹ *ᵥ a) (mat h⁻¹ *ᵥ b)) Φ) := by
  rw [(IsUWeilPair.isUSplitting hp.weil).impl (g, h) _ Φ hΦ]
  congr 2
  change _ = mat g * _ * (mat h)ᵀ
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mat_mul', ← mat_mul', mul_inv_cancel, mul_inv_cancel, mat_one', mat_one',
    Matrix.one_mulVec, Matrix.one_mulVec]

theorem rho_linear (M : Model σ X W) (ψ) (u) {ι : Type} (t : Finset ι) (c : ι → ℂ) (Φ : ι → Fn F n d) :
    M.co.rho ψ u (∑ i ∈ t, c i • Φ i) = ∑ i ∈ t, c i • M.co.rho ψ u (Φ i) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ev_adm {κ : Type} [Fintype κ] (y : κ → AF F) : (LinearMap.proj y : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  classical
  refine ⟨g (fun i => (y i).2) • ((BoundedContinuousFunction.evalCLM ℂ fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)), fun f => ?_⟩
  simp [pureA, mul_comm]

theorem thetaSum_smul' {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem kfin_dec (hp : IsPair B M χX χW om r s r' s') {K : Subgroup (UA σ X.J)} {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (hK : KFinite om K Φ) (S : Submodule ℂ (Fn F n d)) (hS : ∀ k : K, om (k.1, 1) Φ ∈ S) :
    ∃ (m : ℕ) (Ψ : Fin m → Fn F n d) (c : Fin m → K → ℂ), (∀ i, Ψ i ∈ S) ∧ (∀ i, Continuous (c i)) ∧
      ∀ k : K, om (k.1, 1) Φ = ∑ i, c i k • Ψ i := by
  set V := Submodule.span ℂ (Set.range fun k : K => om (k.1, 1) Φ)
  haveI : FiniteDimensional ℂ V := hK
  let b := Module.finBasis ℂ V
  have hc : Continuous fun k : K => (⟨om (k.1, 1) Φ, Submodule.subset_span ⟨k, rfl⟩⟩ : V) := by
    refine Continuous.subtype_mk (continuous_pi fun y => ?_) _
    exact (pair_cont hp (ev_adm y) hΦ).comp (continuous_subtype_val.prodMk continuous_const)
  refine ⟨_, fun i => (b i).1, fun i k => b.repr ⟨om (k.1, 1) Φ, Submodule.subset_span ⟨k, rfl⟩⟩ i,
    fun i => Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hS k) (b i).2,
    fun i => (b.coord i).continuous_of_finiteDimensional.comp hc, fun k => ?_⟩
  have := congrArg Subtype.val (b.sum_repr ⟨om (k.1, 1) Φ, Submodule.subset_span ⟨k, rfl⟩⟩)
  rw [Submodule.coe_sum] at this
  exact this.symm

end Basic

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.Leaves
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem lawα {n d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {χ χ' : Chr F E} {x y : ℝ} {T : UA σ W.J → ℂ}
    (_n : n = n) (h : HasLaw W₁ H' χ x T) (e1 : χ = χ') (e2 : x = y) : HasLaw W₁ H' χ' y T := by subst e1 e2; exact h

theorem splitEx_of (hB : GenBig) (hSm : GenSmall) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx)
    (hPl : PlaneHerm) (hC : EvCone) (hZ : EvZero) (hU : UnipEx) (hL : Low) (hT : TriplePair) : SplitEx := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h d₁ W₁ H' i₀ i₁ hH'
  obtain ⟨hp, hp', hw⟩ := hT F E σ B a a' G X om om' h
  obtain ⟨h1, h2, hW₁⟩ := (hL F E σ B _ _ G.W W₁ H' i₀ i₁ _ _ h.base hH').2 h.geo.hW
  have hlt := h.geo.lt
  have hev := h.geo.even
  have heB := h.geo.eBig
  have haB := h.geo.aBig
  obtain ⟨k, hk⟩ := hev
  have uniq : ∀ f fa fb, Split2 W₁ H' X f fa fb → ∃! x : (UA σ G.W.J → ℂ) × (UA σ G.W.J → ℂ), Split2 W₁ H' X f x.1 x.2 :=
    fun f fa fb hs => ⟨(fa, fb), hs, fun y hy => Prod.ext (split_uniq hU h hH' hy hs).1 (split_uniq hU h hH' hy hs).2⟩
  refine ⟨fun Φ hΦ => ?_, fun Φ hΦ => ?_⟩
  · obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h.base _ _ G.V W₁ _ _ _ _ h.geo.hV hW₁
    obtain ⟨om₁, hp₁⟩ := hW _ _ hp.hX hp.hW hp.resX (res_low hp.resW hH'.rank) M₁ hM₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V G.W G.M _ _ om _ _ _ _ hp d₁ G.V W₁ H' i₀ i₁ M₁ rfl hH' hM₁
    obtain ⟨C₀, -, H0⟩ := anyBig hB hA hK hS hI hP hPl hC F E σ B a (a + a') d₁ G.V G.W W₁ H' i₀ i₁ (a - G.p) G.p _ _ G.M M₁
      (by omega) ⟨(a - a') / 2, by omega, by omega⟩ hH' e₀ he₀
    obtain ⟨A₀, A₁, c1, c2, c3, -⟩ := H0 _ _ om om₁ (IsPair.cast hp rfl rfl (by omega) (by omega)) hp₁ Φ hΦ (by simp)
    exact uniq _ A₁ A₀ ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  · obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h.base _ _ G.V' W₁ _ _ _ _ h.geo.hV' hW₁
    obtain ⟨om₁, hp₁⟩ := hW _ _ hp'.hX hp'.hW hp'.resX (res_low hp'.resW hH'.rank) M₁ hM₁
    obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V' G.W G.M' _ _ om' _ _ _ _ hp' d₁ G.V' W₁ H' i₀ i₁ M₁ rfl hH' hM₁
    obtain ⟨C₀, -, H0⟩ := anySmall hSm hA hK hS hI hP hPl hC F E σ B a' (a + a') d₁ G.V' G.W W₁ H' i₀ i₁ G.q (a' - G.q) _ _ G.M' M₁
      (by omega) ⟨(a - a') / 2 + 1, by omega, by omega⟩ hH' e₀ he₀
    obtain ⟨A₀, A₁, c1, c2, c3, -⟩ := H0 _ _ om' om₁ (IsPair.cast hp' rfl rfl (by omega) (by omega)) hp₁ Φ hΦ.1 (fun _ => hΦ.2)
    exact uniq _ A₀ A₁ ⟨c1, c2, lawα (n := 0) rfl c3 (by simp) (by push_cast; ring)⟩

theorem ctBigZero_of (hB : GenBig) (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hI : IwaEx) (hP : PairEx)
    (hPl : PlaneHerm) (hC : EvCone) (hU : UnipEx) (hT : TriplePair) : CTBigZero := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hc e he
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  obtain ⟨eV, ep, eq, hH, hH'⟩ := hc
  dsimp only at eV ep eq hH hH' he
  subst eV ep
  by_cases hex : ∃ X om om', IsTriple B G X om om'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' _ _ h => absurd ⟨X, om, om', h⟩ hex⟩
  obtain ⟨X0, o, o', h0⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨C₀, hC₀, H0⟩ := anyBig hB hA hK hS hI hP hPl hC F E σ B a (a + (b + 2)) (a + b) G.V G.W W₁ H' _ _ (a - G.p) G.p
    (a + b - (G.p + q₁)) (G.p + q₁) G.M M₁ (by omega) ⟨(a - (b + 2)) / 2, by omega, by omega⟩ hH' e he
  refine ⟨C₀, hC₀, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om om₁ (IsPair.cast (hT F E σ B _ _ G X om om' h).1 rfl rfl (by omega) (by omega))
    (hT F E σ B _ _ _ X om₁ om₁' h₁).1 Φ hΦ (by simp)
  have := split_uniq hU h hH' hs (fa' := A₁) (fb' := A₀)
    ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  rw [this.2]
  exact c4 g m hm x (by simp)

theorem ctSmallZero_of (hA : GenAniso) (hK : KFinData) (hS : StabEx) (hT : TriplePair) : CTSmallZero := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he
  obtain ⟨C, hC, H0⟩ := hA F E σ B a' _ _ G.V' G.W G₁.W H' _ _ G.q (a' - G.q) (b + 2 + a' - (G.p + G.q)) (G.p + G.q)
    (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) G₁.V' G.M' G₁.M' hc.eV (by rw [hc.q0]; simp) hc.hH' e he
  refine ⟨C, hC, fun X om om' om₁ om₁' h h₁ Φ hΦ => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).2.1
  obtain ⟨K, μK, μ, hK1, -⟩ := hS F E σ B _ G.V' _ _ h.base hp.herm
  obtain ⟨A₀, c1, c2, c3⟩ := H0 _ _ om' om₁' hp
    (IsPair.cast (hT F E σ B _ _ G₁ X om₁ om₁' h₁).2.1 (by rw [hc.q0, hc.q1]) (by rw [hc.q0, hc.q1]) rfl rfl) Φ
    (hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ).1
  exact ⟨A₀, ⟨by rwa [add_zero], c2, fun t m _ h => by simp⟩, c3⟩

theorem ctBigCone_of (hB : GenBig) (hK : KFinData) (hI : IwaEx) (hP : PairEx) (hZ : EvZero) (hU : UnipEx) (hT : TriplePair) :
    CTBigCone := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he K μK μ hK1 hμK hμ
  by_cases hex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' h h₁ => absurd ⟨X, om, om', om₁, om₁', h, h₁⟩ hex⟩
  obtain ⟨X0, o, o', o₁, o₁', h0, h1⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  have e1 := hc.ep
  have e2 := hc.q0
  have e3 := hc.q1
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h0.base _ _ G.V G₁.W _ _ _ _ h0.geo.hV h1.geo.hW
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V G.W G.M _ _ o _ _ _ _ (hT F E σ B _ _ G X0 o o' h0).1 _ G.V G₁.W H' _ _ M₁ rfl hc.hH' hM₁
  obtain ⟨C₀, C₁, -, hC₁, H0⟩ := hB F E σ B _ _ _ _ G.V G.W G₁.V G₁.W H H' _ _ _ _ (b - G₁.p) G₁.p (b + a' - (G₁.p + G₁.q))
    (G₁.p + G₁.q) G.M G₁.M hc.hH hc.hH' M₁ e₀ e hM₁ h1.geo.hM he₀ he ((b + 2 - a') / 2) ⟨by omega, by omega⟩ K μK μ
    (hI F E σ B _ _ G.V _ _ H h0.base h0.geo.hV (adapted_x_ne hc.hH) hc.hH.xx K hK1) hμK hμ
  refine ⟨C₁, hC₁, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).1
  have hp₁ := (hT F E σ B _ _ G₁ X om₁ om₁' h₁).1
  obtain ⟨om₂, hp₂⟩ := hW _ _ hp.hX hp.hW hp.resX hp₁.resW M₁ hM₁
  obtain ⟨hs1, hf⟩ := hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om om₂ om₁ (IsPair.cast hp (by omega) (by omega) (by omega) (by omega))
    (IsPair.cast hp₂ (by omega) (by omega) rfl rfl) hp₁ Φ hs1 hf
  have := split_uniq hU h hc.hH' hs (fa' := A₁) (fb' := A₀)
    ⟨by rwa [add_comm A₁], lawα (n := 0) rfl c3 (by simp) (by push_cast; ring), c2⟩
  rw [this.1, (c4 g m hm x).1, inv_div]
  rfl

theorem ctSmallCone_of (hB : GenSmall) (hK : KFinData) (hI : IwaEx) (hP : PairEx) (hZ : EvZero) (hU : UnipEx) (hT : TriplePair) :
    CTSmallCone := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hc e he K μK μ hK1 hμK hμ
  by_cases hex : ∃ X om om' om₁ om₁', IsTriple B G X om om' ∧ IsTriple B G₁ X om₁ om₁'
  swap
  · exact ⟨1, one_ne_zero, fun X om om' om₁ om₁' h h₁ => absurd ⟨X, om, om', om₁, om₁', h, h₁⟩ hex⟩
  obtain ⟨X0, o, o', o₁, o₁', h0, h1⟩ := hex
  have hlt := h0.geo.lt
  have heB := h0.geo.eBig
  have haB := h0.geo.aBig
  have e1 := hc.ep
  have e2 := hc.eq
  obtain ⟨k, hk⟩ := h0.geo.even
  obtain ⟨⟨M₁, hM₁⟩, hW⟩ := hP F E σ B h0.base _ _ G.V' G₁.W _ _ _ _ h0.geo.hV' h1.geo.hW
  obtain ⟨⟨e₀, he₀⟩, -⟩ := hZ F E σ B _ _ G.V' G.W G.M' _ _ o' _ _ _ _ (hT F E σ B _ _ G X0 o o' h0).2.1 _ G.V' G₁.W H' _ _ M₁ rfl
    hc.hH' hM₁
  obtain ⟨C₀, C₁, -, hC₁, H0⟩ := hB F E σ B _ _ _ _ G.V' G.W G₁.V' G₁.W H H' _ _ _ _ G₁.q (b - G₁.q) (a + b - (G₁.p + G₁.q))
    (G₁.p + G₁.q) G.M' G₁.M' hc.hH hc.hH' M₁ e₀ e hM₁ h1.geo.hM' he₀ he ((a - (b + 2)) / 2 + 1) ⟨by omega, by omega⟩ K μK μ
    (hI F E σ B _ _ G.V' _ _ H h0.base h0.geo.hV' (adapted_x_ne hc.hH) hc.hH.xx K hK1) hμK hμ
  refine ⟨C₁, hC₁, fun X om om' om₁ om₁' h h₁ Φ hΦ fa fb hs g m hm x => ?_⟩
  have hp := (hT F E σ B _ _ G X om om' h).2.1
  have hp₁ := (hT F E σ B _ _ G₁ X om₁ om₁' h₁).2.1
  obtain ⟨om₂, hp₂⟩ := hW _ _ hp.hX hp.hW hp.resX hp₁.resW M₁ hM₁
  obtain ⟨-, hf⟩ := hK F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hp K hK1 Φ hΦ.1
  obtain ⟨A₀, A₁, c1, c2, c3, c4⟩ := H0 _ _ om' om₂ om₁' (IsPair.cast hp (by omega) (by omega) (by omega) (by omega))
    (IsPair.cast hp₂ (by omega) (by omega) rfl rfl) hp₁ Φ hΦ.2 hf
  have := split_uniq hU h hc.hH' hs (fa' := A₀) (fb' := A₁) ⟨c1, c2, lawα (n := 0) rfl c3 (by simp) (by push_cast; ring)⟩
  rw [this.2, (c4 g m hm x).1]
  rfl

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.StabDec
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr

theorem stabDec_of : StabDec := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hY hH
  obtain ⟨ε, A', h⟩ := isFr hB hY hH
  have e : fr (incM F H.ι) (incV F H.x) (incV F H.y) = incM F (fr H.ι H.x H.y) := fr_map _
  refine ⟨fun p t hp => ?_, fun ξ g₁ hg m hm => ?_, fun t g₁ m hm u hu => levi_conj hm hu⟩
  · obtain ⟨u, hu, g₁, m, h1, h2, h3⟩ := stab_dec hB.cm h (det_ne hY) p t hp
    refine ⟨u, hu, g₁, m, h1, h2, fun hr => ?_⟩
    obtain ⟨M, hM⟩ := mem_ratU.1 hr
    refine mem_ratU.2 ⟨(A' * M * fr H.ι H.x H.y).toBlocks₁₁, ?_⟩
    rw [h3, hM, e, incM, incM, incM, ← Matrix.map_mul, ← Matrix.map_mul]
    rfl
  · obtain ⟨m', h1, h2⟩ := exists_levi hB.cm h (Units.map (inclR (F := F) (AF F)).toMonoidHom ξ) g₁
    obtain ⟨M, hM⟩ := mem_ratU.1 hg
    rw [levi_uniq h hm h1]
    refine mem_ratU.2 ⟨fr H.ι H.x H.y * dg M ξ.1 (σ (ξ⁻¹).1) * A', ?_⟩
    rw [h2, hM, e, incM, incM, incM, incM, Matrix.map_mul, Matrix.map_mul]
    congr 2
    ext (i | i) (j | j)
    · rfl
    · exact (map_zero (inclR (F := F) (E := E) (AF F))).symm
    · exact (map_zero (inclR (F := F) (E := E) (AF F))).symm
    · fin_cases i <;> fin_cases j
      exacts [rfl, (map_zero (inclR (F := F) (E := E) (AF F))).symm, (map_zero (inclR (F := F) (E := E) (AF F))).symm, rfl]

end PositivityTheory.ThKCT

end
end

