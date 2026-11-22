import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.Bundle0006
import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop
import Development.WeilBound.ThetaLifts.TowerModels.Bundle0006
import Development.WeilBound.ThetaLifts.SmallCones.Bundle0001
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0055
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0030

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ConeCore
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sfin_of {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (s : Set α) : SFinite μ ∧ SFinite (μ.restrict s) :=
  ⟨inferInstance, inferInstance⟩

theorem sfin_haar {G : Type} [Group G] [TopologicalSpace G] [SecondCountableTopology G] [LocallyCompactSpace G] [MeasurableSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (s : Set G) : SFinite μ ∧ SFinite (μ.restrict s) := ⟨inferInstance, inferInstance⟩

theorem cone_core (hUn : Unfold) (hU : UnipEx) (hD : StabDec) (hTB : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hA : EvAdm)
    {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W}
    {M₀ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {j₀ j₁ i₀ i₁ r s r' s' r₀ s₀ r₀' s₀' : ℕ}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) {I e} (he : IsEv B M M₀ H.ι H'.ι I e)
    {K : Subgroup (UA σ X.J)} {μK : Measure K} {μ : Measure (AE F E)ˣ} (hI : Iwa H K) (hμK : μK.IsHaarMeasure) (hμ : μ.IsHaarMeasure)
    (u : (AE F E)ˣ → Ten F E n d) (z : ℕ) (ι : (AE F E)ˣ → (AE F E)ˣ) (hι : ι = id ∨ ι = fun l => l⁻¹) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ χX χW om om₀, IsPair B M χX χW om r s r' s' → IsPair B M₀ χX χW om₀ r₀ s₀ r₀' s₀' →
      ∀ (ν χ : Chr F E) (S : Submodule ℂ (Fn F n d)), Continuous ν → Laws B M om om₀ H H' e u ν χ z ι →
      (∀ Ψ ∈ S, Ψ ∈ schA F (Fin n × Fin d)) → (∀ x, ∀ Ψ ∈ S, om x Ψ ∈ S) →
      (∀ Ψ ∈ S, ∀ h₁, ∫⁻ l, (∫⁻ g in M₀.dom, ‖theta om₀ (e (M.co.rho B.ψ (u l) Ψ)) g h₁‖ₑ ∂M₀.μ) *
        ENNReal.ofReal ((absE F E l : ℝ) ^ z) ∂μ < ⊤) →
      (∀ Ψ ∈ schA F (Fin n × Fin d), ∃ Ψ₁ ∈ schA F (Fin n₁ × Fin d₁), ∀ l₁ ∈ (adeleClass F).adm (Fin n₁ × Fin d₁),
        Integrable (fun l : (AE F E)ˣ => l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) μ ∧
        l₁ Ψ₁ = ∫ l, l₁ (e (M.co.rho B.ψ (u l) Ψ)) * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ∂μ) →
      ∀ Φ ∈ S, KFinite om K Φ →
      (∀ γ, Moves (σ := σ) (X := X) H γ → ∀ h,
        (∀ᵐ g ∂(M.μ.restrict M.dom), Summable fun x => thv B M om e (u 1) Φ h (γ x * g)) ∧
        IntegrableOn (fun g => ∑' x, thv B M om e (u 1) Φ h (γ x * g)) M.dom M.μ ∧
        ∫ g in M.dom, ∑' x, thv B M om e (u 1) Φ h (γ x * g) ∂M.μ = κ * coneI B M om M₀ om₀ e K μK μ u ν z (om (1, h) Φ) 1) ∧
      (∀ t h₁ p, IsLevi H' t h₁ p → ∀ h, coneI B M om M₀ om₀ e K μK μ u ν z (om (1, p * h) Φ) 1 =
        (χ t : ℂ) * (((absE F E t : ℝ) ^ (((d : ℝ) - n) / 2) : ℝ) : ℂ) * coneI B M om M₀ om₀ e K μK μ u ν z (om (1, h) Φ) h₁) ∧
      ∀ h h₁, coneI B M om M₀ om₀ e K μK μ u ν z (om (1, h) Φ) h₁ = M₀.I om₀ (cone B M om e K μK μ u ν z (om (1, h) Φ)) h₁ := by
  by_cases hex : ∃ χX χW om om₀, IsPair B M χX χW om r s r' s' ∧ IsPair B M₀ χX χW om₀ r₀ s₀ r₀' s₀'
  swap
  · exact ⟨1, one_ne_zero, fun χX χW om om₀ hp hp₀ => absurd ⟨χX, χW, om, om₀, hp, hp₀⟩ hex⟩
  obtain ⟨χ0, χ0', o, o₀, hq, hq₀⟩ := hex
  obtain ⟨-, -, -, -, ⟨lev, hlc, hlev, -⟩, -⟩ := hU F E σ B n n₁ X X₁ H j₀ j₁ r s hq.base (Or.inl hq.herm) hH
  obtain ⟨-, -, -, -, ⟨lev', -, hlev', -⟩, -⟩ := hU F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hq.base (Or.inr hq.skew) hH'
  obtain ⟨κ, hκ, hUnf⟩ := hUn F E σ B n n₁ X X₁ H j₀ j₁ r s hq.base hq.herm hH K μK μ M.μ M.dom M₀.μ M₀.dom lev hI hμK hμ
    hq.good.haar hq.good.dom hq₀.good.haar hq₀.good.dom hlev
  refine ⟨κ, by exact_mod_cast hκ.ne', fun χX χW om om₀ hp hp₀ ν χ S hν hL hle hst hfin hlam Φ hΦ hK => ?_⟩
  obtain ⟨-, -, i1, -, i2, i3, i4⟩ := ideleTop F E
  obtain ⟨j1, j2, j3, -⟩ := i4 μ hμ
  obtain ⟨k1, k2, -⟩ := hG F E σ hp.base.cm n₁ X₁.J (hE F E σ B hp.base n₁ X₁ r₀ s₀ (Or.inl hp₀.herm)).1
  obtain ⟨-, k3, -⟩ := hG F E σ hp.base.cm n X.J (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1
  have k4 : BorelSpace (UA σ X₁.J) := ⟨rfl⟩
  have k5 : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have k6 := hp₀.good.haar
  obtain ⟨k10, k11⟩ := sfin_haar M₀.μ M₀.dom
  have k12 : SFinite μ := (sfin_of μ ∅).1
  have k7 : CompactSpace K := isCompact_iff_compactSpace.1 hI.1
  obtain ⟨⟨l₀, hl₀, hl₀'⟩, hrho, hev⟩ := hA F E σ B n d n₁ d₁ X W X₁ W₁ M M₀ hp.base hp.good hp₀.good
  obtain ⟨l₁, hl₁, hl₁'⟩ := hev _ _ _ e he (u 1) l₀ hl₀
  have hsch : ∀ v, ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ v Ψ) ∈ schA F (Fin n₁ × Fin d₁) :=
    fun v Ψ h => he.maps _ (hrho v Ψ h)
  have hcv : ∀ Ψ ∈ schA F (Fin n × Fin d), Continuous fun x => thetaSum F (e (M.co.rho B.ψ (u 1) (om x Ψ))) := fun Ψ h =>
    (pair_cont hp hl₁ h).congr fun x => by rw [hl₁' _ (pair_pres hp x h), hl₀' _ (hsch _ _ (pair_pres hp x h))]
  have hιc : Continuous ι := by rcases hι with rfl | rfl; exacts [continuous_id, continuous_inv]
  have habs : Continuous fun l : (AE F E)ˣ => (absE F E l : ℝ) := NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE
  have hw : Continuous fun l : (AE F E)ˣ => (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z :=
    (continuous_subtype_val.comp hν).mul ((Complex.continuous_ofReal.comp habs).pow z)
  have hw0 : ∀ l : (AE F E)ˣ, (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z ≠ 0 := fun l =>
    mul_ne_zero (Circle.coe_ne_zero _) (pow_ne_zero _ (by exact_mod_cast absE_ne l))
  have hOK : LineOK B M om M₀ om₀ e μ u ν z S := by
    refine ⟨hle, hst, fun l => hsch _, fun g h => ⟨_, pair_adm hp₀ (g, h) hl₀, fun Φ hΦ => hl₀' _ (pair_pres hp₀ _ hΦ)⟩,
      fun Ψ hΨ h₁ => ?_, hlam⟩
    refine int_prod μ _ (θ := fun x => theta om₀ (e (M.co.rho B.ψ (u x.1) Ψ)) x.2 h₁) ?_ hw (fun l => ?_) (hfin Ψ hΨ h₁)
    · have c1 : Continuous fun x : (AE F E)ˣ × UA σ X₁.J =>
          thetaSum F (e (M.co.rho B.ψ (u 1) (om (lev (ι x.1, x.2), lev' (1, h₁)) Ψ))) *
            (((absE F E (ι x.1) : ℝ) ^ (1 - (n : ℝ)) : ℝ) : ℂ) / ((ν x.1 : ℂ) * ((absE F E x.1 : ℝ) : ℂ) ^ z) :=
        (((hcv Ψ (hle Ψ hΨ)).comp ((hlc.comp ((hιc.comp continuous_fst).prodMk continuous_snd)).prodMk continuous_const)).mul
          (Complex.continuous_ofReal.comp ((habs.comp (hιc.comp continuous_fst)).rpow_const fun x => Or.inl (absE_ne _)))).div
          (hw.comp continuous_fst) fun x => hw0 _
      exact c1.congr fun x => by rw [hL.toLawsT.theta (hlev _ _) (hlev' _ _) (hle Ψ hΨ), mul_div_cancel_right₀ _ (hw0 _)]
    · rw [norm_mul, Circle.norm_coe, one_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  obtain ⟨m, Ψ, c, hΨ, hc, hd⟩ := kfin_dec hp (hle Φ hΦ) hK S fun k => hst _ _ hΦ
  have hci : ∀ i, Integrable (c i) μK := fun i => (hc i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hd' : ∀ h (k : K), om (k.1, 1) (om (1, h) Φ) = ∑ i, c i k • om (1, h) (Ψ i) := fun h k => by
    rw [show om (k.1, 1) (om (1, h) Φ) = om (1, h) (om (k.1, 1) Φ) by simp [om_mul], hd, map_sum]
    simp only [map_smul]
  refine ⟨fun γ hγ h => ?_, fun t h₁ p hl h => hL.coneI_law hp μK (hle Φ hΦ) hl h,
    fun h h₁ => hOK.coneI_eq μK (fun i => hst _ _ (hΨ i)) hci (hd' h) h₁⟩
  obtain ⟨f1, f2⟩ := hOK.unf μK (fun i => hst _ _ (hΨ i)) hci (hd' h) ι
    (fun G => by rcases hι with rfl | rfl; exacts [rfl, lintegral_inv_eq_self G])
    (fun G => by rcases hι with rfl | rfl; exacts [rfl, integral_inv_eq_self G μ]) lev (thv B M om e (u 1) Φ h) (fun l g k => by
      rw [← hL.toLawsT.theta (hlev _ _) (levi_one (W₁ := W₁) H') (pair_pres hp _ (pair_pres hp _ (hle Φ hΦ)))]
      simp [thv, om_mul])
  rw [← f2]
  refine hUnf γ hγ _ ((hcv Φ (hle Φ hΦ)).comp (continuous_id.prodMk continuous_const)) (fun v hv g => ?_)
    (fun δ hδ hx g => hL.toLawsT.rat hD hTB hp hp₀ hH (hsch _) (hle Φ hΦ) h hδ hx g) f1
  unfold thv
  rw [show om (v * g, h) Φ = om (v, 1) (om (g, h) Φ) by simp [om_mul], hL.uni v hv _ (pair_pres hp _ (hle Φ hΦ))]

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.SplitLatMap
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr PositivityTheory.ThKG.Tow.Pln

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cartan_low {n n₁ : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} {θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ}
    {ι : Matrix (Fin n) (Fin n₁) ℂ} {P : Matrix (Fin n₁) (Fin n) ℂ} (hP : P * ι = 1) (h : IsCartan M θ) (e : θ * ι = ι * θ₁) :
    IsCartan (ιᵀ * M * ι.map star) θ₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [← Matrix.one_mul (θ₁ * θ₁), ← hP, Matrix.mul_assoc, ← Matrix.mul_assoc ι, ← e, Matrix.mul_assoc θ, ← e,
      ← Matrix.mul_assoc θ, h1, Matrix.one_mul]
  · have m : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (C : Matrix (Fin b) (Fin c) ℂ),
        (A * C).map star = A.map star * C.map star := fun A C => Matrix.map_mul (f := starRingEnd ℂ)
    calc _ = (ι * θ₁)ᵀ * M * (ι * θ₁).map star := by simp only [Matrix.transpose_mul, m, Matrix.mul_assoc]
      _ = ιᵀ * (θᵀ * M * θ.map star) * ι.map star := by rw [← e]; simp only [Matrix.transpose_mul, m, Matrix.mul_assoc]
      _ = _ := by rw [h2]
  · rw [← gram_vec, Matrix.mulVec_mulVec, ← e, ← Matrix.mulVec_mulVec]
    refine h3 _ fun h0 => hx ?_
    rw [← Matrix.one_mulVec x, ← hP, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem splitLat_map {v : Pl F} (τ : E →ₐ[F] Fv F v) {n m : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    {L' : Submodule (𝓞 E) (Fin m → E)} (A : Matrix (Fin m) (Fin n) E) (h : ∀ z ∈ L, A *ᵥ z ∈ L') {w : Fin n → Fv F v}
    (hw : w ∈ splitLat τ L) : A.map τ *ᵥ w ∈ splitLat τ L' :=
  splitLat_le τ ((splitLat τ L').comap ((A.map τ).mulVecLin.restrictScalars _)) (fun z hz => by
    have e : A.map τ *ᵥ (fun i => τ (z i)) = fun i => τ ((A *ᵥ z) i) :=
      funext fun i => (RingHom.map_mulVec (τ : E →+* Fv F v) A z i).symm
    show A.map τ *ᵥ (fun i => τ (z i)) ∈ splitLat τ L'
    rw [e]
    exact map_mem_splitLat τ (h z hz)) hw

theorem low_eps {B : Base F E} (hB : B.IsGood σ) {ε : E} {κ : ℂ} (hκ1 : κ * star κ = 1)
    (hκ : ∀ e : E →+* ℂ, star κ * e ε = κ) {D : Submodule (𝓞 E) E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {H : Plane E n n₁} {i₀ i₁ r s : ℕ} (hY : IsEps σ B ε κ D Y r s) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) {ε' : E}
    {A' : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E} (h : IsFr (σ : E →+* E) ε' Y.J Y₁.J H.ι H.x H.y A') :
    1 ≤ r ∧ 1 ≤ s ∧ IsEps σ B ε κ D Y₁ (r - 1) (s - 1) := by
  have hcm := hB.cm
  set P : Matrix (Fin n₁) (Fin n) E := A'.submatrix Sum.inl id with hPd
  have hP : ∀ (u : Fin n₁ → E) (a b : E), P *ᵥ (H.ι *ᵥ u + a • H.x + b • H.y) = u := fun u a b => funext fun j => by
    have : A' *ᵥ (H.ι *ᵥ u + a • H.x + b • H.y) = Sum.elim u ![a, b] := by
      rw [← fr_mulVec, Matrix.mulVec_mulVec, h.inv2, Matrix.one_mulVec]
    exact congrFun this (Sum.inl j)
  have hPι : P * H.ι = 1 := Matrix.ext fun i j => by
    exact (congrFun (congrFun h.inv2 (Sum.inl i)) (Sum.inl j)).trans (by simp [Matrix.one_apply])
  have hform : ∀ u u', form σ Y₁.J u u' = form σ Y.J (H.ι *ᵥ u) (H.ι *ᵥ u') := hH.gram ▸ form_gram Y.J H.ι
  have hL : Y₁.L = Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) := Submodule.ext hH.low
  have cg : ∀ e : E →+* ℂ, (H.ι.map e)ᵀ * (κ • Y.J.map e) * (H.ι.map e).map star = κ • Y₁.J.map e := fun e => by
    rw [Matrix.mul_smul, Matrix.smul_mul, map_gram hcm, hH.gram]
  have hPe : ∀ {S : Type} [CommRing S] (e : E →+* S), P.map e * H.ι.map e = 1 := fun e => by
    rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXX : ∀ e : E →+* ℂ, (fun i => e (H.x i)) ⬝ᵥ (κ • Y.J.map e) *ᵥ star (fun i => e (H.x i)) = 0 := fun e => by
    rw [Matrix.smul_mulVec, dotProduct_smul, ← map_form hcm, hH.xx, map_zero, smul_zero]
  have hmin : min r s ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h1 := aniso (hY.sig w) h0 (hXX _)
    have h2 : H.x = 0 := funext fun i => (B.emb w).1.injective ((congrFun h1 i).trans (map_zero _).symm)
    have e := hH.xy
    rw [h2, form, zero_dotProduct] at e
    exact zero_ne_one e
  refine ⟨by omega, by omega, fun i j => ?_, fun w => ?_, hL ▸ isLattice_comap n n₁ Y.L H.ι P hPι hY.lat, fun u => ?_,
    fun w => ?_, fun v u => ?_⟩
  · rw [← form_single (σ := σ) Y₁.J j i, ← form_single (σ := σ) Y₁.J i j, hform, hform, form_swap hcm hY.herm]
  · rw [← cg]
    refine (real_plane _ (fun i => (B.emb w).1 (H.x i)) (κ • fun i => (B.emb w).1 (H.y i)) _ (P.map (B.emb w).1) hH.rank
      (map_herm hcm _ (hκ _) hY.herm) (hXX _) ?_ ?_ ?_ ?_ (hPe _) (hY.sig w)).1
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hH.yy, map_zero, smul_zero, smul_zero, smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hH.xy, map_one, smul_eq_mul, smul_eq_mul, mul_one, mul_comm, hκ1]
    · rw [Matrix.smul_mulVec, Matrix.mulVec_smul, map_orth hcm _ Y.J H.ι H.x (fun u => (hH.orth u).1), smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
        map_orth hcm _ Y.J H.ι H.y (fun u => (hH.orth u).2), smul_zero, smul_zero]
  · refine ⟨fun hu u' hu' => ?_, fun G => (hH.low u).2 ((hY.dual _).2 fun z hz => ?_)⟩
    · rw [hform]; exact (hY.dual _).1 ((hH.low u).1 hu) _ ((hH.low u').1 hu')
    · obtain ⟨_, _, u', -, -, hu', hz'⟩ := hH.split z hz
      rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (hH.orth u).1,
        (hH.orth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform]
      exact G u' hu'
  · rw [← cg]
    exact cartan_low (hPe _) (hY.cartan w) (hH.cartan w).1
  · have hn := hH.rank
    let f : Fin n₁ → Fin n := fun j => ⟨skip i₀ i₁ j, by have := j.2; unfold skip; split_ifs <;> omega⟩
    have hf : Function.Injective f := fun a b e => Fin.ext (by
      have := congrArg Fin.val e
      simp only [f, skip] at this
      split_ifs at this <;> omega)
    let T : Matrix (Fin n) (Fin n₁) (Fv F v.1) := (1 : Matrix (Fin n) (Fin n) _).submatrix id f
    have e1 : (Y.bas v).1 * T = H.ι.map (B.τ v) * (Y₁.bas v).1 := Matrix.ext fun a j => by
      rw [← (hH.bas v (f j)).2.2 j rfl a]
      simp [T, Matrix.mul_apply, Matrix.one_apply]
    have e2 : (∀ i, u i ∈ v.1.adicCompletionIntegers F) ↔ ∀ i, (T *ᵥ u) i ∈ v.1.adicCompletionIntegers F := by
      refine ⟨fun G i => sum_mem fun j _ => mul_mem ?_ (G j), fun G j => ?_⟩
      · simp only [T, Matrix.submatrix_apply, Matrix.one_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
      · simpa [T, Matrix.mulVec, dotProduct, Matrix.one_apply, hf.eq_iff] using G (f j)
    rw [e2, hY.bas v, Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]
    refine ⟨fun G => ?_, splitLat_map _ _ fun z hz => (hH.low z).1 hz⟩
    have := splitLat_map (L' := Y₁.L) _ P (fun z hz => by
      obtain ⟨a, b, u', -, -, hu', rfl⟩ := hH.split z hz
      rwa [add_comm (a • H.x), hP]) G
    rwa [Matrix.mulVec_mulVec, show P.map (B.τ v) * H.ι.map (B.τ v) = 1 from hPe (B.τ v : E →+* Fv F v.1),
      Matrix.one_mulVec] at this

theorem low_of : Low := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hH
  refine ⟨fun hY => ?_, fun hY => ?_⟩
  · obtain ⟨ε, A', h⟩ := isFr hB (Or.inl hY) hH
    simp only [isHerm_iff] at hY ⊢
    exact low_eps hB (by simp) (fun e => by simp) hY hH h
  · obtain ⟨ε, A', h⟩ := isFr hB (Or.inr hY) hH
    simp only [isSkew_iff] at hY ⊢
    exact low_eps hB (by simp) (fun e => by simp) hY hH h

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.UnfParH
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology PositivityTheory.PlacePermOperatorBicommutantSpan
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.Doubling (absE)

noncomputable section

namespace PositivityTheory.ThKCT.Unf

theorem Par.transport {G G' N H H' T : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] [TopologicalSpace N]
    [MeasurableSpace N] [Group H] [TopologicalSpace H] [Group H'] [TopologicalSpace H'] [CommGroup T] [TopologicalSpace T]
    {μN : Measure N} {nn : N → G} {ι : H →* G} {mm : T →* G} {χ : T →* ℝ≥0} (h : Par μN nn ι mm χ) (Φ : G ≃ₜ* G') (Ψ : H ≃ₜ* H') :
    Par μN (fun p => Φ (nn p)) ((Φ : G →* G').comp (ι.comp (Ψ.symm : H' →* H))) ((Φ : G →* G').comp mm) χ where
  cn := Φ.continuous.comp h.cn
  ci := Φ.continuous.comp (h.ci.comp Ψ.symm.continuous)
  cm := Φ.continuous.comp h.cm
  cχ := h.cχ
  emb := by
    have := (Φ.toHomeomorph.isClosedEmbedding.comp h.emb).comp
      ((Homeomorph.refl N).prodCongr (Ψ.symm.toHomeomorph.prodCongr (Homeomorph.refl T))).isClosedEmbedding
    refine (congrArg IsClosedEmbedding (funext fun z => ?_)).mp this
    exact (map_mul Φ _ _).trans (congrArg (· * _) (map_mul Φ _ _))
  h1 p := by
    obtain ⟨L, a, b⟩ := h.h1 p
    exact ⟨L, a, fun x => by rw [← map_mul, b]⟩
  h2 u := by
    obtain ⟨L, a, b⟩ := h.h2 (Ψ.symm u)
    exact ⟨L, a, fun x => (map_mul Φ _ _).symm.trans ((congrArg Φ (b x)).trans (map_mul Φ _ _))⟩
  h3 t := by
    obtain ⟨L, a, b, c⟩ := h.h3 t
    exact ⟨L, a, b, fun x => (map_mul Φ _ _).symm.trans ((congrArg Φ (c x)).trans (map_mul Φ _ _))⟩
  h4 u t := (map_mul Φ _ _).symm.trans ((congrArg Φ (h.h4 _ t)).trans (map_mul Φ _ _))
  ne := h.ne

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem parH (hcm : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) :
    ∃ (N : Type) (_ : TopologicalSpace N) (_ : SecondCountableTopology N) (_ : MeasurableSpace N) (_ : BorelSpace N)
      (μN : Measure N) (_ : SigmaFinite μN) (_ : IsFiniteMeasureOnCompacts μN) (nn : N → HA (AF F) σ (hypJ J))
      (ι : HA (AF F) σ J →* HA (AF F) σ (hypJ J)) (mm : (AF F ⊗[F] E)ˣ →* HA (AF F) σ (hypJ J)) (χ : (AF F ⊗[F] E)ˣ →* ℝ≥0) (p₀ : N),
      Par μN nn ι mm χ ∧ (∀ a, χ a * absE F E a ^ (M + 1) = 1) ∧ nn p₀ = 1 ∧
      (∀ p u (a : (AF F ⊗[F] E)ˣ), ∃ b r w, (nn p * ι u * mm a).1.val =
        pm (a : AF F ⊗[F] E) b r (sigR (AF F) σ (a⁻¹ : (AF F ⊗[F] E)ˣ)) w u.1.val ∧ (p = p₀ → b = 0 ∧ r = 0 ∧ w = 0)) ∧
      (∀ (h : HA (AF F) σ (hypJ J)) (a : (AF F ⊗[F] E)ˣ), h.1.val *ᵥ Pi.single 0 1 = (a : AF F ⊗[F] E) • Pi.single 0 1 →
        ∃ p u, h = nn p * ι u * mm a) ∧
      (∀ p, ∃ R : N → N, MeasurePreserving R μN μN ∧ ∀ x, nn x * nn p = nn (R x)) ∧
      ∃ C : Set N, IsCompact C ∧ ∀ p, ∃ q, HA.mat (AF F) σ (hypJ J) (nn q) ∈ HFin (AF F) σ (hypJ J) ∧ ∃ p' ∈ C, nn q * nn p = nn p' := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, hsc, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 M
  have : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨nn, ι, mm, c, hval, hΨ, cn, ci, cm, cc, n0, nmul, -, hin, hmn, hmi, -, hdec, rn, -, -⟩ := par2 F E σ hcm M J hJ
  set μW : Measure (Fin 1 → Fin M → AF F ⊗[F] E) := Measure.addHaar with hμW
  set μA : Measure (AF F) := Measure.addHaar with hμA
  obtain ⟨χ, χc, χ1, χ2⟩ := modulus hcm M μW μA inferInstance inferInstance
  obtain ⟨⟨CW, hCW, hW⟩, -⟩ := GlobalTheory.T.rational_tuples_discrete_cocompact_adelic F E σ hcm 1 M
  obtain ⟨⟨CA, hCA, hA⟩, -⟩ := GlobalTheory.T.adele_ring_cocompact_discrete_number_field F
  refine ⟨_, inferInstance, inferInstance, inferInstance, inferInstance, μW.prod μA, inferInstance, inferInstance, nn, ι, mm, χ,
    (0, 0), ⟨cn, ci, cm, χc, hΨ, fun p => ⟨fun x => (p.1 + x.1, p.2 + x.2 + c p.1 x.1), ?_, fun x => nmul _ _ _ _⟩,
      fun u => ⟨Prod.map (actW (AF F) σ J u) id, ?_, fun x => hin u _ _⟩, fun t => ⟨_, ?_, χ1 t, fun x => hmn t _ _⟩, hmi,
      NeZero.ne _⟩, χ2, n0, fun p u a => ?_, fun h a ha => hdec h a ?_,
    fun p => ⟨fun x => (x.1 + p.1, x.2 + p.2 + c x.1 p.1), ?_, fun x => nmul _ _ _ _⟩, CW ×ˢ CA, hCW.prod hCA, fun ⟨w, t⟩ => ?_⟩
  · refine (measurePreserving_add_left μW p.1).skew_product (g := fun w y => p.2 + y + c p.1 w) ?_ (ae_of_all _ fun w => ?_)
    · exact ((continuous_const.add continuous_snd).add (cc.comp (continuous_const.prodMk continuous_fst))).measurable
    · simpa only [add_right_comm p.2] using map_add_left_eq_self μA (p.2 + c p.1 w)
  · exact MeasurePreserving.prod ⟨((hact 1).1.comp (continuous_const.prodMk continuous_id)).measurable,
      GlobalTheory.T.adelic_haar_invariant_unitary_action F E σ hcm M J hJ μW inferInstance u⟩ (MeasurePreserving.id μA)
  · exact Continuous.measurable (by fun_prop)
  · obtain ⟨b, r, e1, e2⟩ := hval p u a
    exact ⟨b, r, _, e1, fun hp => ⟨(e2 hp).1, (e2 hp).2, by rw [hp]; exact smul_zero _⟩⟩
  · have e : eOne (AF F ⊗[F] E) (M + 1) = fun _ => Pi.single 0 1 := by
      funext k i
      refine Fin.cases rfl (fun i => ?_) i
      simp [eOne]
    rw [e]
    exact funext fun _ => ha
  · refine (measurePreserving_add_right μW p.1).skew_product (g := fun w y => y + p.2 + c w p.1) ?_ (ae_of_all _ fun w => ?_)
    · exact ((continuous_snd.add continuous_const).add (cc.comp (continuous_fst.prodMk continuous_const))).measurable
    · simpa only [add_assoc] using map_add_right_eq_self μA (p.2 + c w p.1)
  · obtain ⟨X, hX⟩ := hW w
    obtain ⟨r, hr⟩ := hA (t + c (ratTup (AF F) (-X)) w)
    refine ⟨_, rn (-X) (-r), _, ⟨?_, ?_⟩, nmul _ _ _ _⟩
    · have e : ratTup (F := F) (AF F) (-X) = -ratTup (AF F) X := funext fun a => funext fun i => map_neg _ _
      rwa [e, neg_add_eq_sub]
    · rwa [map_neg, add_assoc, neg_add_eq_sub]

end PositivityTheory.ThKCT.Unf
end
end

