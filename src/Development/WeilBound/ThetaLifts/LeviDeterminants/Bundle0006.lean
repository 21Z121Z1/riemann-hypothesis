import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0002
import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0014

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.EvalZeroMemAdelicSchwartzAdmittedForms
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.ThKF0

def SiegelChar : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ c : UG (cA σ) (dbl (incM F J)) →* ℂˣ, Continuous c → (∀ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 → c p = 1) → c = 1

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in

theorem evalZero_mem_adelicSchwartzAdmittedForms (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    BoundedContinuousFunction.evalCLM_apply, smul_eq_mul]
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : (fun i : κ => ((0 : κ → AdeleRing (𝓞 F) F) i).2) = 0 := by
    funext i; rfl
  rw [h1, h2, mul_comm]

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem actB_inv_actB {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] {c : E' →ₐ[R] E'} {α β : Type}
    [Fintype β] [DecidableEq β] {J : Matrix β β E'} (p : UG c J) (x : Matrix α β E') :
    actB c p⁻¹ (actB c p x) = x := by
  unfold actB
  rw [Matrix.mul_assoc, ← Matrix.transpose_mul]
  have : ((↑(p⁻¹) : GL β E') : Matrix β β E') * ((p : GL β E') : Matrix β β E') = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  rw [this, Matrix.transpose_one, Matrix.mul_one]

theorem dd_rho_diag {a b : ℕ} {σ : E →ₐ[F] E} {JA : Matrix (Fin a) (Fin a) E} {JB : Matrix (Fin b) (Fin b) E} {κ : Type}
    [Fintype κ] {d : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ}
    {dd : Darboux (symp (cA σ) (-1) (incM F JA) (dbl (incM F JB))) (κ ⊕ κ)}
    (h : IsDblCoord (cA σ) (-1) (incM F JA) (incM F JB) d dd) (ψ : AddChar (AF F) ℂ)
    (z : Matrix (Fin a) (Fin b) (AE F E)) :
    dd.rho ψ (z * (diagCols (Fin b))ᵀ) =
      schr ψ (Sum.elim (d.e z).1 (d.e z).1, Sum.elim (d.e z).2 (-(d.e z).2)) := by
  unfold Darboux.rho
  rw [← h]
  congr 2
  ext i j
  rcases j with j | j <;> erw [Matrix.mul_apply] <;> simp [diagCols, Matrix.one_apply]

theorem member_tw (hT : TwEx) (hC : SiegelChar) (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (d d₁ : Darboux (symp (cA σ) (-1) (incM F JA) (incM F JB)) κ) (hr : RatRel d d₁) (hr' : RatRel d₁ d) (χ : Chr F E)
    (om om₁ : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (h₁ : IsUWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d₁ χ om₁) {e} (he : Tw ψ d d₁ e) :
    ∀ g, ∀ Φ ∈ schA F κ, e (om g Φ) = om₁ g (e Φ) := by
  obtain ⟨hS0, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  obtain ⟨-, dd₁, omd₁, hdd₁, ⟨-, hS₁, hR₁⟩, hres₁⟩ := h₁
  obtain ⟨ed, hd⟩ := hT F ψ hψ _ _ _ dd dd₁
  obtain ⟨ed₀, hd₀⟩ := hT F ψ hψ _ _ _ dd₁ dd
  obtain ⟨ed', hd', hl1, hl2⟩ := hd.exists_inv hψ hd₀ (hr.dbl hdd hdd₁) (hr'.dbl hdd₁ hdd)
  have inv_mul : ∀ (p : UG (cA σ) (dbl (incM F JB))) φ, omd p (omd p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨φy, hφy, hφy0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F (κ ⊕ κ)
  obtain ⟨φz, hφz, hφz0⟩ : ∃ φ ∈ schA F (κ ⊕ κ), ed φ 0 ≠ 0 := ⟨ed' φy, hd'.maps _ hφy, by rwa [hl2 _ hφy]⟩
  have hsp : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd p φ ∈ schA F (κ ⊕ κ) := fun p φ hφ => hS.pres p φ hφ
  have hsp₁ : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ ∈ schA F (κ ⊕ κ) := fun p φ hφ => hS₁.pres p φ hφ
  have key : ∀ p, ∃ c : ℂ, ∀ φ ∈ schA F (κ ⊕ κ), omd₁ p (ed φ) = c • ed (omd p φ) := fun p => by
    obtain ⟨c, hc⟩ := schur hψ dd (omd p⁻¹ ∘ₗ ed' ∘ₗ omd₁ p ∘ₗ ed)
      (fun φ hφ => hsp _ _ (hd'.maps _ (hsp₁ _ _ (hd.maps φ hφ))))
      (fun l hl => hd.adm _ (hS₁.adm p _ (hd'.adm _ (hS.adm p⁻¹ l hl))))
      (fun w φ hφ => by
        have m1 := hd.maps φ hφ
        have m2 := hsp₁ p _ m1
        simp only [LinearMap.comp_apply]
        rw [hd.Heisenberg₂ w φ hφ, hS₁.impl p w _ m1, hd'.Heisenberg₂ _ _ m2, hS.impl _ _ _ (hd'.maps _ m2), actB_inv_actB])
    refine ⟨c, fun φ hφ => ?_⟩
    have := congrArg (fun x => ed (omd p x)) (hc φ hφ)
    simp only [LinearMap.comp_apply, inv_mul, map_smul] at this
    rwa [hl2 _ (hsp₁ p _ (hd.maps φ hφ))] at this
  choose cf hcf using key
  have huniq : ∀ p (c : ℂ), (∀ φ ∈ schA F (κ ⊕ κ), omd₁ p (ed φ) = c • ed (omd p φ)) → c = cf p := fun p c hc => by
    have h1 := hc _ (hsp p⁻¹ φz hφz)
    rw [hcf p _ (hsp p⁻¹ φz hφz), inv_mul] at h1
    have h2 := congrFun h1 0
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact (mul_right_cancel₀ hφz0 h2).symm
  have hmul : ∀ p q, cf (p * q) = cf p * cf q := fun p q => (huniq (p * q) _ fun φ hφ => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcf q φ hφ, map_smul,
      hcf p _ (hsp q φ hφ), smul_smul, mul_comm]).symm
  have hone : cf 1 = 1 := (huniq 1 1 fun φ _ => by simp).symm
  let cM : UG (cA σ) (dbl (incM F JB)) →* ℂ := { toFun := cf, map_one' := hone, map_mul' := hmul }
  let c := cM.toHomUnits
  have hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cf p := fun p => rfl
  have hcont_cf : Continuous cf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hφ := hsp p₀⁻¹ φz hφz
    have hf := hS.cont _ (hd.adm _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ))) _ hφ
    have hf₁ := hS₁.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ (hd.maps _ hφ)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply] at hf hf₁
    have h0 : ed (omd p₀ (omd p₀⁻¹ φz)) 0 ≠ 0 := by rw [inv_mul]; exact hφz0
    refine (hf₁.continuousAt.div hf.continuousAt h0).congr ?_
    filter_upwards [hf.continuousAt.eventually_ne h0] with p hp
    show omd₁ p _ 0 / ed (omd p _) 0 = cf p
    rw [hcf p _ hφ]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hcont : Continuous c := by
    refine Units.continuous_iff.2 ⟨hcont_cf, ?_⟩
    have : (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_cf.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero
  obtain ⟨l, hl, hlinv, φ₀, hφ₀, hl0⟩ := GlobalTheory.T.exists_diagonalLagrangian_invariant_form F ψ κ
  have hinv₁ : ∀ z : Matrix (Fin a) (Fin b) (AE F E), ∀ φ ∈ schA F (κ ⊕ κ), l (dd₁.rho ψ (z * (diagCols (Fin b))ᵀ) φ) = l φ :=
    fun z φ hφ => by rw [dd_rho_diag hdd₁ ψ z]; exact hlinv _ _ φ hφ
  have hP : ∀ (p : UG (cA σ) (dbl (incM F JB))) (t : GL (Fin b) (AE F E)),
      ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * t.1 →
        c p = 1 := fun p t hpt => by
    have hφ := hsp p⁻¹ _ (hd'.maps φ₀ hφ₀)
    have e1 := hR (l ∘ₗ ed) (hd.adm l hl) (fun z φ hφ => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hd.Heisenberg₂ _ φ hφ]
      exact hinv₁ z _ (hd.maps φ hφ)) p t hpt _ hφ
    have e2 := hR₁ l hl hinv₁ p t hpt _ (hd.maps _ hφ)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← e2, hcf p _ hφ, inv_mul, hl2 _ hφ₀, map_smul, smul_eq_mul] at e1
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    exact mul_right_cancel₀ hl0 (by rw [one_mul]; exact e1.symm)
  have hc1 := hC F E σ hσ b JB ε hJ hdet c hcont hP
  have hcf1 : ∀ p, cf p = 1 := fun p => by
    rw [← hcv, hc1]; rfl
  intro g Φ hΦ
  obtain ⟨gd, hgd⟩ := GlobalTheory.T.exists_unitaryDoubled_blockDiag_one (AF F) (AE F E) (cA σ) (Fin b) (incM F JB) g
  obtain ⟨e₂, h₂, hbox⟩ := box_compat hT hψ hr hdd hdd₁ he hd
  obtain ⟨φ₂, hφ₂, hφ₂0⟩ := h₂.ne
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hφ₂0
  have k := hcf gd _ (GlobalTheory.T.theta_sum_tensor_product F κ κ Φ hΦ φ₂ hφ₂).1
  rw [hcf1 gd, one_smul, hres g gd hgd Φ hΦ φ₂ hφ₂, hbox Φ hΦ φ₂ hφ₂, hbox _ (hS0.pres g Φ hΦ) φ₂ hφ₂,
    hres₁ g gd hgd _ (he.maps Φ hΦ) _ (h₂.maps φ₂ hφ₂)] at k
  funext x
  have := congrFun k (Sum.elim x y)
  simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr] at this
  exact (mul_right_cancel₀ hy this).symm

theorem pair_tw (hT : TwEx) (hC : SiegelChar) (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
    (M M₁ : Model σ X W) {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} (hψ : IsStd ψ) (hX : ∀ i j, σ (X.J j i) = X.J i j)
    (hXd : X.J.det ≠ 0) (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0) (hr : RatRel M.co M₁.co) (hr' : RatRel M₁.co M.co)
    {om om₁ : Rep σ X W} (h : M.IsWeil ψ χX χW om) (h₁ : M₁.IsWeil ψ χX χW om₁) {e} (he : Tw ψ M.co M₁.co e) :
    ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), e (om x Φ) = om₁ x (e Φ) := by
  intro x Φ hΦ
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := h
  obtain ⟨hB₁, ⟨d₁, hd₁, hA₁⟩, -⟩ := h₁
  have eW : ∀ i j, σ (W.J j i) = (((-1 : ℤˣ) : ℤ) : E) * W.J i j := fun i j => by simp [hW i j]
  have eX : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j := fun i j => by simp [hX i j]
  have uB := member_tw hT hC σ hσ X.J W.J (-1) eW hWd ψ hψ M.co M₁.co hr hr' χX _ _ hB hB₁ he
  have r1 : RatRel d' d₁ := fun y z => by
    obtain ⟨w, y', z', h1, h2⟩ := hr y z
    exact ⟨wᵀ, y', z', (hd' w).trans h1, (hd₁ w).trans h2⟩
  have r2 : RatRel d₁ d' := fun y z => by
    obtain ⟨w, y', z', h1, h2⟩ := hr' y z
    exact ⟨wᵀ, y', z', (hd₁ w).trans h1, (hd' w).trans h2⟩
  have he' : Tw ψ d' d₁ e := ⟨he.maps, fun w Φ hΦ => by
    have := he.Heisenberg₂ wᵀ Φ hΦ
    rw [Darboux.rho, Darboux.rho, ← hd', ← hd₁, Matrix.transpose_transpose] at this
    exact this, he.adm, he.ne⟩
  have uA := member_tw hT hC σ hσ W.J X.J 1 eX hXd ψ hψ d' d₁ r1 r2 χW _ _ hA hA₁ he'
  have hx : x = (x.1, 1) * (1, x.2) := by simp
  rw [hx, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have h1 : e (om (1, x.2) Φ) = om₁ (1, x.2) (e Φ) := uB x.2 Φ hΦ
  rw [← h1]
  exact uA x.1 _ (hB.1.pres x.2 Φ hΦ)

end PositivityTheory.ThKF0

end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.ThetaGrow
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace PositivityTheory.ThKF0

def ArchBd : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k

theorem theta_moderate_growth_of_decay (harch : ArchBd) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  have hlat := theta_sum_norm_bound_denominator
  have hfin := weil_rep_bounded_denominator
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨N₀, k₂, C₂, hL⟩ := hlat F (Fin n × Fin d)
  obtain ⟨C₁, k₁, hA⟩ := harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ N₀
  obtain ⟨C₃, k₃, hF⟩ := hfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  refine ⟨|C₂| * |C₁| * |C₃| ^ k₂, k₁ + k₃ * k₂, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hsupp⟩ := hF g h
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hb := hL (C₁ * H ^ k₁) m (om (g, h) Φ) hm1 (fun ξ => hA g h _) hsupp
  have hA0 : 0 ≤ C₁ * H ^ k₁ :=
    le_trans (by positivity) (hA g h (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)))
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ k₂ := by positivity
  have hmk : (m : ℝ) ^ k₂ ≤ (|C₃| * H ^ k₃) ^ k₂ :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _))) _
  have hC1 : C₁ * H ^ k₁ ≤ |C₁| * H ^ k₁ := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _)
  show ‖thetaSum F (om (g, h) Φ)‖ ≤ _
  calc ‖thetaSum F (om (g, h) Φ)‖ ≤ C₂ * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ := hb
    _ ≤ |C₂| * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA0) hm0
    _ ≤ |C₂| * (|C₁| * H ^ k₁) * (|C₃| * H ^ k₃) ^ k₂ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC1 (abs_nonneg _)) hmk hm0 (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg hH0 _)))
    _ = |C₂| * |C₁| * |C₃| ^ k₂ * H ^ (k₁ + k₃ * k₂) := by rw [pow_add, pow_mul]; ring

end PositivityTheory.ThKF0
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepRationalDarbouxFixesThetaDistribution
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace PositivityTheory.ThKF0.Resc

section Gen

variable {R : Type} [CommRing R] {K : Type} [CommRing K] [Algebra R K] {c : K →ₐ[R] K}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem ug_smul {v : K} (hv : IsUnit v) (J : Matrix β β K) : UG c (v • J) = UG c J := by
  ext g
  change (g : Matrix β β K)ᵀ * (v • J) * (g : Matrix β β K).map c = v • J ↔
    (g : Matrix β β K)ᵀ * J * (g : Matrix β β K).map c = J
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact hv.smul_left_cancel

omit [Fintype β] [DecidableEq β] in
theorem dbl_smul (v : K) (J : Matrix β β K) : dbl (v • J) = v • dbl J := by
  ext (i | i) (j | j) <;> simp [dbl]

omit [DecidableEq α] [DecidableEq β] in
theorem symp_smul {ξ ξ' u v : K} (h : ξ = ξ' * u * v) (JA : Matrix α α K) (JB : Matrix β β K) (x y : Matrix α β K) :
    symp c ξ' (u • JA) (v • JB) x y = symp c ξ JA JB x y := by
  rw [symp, symp, h]
  congr 1
  simp only [hTens, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

variable [Invertible (2 : R)]

theorem isWeilB_resc {ξ ξ' u v : K} (h : ξ = ξ' * u * v) (hv : IsUnit v) {JA JA' : Matrix α α K} {JB JB' : Matrix β β K}
    (hA : JA' = u • JA) (hB : JB' = v • JB) {κ : Type} [Fintype κ] {C : TestClass R} {ψ : AddChar R ℂ}
    {d : Darboux (symp c ξ JA JB) κ} {χ : Kˣ →* Circle} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (hW : IsWeilB c C ψ ξ JA JB d χ om) :
    ∃ (d' : Darboux (symp c ξ' JA' JB') κ) (om' : UG c JB' →* Module.End ℂ ((κ → R) → ℂ)), d'.e = d.e ∧
      IsWeilB c C ψ ξ' JA' JB' d' χ om' ∧ ∀ g : UG c JB, ∃ g' : UG c JB', g'.1 = g.1 ∧ om' g' = om g := by
  subst hA hB
  obtain ⟨hS, dd, omd, hdd, hSd, hR, hbox⟩ := hW
  have hU : UG c (v • JB) = UG c JB := ug_smul hv JB
  have hUd : UG c (dbl (v • JB)) = UG c (dbl JB) := by rw [dbl_smul]; exact ug_smul hv _
  refine ⟨⟨d.e, fun w w' => (symp_smul h JA JB w w').trans (d.form w w')⟩, om.comp (Subgroup.inclusion hU.le), rfl,
    ⟨⟨fun g => hS.pres _, fun g => hS.impl (Subgroup.inclusion hU.le g), fun g => hS.adm _⟩,
      ⟨dd.e, fun w w' => by rw [dbl_smul]; exact (symp_smul h JA _ w w').trans (dd.form w w')⟩,
      omd.comp (Subgroup.inclusion hUd.le), hdd,
      ⟨fun g => hSd.pres _, fun g => hSd.impl (Subgroup.inclusion hUd.le g), fun g => hSd.adm _⟩,
      fun l hl hinv p t hp => hR l hl hinv (Subgroup.inclusion hUd.le p) t hp,
      fun g gd hg => hbox (Subgroup.inclusion hU.le g) (Subgroup.inclusion hUd.le gd) hg⟩,
    fun g => ⟨Subgroup.inclusion hU.ge g, rfl, rfl⟩⟩

end Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_isQuad (hσ : IsCMExt F E σ) : ∃ δ : E, IsQuad σ δ := by
  obtain ⟨-, hc, h2, hτ⟩ := hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hi : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ, star_star])
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push Not at h
    refine IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_))
    have := hτ τ x
    rw [h] at this
    exact this.symm
  have h0 : x - σ x ≠ 0 := sub_ne_zero.2 hx.symm
  have ha : σ (x - σ x) = -(x - σ x) := by rw [map_sub, hi, neg_sub]
  have hl : LinearIndependent F ![(1 : E), x - σ x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg σ hst
    have h4 := hst
    rw [Algebra.smul_def, Algebra.smul_def] at h1 h4
    rw [map_add, map_mul, map_mul, σ.commutes, σ.commutes, map_one, ha, map_zero] at h1
    have h3 : algebraMap F E (s + s) = 0 := by
      rw [map_add]
      linear_combination h4 + h1
    have hs : s = 0 := add_self_eq_zero.1 ((map_eq_zero _).1 h3)
    rw [hs, zero_smul, zero_add] at hst
    exact ⟨hs, (smul_eq_zero.1 hst).resolve_right h0⟩
  refine ⟨x - σ x, h0.isUnit, ha, basisOfLinearIndependentOfCardEqFinrank hl (by simp [h2]), ?_, ?_⟩ <;>
    simp

theorem exists_ratCoord (h2 : Module.finrank F E = 2) {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    (hκ : Fintype.card κ = Fintype.card α * Fintype.card β)
    (e : Matrix α β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (he : ∀ x : Matrix α β E, ∃ y z : κ → F,
      e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ d₀ : Matrix α β E ≃ₗ[F] (κ → F) × (κ → F), ∀ x,
      e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)) := by
  choose y z h using he
  have inj := AdeleRing.algebraMap_injective (𝓞 F) F
  have hadd : ∀ a b : Matrix α β E, incM F (a + b) = incM F a + incM F b := fun a b => by
    ext i j; simp [incM]
  have hsm : ∀ (t : F) (a : Matrix α β E), incM F (t • a) = algebraMap F (AF F) t • incM F a := fun t a => by
    ext i j
    change (1 : AF F) ⊗ₜ[F] (t • a i j) = algebraMap F (AF F) t • ((1 : AF F) ⊗ₜ[F] a i j)
    rw [algebraMap_smul, TensorProduct.tmul_smul]
  let f : Matrix α β E →ₗ[F] (κ → F) × (κ → F) :=
    { toFun := fun x => (y x, z x)
      map_add' := fun a b => by
        have := h (a + b)
        rw [hadd, map_add, h, h] at this
        refine Prod.ext (funext fun i => inj ?_) (funext fun i => inj ?_)
        · simpa using (congrFun (congrArg Prod.fst this) i).symm
        · simpa using (congrFun (congrArg Prod.snd this) i).symm
      map_smul' := fun t a => by
        have := h (t • a)
        rw [hsm, map_smul, h] at this
        refine Prod.ext (funext fun i => inj ?_) (funext fun i => inj ?_)
        · exact (congrFun (congrArg Prod.fst this) i).symm.trans (map_mul (algebraMap F (AF F)) t (y a i)).symm
        · exact (congrFun (congrArg Prod.snd this) i).symm.trans (map_mul (algebraMap F (AF F)) t (z a i)).symm }
  have hf : Function.Injective f := fun a b hab => by
    have h1 : y a = y b := congrArg Prod.fst hab
    have h3 : z a = z b := congrArg Prod.snd hab
    have : incM F a = incM F b := e.injective (by rw [h, h, h1, h3])
    exact Matrix.map_injective (Algebra.TensorProduct.includeRight_injective inj) this
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ h2
  refine ⟨f.linearEquivOfInjective hf ?_, h⟩
  rw [Module.finrank_matrix, h2, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hκ]
  ring

theorem member (hσ : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {δ a b : E} (hq : IsQuad σ δ)
    (hab : -1 = δ * a * b) {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (hκ : Fintype.card κ = Fintype.card α * Fintype.card β) {JA : Matrix α α E} {JB : Matrix β β E}
    (hA : IsHerm σ (a • JA)) (hB : IsHerm σ (b • JB))
    {d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ}
    (hd : ∀ x : Matrix α β E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    {χ : Chr F E} (hχ : IsHecke F E χ) {om : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ)}
    (h : IsWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (g : UG (cA σ) (incM F JB)) (γ : Matrix β β E) (hg : (g.1 : Matrix β β (AE F E)) = incM F γ) :
    ∀ Φ ∈ schA F κ, thetaSum F (om g Φ) = thetaSum F Φ := by
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hsm : ∀ {ι : Type} (t : E) (J : Matrix ι ι E), incM F (t • J) = inclR (F := F) (AF F) t • incM F J := fun t J => by
    ext i j; simp [incM]
  obtain ⟨d', om', he, hW, hom⟩ := isWeilB_resc (ξ' := inclR (F := F) (AF F) δ)
    (by rw [← map_mul, ← map_mul, ← hab, map_neg, map_one]) (hb.isUnit.map (inclR (F := F) (AF F))) (hsm a JA) (hsm b JB) h
  obtain ⟨d₀, hd₀⟩ := exists_ratCoord hσ.2.2.1 hκ d.e hd
  obtain ⟨g', hg', e⟩ := hom g
  rw [← e]
  refine GlobalTheory.T.seesaw_theta_dual_pair F E σ δ α β κ (a • JA) (b • JB) ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 hq hA hB d' d₀
    (fun x => by rw [← hd₀, ← he]; rfl) χ om' (fun z u hu => ?_) hW g' ⟨γ, by rw [hg']; exact hg⟩
  have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  have : Nontrivial (AF F ⊗[F] E) := (Algebra.TensorProduct.includeRight_injective (A := AF F) (B := E)
    (algebraMap F (AF F)).injective).nontrivial
  have hz : z ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hu, TensorProduct.tmul_zero])
  rw [show u = Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 z hz) from Units.ext hu]
  exact hχ.2 _

omit [NumberField E] in
theorem rat_mat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {γ : UA σ J} (hγ : γ ∈ ratU σ J) :
    ∃ γ₀ : Matrix (Fin n) (Fin n) E, (γ.1 : Matrix (Fin n) (Fin n) (AE F E)) = incM F γ₀ := by
  obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
  exact ⟨g₀, by rw [← hg₀]; rfl⟩

end PositivityTheory.ThKF0.Resc

namespace PositivityTheory.ThKF0

open Resc

theorem darboux_coordinates_rational_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 → ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW → ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JW) co χX χW om → ∀ γ ∈ ratU σ JX, ∀ γ' ∈ ratU σ JW, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro F E _ _ _ _ _ σ hσ ψ hψ n d JX JW hX hXd hW hWd co hco χX χW hχX hχW om hom γ hγ γ' hγ' Φ hΦ
  obtain ⟨hB, d', hd', hA⟩ := hom.isWeilPair
  obtain ⟨g₀, hg₀⟩ := rat_mat hγ
  obtain ⟨g₀', hg₀'⟩ := rat_mat hγ'
  obtain ⟨δ, hq⟩ := exists_isQuad hσ
  have h0 : δ ≠ 0 := hq.unit.ne_zero
  have eX : IsHerm σ ((1 : E) • JX) := by rw [one_smul]; exact ⟨hX, hXd.isUnit⟩
  have eW : IsHerm σ ((-δ⁻¹) • JW) := by
    refine ⟨fun i j => by simp [hW i j, hq.anti], Ne.isUnit ?_⟩
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hWd
  have hco' : ∀ x : Matrix (Fin d) (Fin n) E, ∃ y z : Fin n × Fin d → F,
      d'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    have e : incM F x = (incM F xᵀ)ᵀ := rfl
    rw [e, hd']
    exact hco xᵀ
  have e : om (γ, γ') Φ = om.comp (MonoidHom.inl _ _) γ (om.comp (MonoidHom.inr _ _) γ' Φ) := by
    rw [← Module.End.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]
    simp
  rw [e, member hσ hψ hq (by field_simp) (by simp [Nat.mul_comm]) eW eX hco' hχW hA γ g₀ hg₀ _ (hB.1.pres γ' Φ hΦ)]
  exact member hσ hψ hq (by field_simp) (by simp) eX eW hco hχX hB γ' g₀' hg₀' Φ hΦ

end PositivityTheory.ThKF0
end
end

