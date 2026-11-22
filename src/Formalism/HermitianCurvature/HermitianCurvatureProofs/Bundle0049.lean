import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0044
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SeminormCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.Bundle0004

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.SandwichRhoAction Formalism.FourierDecayAlt.P.ChartIntegralLocal

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma ckOn_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (m : ℕ∞) :
    CkOn m (GV k r) (fun _ : Mat k r => (0 : E)) := fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

lemma dLR_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (u v : List (Mat k r)) :
    dLR u v (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
  have hR : ∀ w : List (Mat k r), Rw w (fun _ : Mat k r => (0 : E)) = fun _ => 0 := by
    intro w
    induction w with
    | nil => rfl
    | cons X w ih =>
      show RdV X (Rw w _) = _
      rw [ih]
      funext g
      simp only [RdV, deriv_const']
  induction u with
  | nil => exact hR v
  | cons X u ih =>
    show LdV X (dLR u v _) = _
    rw [ih]
    funext g
    simp only [LdV, deriv_const']

lemma norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mat k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [Complex.norm_exp]
  simp

lemma isOpen_OmPlus (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Formalism.FourierDecayAlt.Q.OmPlus k r z z') := by
  have e : Formalism.FourierDecayAlt.Q.OmPlus k r z z' =
      (⋂ l : Fin (r + 2), {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0}) ∩ {g | 0 < Gf k r z z' g} := by
    ext g; simp [Formalism.FourierDecayAlt.Q.OmPlus]
  rw [e]
  refine (isOpen_iInter_of_finite fun l => ?_).inter
    (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Ux8.cont_Gf k r z z'))
  by_cases hl : l.val ≤ r
  · have e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = {g | Dmin k r z z' g l ≠ 0} := by
      ext g; simp [hl]
    rw [e2]; exact isOpen_ne_fun (Formalism.FourierDecayAlt.P.Ux8.cont_Dmin k r z z' l) continuous_const
  · have e2 : {g : Mat k r | l.val ≤ r → Dmin k r z z' g l ≠ 0} = Set.univ := by
      ext g; simp [hl]
    rw [e2]; exact isOpen_univ

lemma cv_continuous (b : Bool) (X g : Mat k r) : Continuous fun t : ℝ => cv b X t g := by
  cases b
  · exact (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  · have h := (Formalism.FourierDecayAlt.P.B5.curve_contDiff (1 : Mat k r) (-X)).continuous
    have h2 := (continuous_mul_const g).comp h
    refine h2.congr fun t => ?_
    simp [cv, smul_neg]

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma norm_xiP (D : RealPlaceData k r Wp Wq) (p : SS k r) : ‖xiP D p‖ ≤ 1 := by
  unfold xiP
  simp [norm_psi]

lemma continuous_xiP (D : RealPlaceData k r Wp Wq) : Continuous (xiP D) := by
  have key : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => ell k r z (Matrix.of M) := by
    intro z
    unfold ell
    refine continuous_finset_sum _ fun a _ => ?_
    by_cases h : a.val + 1 < r
    · simp only [h, ↓reduceDIte, Matrix.of_apply]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [h, ↓reduceDIte, Matrix.mulVec, dotProduct, Matrix.of_apply]
      refine continuous_finset_sum _ fun j _ => ?_
      first
        | fun_prop
        | exact (((continuous_apply j).comp (continuous_apply (eI k r a))).mul continuous_const :)
        | continuity
  have hpsi : ∀ z : Fin (2 * r + k + 1) → ℂ, Continuous fun M : Mt k r => psi k r z cStd (Matrix.of M) := by
    intro z
    unfold psi
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp (continuous_const.mul (key z)))))
  unfold xiP
  exact ((hpsi D.z).comp (continuous_snd.comp continuous_fst)).mul
    (continuous_star.comp ((hpsi D.z').comp (continuous_snd.comp continuous_snd)))

lemma ckOn_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ∞} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn m (GV k r) F) : CkOn m (GV k r) (rho D p F) := by
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GV k r :=
    WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hp.1.1) (WeylGroupFacts.uh_inv hp.2.1.1)
  have hb : Matrix.of p.2.2 * Matrix.of p.2.1 ∈ GV k r := WeylGroupFacts.uh_mul hp.2.2.2.1 hp.2.2.1.1
  have e : rho D p F = fun x => ((ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp
      ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹)))
      (F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * x * (Matrix.of p.2.2 * Matrix.of p.2.1))) := by
    funext x
    simp only [rho, sgs, Matrix.mul_assoc]
    rfl
  rw [e]
  exact Formalism.FourierDecayAlt.P.B5.ckOn_clm (Formalism.FourierDecayAlt.P.B5.ckOn_translate hF ha hb) _

lemma ckOn_dLR_rho (D : RealPlaceData k r Wp Wq) {p : SS k r} (hp : D.inSS p) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)}
    (hF : CkOn (m : ℕ∞) (GV k r) F) {u v : List (Mat k r)} (hu : ∀ X ∈ u, unitLie k r X)
    (hv : ∀ X ∈ v, unitLie k r X) (j : ℕ) (hl : j + (u.length + v.length) ≤ m) :
    CkOn ((j : ℕ) : ℕ∞) (GV k r) (dLR u v (rho D p F)) := by
  rw [dLR_eq]
  exact smooth_on_of_word_derivatives _ (allLie_lr hu hv) j (ckOn_mono (by rw [length_lr]; omega) (ckOn_rho D hp hF))

lemma good_set (D : RealPlaceData k r Wp Wq) {m : ℕ} {F : Mat k r → (Wq →L[ℂ] Wp)} (hF : CkOn (m : ℕ∞) (GV k r) F)
    {K : Set (Mat k r)} (hK : IsCompact K) (hKG : K ⊆ GV k r)
    {WS : Set (List (Mat k r) × List (Mat k r))} (hWS : WS.Countable)
    (hWSl : ∀ uv ∈ WS, (∀ X ∈ uv.1, unitLie k r X) ∧ (∀ X ∈ uv.2, unitLie k r X) ∧ uv.1.length + uv.2.length ≤ m)
    (b : SS k r → ℝ)
    (hb : ∀ uv ∈ WS, ∀ g ∈ K, ∀ᵐ p ∂D.μSS, ‖rho D p (dLR (uv.1.map (AdL p)) (uv.2.map (AdR p)) F) g‖ ≤ b p) :
    ∀ᵐ p ∂D.μSS, D.inSS p ∧ ∀ uv ∈ WS, ∀ g ∈ K, ‖dLR uv.1 uv.2 (rho D p F) g‖ ≤ b p := by
  haveI : TopologicalSpace.PseudoMetrizableSpace (Mat k r) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ))
  obtain ⟨S, hSK, hSc, hKS⟩ := hK.isSeparable.exists_countable_dense_subset
  haveI := hWS.to_subtype
  haveI := hSc.to_subtype
  have hall : ∀ᵐ p ∂D.μSS, ∀ i : WS × S,
      ‖rho D p (dLR (i.1.1.1.map (AdL p)) (i.1.1.2.map (AdR p)) F) i.2.1‖ ≤ b p :=
    ae_all_iff.2 fun i => hb i.1.1 i.1.2 i.2.1 (hSK i.2.2)
  filter_upwards [hall, Formalism.FourierDecayAlt.P.B7.ae_inSS D] with p hp hpS
  refine ⟨hpS, fun uv huv g hg => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hWSl uv huv
  have hcont : ContinuousOn (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) (GV k r) :=
    (Formalism.FourierDecayAlt.P.B5.ckOn_continuousOn (ckOn_dLR_rho D hpS hF h1 h2 0 (by omega))).norm
  have hcl : IsClosed (GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p)) :=
    hcont.preimage_isClosed_of_isClosed Formalism.FourierDecayAlt.P.B5.GV_closed isClosed_Iic
  have hS : S ⊆ GV k r ∩ (fun x => ‖dLR uv.1 uv.2 (rho D p F) x‖) ⁻¹' Set.Iic (b p) := by
    intro x hx
    refine ⟨hKG (hSK hx), ?_⟩
    show ‖dLR uv.1 uv.2 (rho D p F) x‖ ≤ b p
    rw [dLR_rho D hpS]
    exact hp ⟨⟨uv, huv⟩, ⟨x, hx⟩⟩
  exact (hcl.closure_subset_iff.2 hS (hKS hg)).2

lemma curve_ball (D : RealPlaceData k r Wp Wq) {g : Mat k r} (hg : g ∈ Om k r D.z D.z') (b : Bool) {X : Mat k r}
    (hX : inLie k r X) : ∃ ε > 0, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, cv b X t g ∈ Om k r D.z D.z' := by
  have hopen : IsOpen ((fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z') :=
    (isOpen_OmPlus _ _).preimage (cv_continuous b X g)
  have h0 : (0 : ℝ) ∈ (fun t : ℝ => cv b X t g) ⁻¹' Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := by
    show cv b X 0 g ∈ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z'
    rw [cv_zero]; exact hg.2
  obtain ⟨ε1, hε1, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0
  have hg' : g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z' := hg
  refine ⟨ε1 / 2, by linarith, fun t ht => (⟨cv_mem hX hg'.1 t, hball ?_⟩ : cv b X t g ∈ GV k r ∩ Formalism.FourierDecayAlt.Q.OmPlus k r D.z D.z')⟩
  rw [Metric.mem_closedBall] at ht
  rw [Metric.mem_ball]
  linarith

end Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SplLen
section
open Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma dif {E₁ F₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    {f : E₁ → F₁} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f := by
  exact hf.differentiable (by simp)

lemma hdx (x : Bool × Mat k r) {f : Mat k r → E} (hf : Differentiable ℝ f) (g : Mat k r) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (fderiv ℝ f g (dirv x g)) 0 := by
  have hd : HasFDerivAt f (fderiv ℝ f g) (crv x g 0) := by
    rw [crv_zero]
    exact (hf g).hasFDerivAt
  exact hd.comp_hasDerivAt 0 (crv_hasDerivAt x g)

private theorem dx_eq_deriv_crv (x : Bool × Mat k r) (f : Mat k r → E) (g : Mat k r) :
    Dx x f g = deriv (fun t : ℝ => f (crv x g t)) 0 := by
  rcases x with ⟨b, X⟩
  cases b <;> rfl

private theorem dirL_eq_dirv (x : Bool × Mat k r) (g : Mat k r) : dirL x g = dirv x g := by
  rcases x with ⟨b, X⟩
  cases b <;> first | rfl | simp [dirL, dirv]

lemma dx_fd (x : Bool × Mat k r) {f : Mat k r → E} (hf : Differentiable ℝ f) :
    Dx x f = fun g => fderiv ℝ f g (dirL x g) := by
  funext g
  rw [dx_eq_deriv_crv, (hdx x hf g).deriv, dirL_eq_dirv]

lemma cdx (x : Bool × Mat k r) {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dx x f) := by
  rw [dx_fd x (dif hf)]
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply (dirL x).contDiff

lemma cdw (w : List (Bool × Mat k r)) {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dw w f) := by
  induction w with
  | nil => simpa [Dw] using hf
  | cons a w ih => simpa [Dw] using cdx a ih

lemma dx_add (x : Bool × Mat k r) {a b : Mat k r → E} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Dx x (fun g => a g + b g) = fun g => Dx x a g + Dx x b g := by
  rw [dx_fd x (f := fun g => a g + b g) (ha.add hb), dx_fd x ha, dx_fd x hb]
  funext g
  exact congrArg (fun T => T (dirL x g)) (fderiv_add (ha g) (hb g))

lemma dw_add (w : List (Bool × Mat k r)) {a b : Mat k r → E} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    Dw w (fun g => a g + b g) = fun g => Dw w a g + Dw w b g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => a g + b g) = fun g => Dx x (Dw w a) g + Dx x (Dw w b) g
    rw [ih]
    exact dx_add x (dif (cdw w ha)) (dif (cdw w hb))

lemma dx_clm {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] (L : E →L[ℝ] E₂) (x : Bool × Mat k r)
    {f : Mat k r → E} (hf : Differentiable ℝ f) : Dx x (fun g => L (f g)) = fun g => L (Dx x f g) := by
  rw [dx_fd x (f := fun g => L (f g)) (L.differentiable.comp hf), dx_fd x hf]
  funext g
  have h := (L.hasFDerivAt.comp g (hf g).hasFDerivAt).fderiv
  rw [show (fun g => L (f g)) = ⇑L ∘ f from rfl]
  exact congrArg (fun T => T (dirL x g)) h

lemma dw_clm {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] (L : E →L[ℝ] E₂) (w : List (Bool × Mat k r))
    {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) : Dw w (fun g => L (f g)) = fun g => L (Dw w f g) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => L (f g)) = fun g => L (Dx x (Dw w f) g)
    rw [ih]
    exact dx_clm L x (dif (cdw w hf))

section app

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma dx_app (x : Bool × Mat k r) {a : Mat k r → (F →L[ℝ] E)} {b : Mat k r → F} (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) :
    Dx x (fun g => a g (b g)) = fun g => Dx x a g (b g) + a g (Dx x b g) := by
  rw [dx_fd x (ha.clm_apply hb), dx_fd x ha, dx_fd x hb]
  funext g
  have h2 := congrArg (fun T => T (dirL x g)) (fderiv_clm_apply (ha g) (hb g))
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at h2
  exact h2.trans (add_comm _ _)

lemma cd_app {a : Mat k r → (F →L[ℝ] E)} {b : Mat k r → F} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    ContDiff ℝ ∞ (fun g => a g (b g)) := ha.clm_apply hb

private lemma dw_append_singleton' {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E'] (w : List (Bool × Mat k r))
    (x : Bool × Mat k r) (f : Mat k r → E') : Dw (w ++ [x]) f = Dw w (Dx x f) := by
  unfold Dw
  rw [List.foldr_append]
  rfl

lemma leibA (g : Mat k r) (M : ℝ) (w : List (Bool × Mat k r)) :
    ∀ (a : Mat k r → (F →L[ℝ] E)) (b : Mat k r → F), ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      (∀ w₁ w₂, Spl w w₁ w₂ → ‖Dw w₁ a g‖ * ‖Dw w₂ b g‖ ≤ M) →
      ‖Dw w (fun g => a g (b g)) g‖ ≤ 2 ^ w.length * M := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a b ha hb h
    have h0 := h [] [] ⟨List.Sublist.slnil, List.Sublist.slnil, List.Perm.nil⟩
    simp only [Dw, List.foldr_nil, List.length_nil, pow_zero, one_mul] at h0 ⊢
    exact (ContinuousLinearMap.le_opNorm _ _).trans h0
  | append_singleton w x ih =>
    intro a b ha hb h
    have splL : ∀ {w₁ w₂ : List (Bool × Mat k r)}, Spl w w₁ w₂ → Spl (w ++ [x]) (w₁ ++ [x]) w₂ := by
      intro w₁ w₂ hs
      refine ⟨hs.1.append (List.Sublist.refl [x]), hs.2.1.trans (List.sublist_append_left w [x]), ?_⟩
      have hp : (w₁ ++ [x] ++ w₂).Perm (w₁ ++ w₂ ++ [x]) := by
        simpa [List.append_assoc] using (List.perm_append_comm (l₁ := [x]) (l₂ := w₂)).append_left w₁
      exact hp.trans (hs.2.2.append_right [x])
    have splR : ∀ {w₁ w₂ : List (Bool × Mat k r)}, Spl w w₁ w₂ → Spl (w ++ [x]) w₁ (w₂ ++ [x]) := by
      intro w₁ w₂ hs
      refine ⟨hs.1.trans (List.sublist_append_left w [x]), hs.2.1.append (List.Sublist.refl [x]), ?_⟩
      rw [← List.append_assoc]
      exact hs.2.2.append_right [x]
    have h1 : ‖Dw w (fun g => Dx x a g (b g)) g‖ ≤ 2 ^ w.length * M :=
      ih (Dx x a) b (cdx x ha) hb fun w₁ w₂ hs => by
        have h' := h (w₁ ++ [x]) w₂ (splL hs)
        rwa [dw_append_singleton'] at h'
    have h2 : ‖Dw w (fun g => a g (Dx x b g)) g‖ ≤ 2 ^ w.length * M :=
      ih a (Dx x b) ha (cdx x hb) fun w₁ w₂ hs => by
        have h' := h w₁ (w₂ ++ [x]) (splR hs)
        rwa [dw_append_singleton'] at h'
    rw [dw_append_singleton', dx_app x (dif ha) (dif hb), dw_add w (cd_app (cdx x ha) hb) (cd_app ha (cdx x hb))]
    beta_reduce
    refine (norm_add_le _ _).trans ?_
    rw [List.length_append, List.length_singleton, pow_succ]
    linarith

lemma dx_comp (x : Bool × Mat k r) {ψ : Mat k r → F} {Φ : F → E} (hψ : Differentiable ℝ ψ)
    (hΦ : Differentiable ℝ Φ) : Dx x (fun g => Φ (ψ g)) = fun g => fderiv ℝ Φ (ψ g) (Dx x ψ g) := by
  rw [dx_fd x (f := fun g => Φ (ψ g)) (hΦ.comp hψ), dx_fd x hψ]
  funext g
  rw [show (fun g => Φ (ψ g)) = Φ ∘ ψ from rfl]
  exact congrArg (fun T => T (dirL x g)) (fderiv_comp g (hΦ (ψ g)) (hψ g))

lemma spl_len {w w₁ w₂ : List (Bool × Mat k r)} (h : Spl w w₁ w₂) : w₁.length + w₂.length = w.length := by
  obtain ⟨-, -, hp⟩ := h
  rw [← List.length_append]
  exact hp.length_eq

private theorem adm_of_sublist {n : ℕ} {w w' : List (Bool × Mat k r)} (h : admitted n w)
    (hw : w'.Sublist w) : admitted n w' := by
  obtain ⟨u, v, hu, hv, hlen, rfl⟩ := h
  obtain ⟨l₁, l₂, rfl, h1, h2⟩ := List.sublist_append_iff.1 hw
  unfold wL at h1
  unfold wR at h2
  obtain ⟨u', hu', rfl⟩ := List.sublist_map_iff.1 h1
  obtain ⟨v', hv', rfl⟩ := List.sublist_map_iff.1 h2
  exact ⟨u', v', fun X hX => hu X (hu'.subset hX), fun X hX => hv X (hv'.subset hX),
    by have := hu'.length_le; have := hv'.length_le; omega, rfl⟩

theorem fdb (ψ : Mat k r → F) (hψ : ContDiff ℝ ∞ ψ) (S : Set (Mat k r)) (K : Set F) (hK : ∀ g ∈ S, ψ g ∈ K)
    (Y : Mat k r → ℝ) (hY : ∀ g ∈ S, 1 ≤ Y g) (α β : ℕ) (M : ℝ) (n : ℕ)
    (H : ∀ w, admitted n w → w ≠ [] → ∀ g ∈ S, ‖Dw w ψ g‖ ≤ M * Y g ^ (α * w.length + β)) :
    ∀ m : ℕ, ∀ (E₁ : Type) [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] (Φ : F → E₁), ContDiff ℝ ∞ Φ →
      (∀ j : ℕ, ∃ B : ℝ, ∀ y ∈ K, ‖iteratedFDeriv ℝ j Φ y‖ ≤ B) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ w, admitted n w → w.length ≤ m → ∀ g ∈ S,
        ‖Dw w (fun g => Φ (ψ g)) g‖ ≤ C * Y g ^ ((α + β) * w.length) := by
  intro m
  induction m with
  | zero =>
    intro E₁ _ _ Φ hΦ hB
    obtain ⟨B0, hB0⟩ := hB 0
    refine ⟨max B0 0, le_max_right _ _, fun w _ hw g hg => ?_⟩
    have hw0 : w = [] := List.length_eq_zero_iff.1 (by omega)
    subst hw0
    simp only [Dw, List.foldr_nil, List.length_nil, mul_zero, pow_zero, mul_one]
    have h0 := hB0 (ψ g) (hK g hg)
    rw [norm_iteratedFDeriv_zero] at h0
    exact h0.trans (le_max_left _ _)
  | succ m ih =>
    intro E₁ _ _ Φ hΦ hB
    obtain ⟨C', hC'0, hC'⟩ := ih (F →L[ℝ] E₁) (fderiv ℝ Φ) (hΦ.fderiv_right (m := ∞) (by simp))
      (fun j => by
        obtain ⟨B, hB'⟩ := hB (j + 1)
        exact ⟨B, fun y hy => by rw [norm_iteratedFDeriv_fderiv]; exact hB' y hy⟩)
    obtain ⟨B0, hB0⟩ := hB 0
    have hM' : 0 ≤ max M 0 := le_max_right _ _
    refine ⟨max B0 0 + 2 ^ m * (C' * max M 0),
      add_nonneg (le_max_right _ _) (mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg hC'0 hM')),
      fun w hwA hw g hg => ?_⟩
    have hY1 := hY g hg
    have hY0 : 0 ≤ Y g := by linarith
    have hrest : 0 ≤ 2 ^ m * (C' * max M 0) :=
      mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg hC'0 hM')
    rcases List.eq_nil_or_concat w with rfl | ⟨w', x, rfl⟩
    · simp only [Dw, List.foldr_nil, List.length_nil, mul_zero, pow_zero, mul_one]
      have h0 := hB0 (ψ g) (hK g hg)
      rw [norm_iteratedFDeriv_zero] at h0
      linarith [le_max_left B0 0]
    · rw [List.concat_eq_append] at hwA hw ⊢
      rw [dw_append_singleton', dx_comp x (dif hψ) (dif hΦ)]
      have hlen : w'.length ≤ m := by
        rw [List.length_append, List.length_singleton] at hw
        omega
      have key := leibA g (C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1))) w'
        (fun g => fderiv ℝ Φ (ψ g)) (Dx x ψ) ((hΦ.fderiv_right (m := ∞) (by simp)).comp hψ) (cdx x hψ)
        (fun w₁ w₂ hs => by
          have hl := spl_len hs
          have h1 : ‖Dw w₁ (fun g => fderiv ℝ Φ (ψ g)) g‖ ≤ C' * Y g ^ ((α + β) * w₁.length) :=
            hC' w₁ (adm_of_sublist hwA (hs.1.trans (List.sublist_append_left _ _))) (by omega) g hg
          have h2 : ‖Dw w₂ (Dx x ψ) g‖ ≤ max M 0 * Y g ^ (α * (w₂ ++ [x]).length + β) := by
            rw [← dw_append_singleton']
            exact (H (w₂ ++ [x]) (adm_of_sublist hwA (hs.2.1.append_right [x])) (by simp) g hg).trans
              (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hY0 _))
          have hexp : (α + β) * w₁.length + (α * (w₂ ++ [x]).length + β) ≤
              (α + β) * (w'.length + 1) := by
            rw [List.length_append, List.length_singleton]
            nlinarith
          calc ‖Dw w₁ (fun g => fderiv ℝ Φ (ψ g)) g‖ * ‖Dw w₂ (Dx x ψ) g‖
              ≤ (C' * Y g ^ ((α + β) * w₁.length)) * (max M 0 * Y g ^ (α * (w₂ ++ [x]).length + β)) :=
                mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC'0 (pow_nonneg hY0 _))
            _ = C' * max M 0 * Y g ^ ((α + β) * w₁.length + (α * (w₂ ++ [x]).length + β)) := by
                rw [pow_add]
                ring
            _ ≤ C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1)) :=
                mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 hexp) (mul_nonneg hC'0 hM'))
      have hP : 0 ≤ C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1)) :=
        mul_nonneg (mul_nonneg hC'0 hM') (pow_nonneg hY0 _)
      calc _ ≤ 2 ^ w'.length * (C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1))) := key
        _ ≤ 2 ^ m * (C' * max M 0 * Y g ^ ((α + β) * (w'.length + 1))) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) hP
        _ ≤ (max B0 0 + 2 ^ m * (C' * max M 0)) * Y g ^ ((α + β) * (w' ++ [x]).length) := by
            rw [List.length_append, List.length_singleton]
            have : 0 ≤ max B0 0 * Y g ^ ((α + β) * (w'.length + 1)) :=
              mul_nonneg (le_max_right _ _) (pow_nonneg hY0 _)
            nlinarith

end app

end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

