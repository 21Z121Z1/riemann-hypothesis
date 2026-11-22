import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0004
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0008
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0003
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0007

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPhiA
section
noncomputable section

open Finset Matrix
open scoped ContDiff

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def smoothS (n : ℕ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  carrier := {F | ContDiffOn ℂ ∞ F (OmegaSet n)}
  add_mem' hF hG := hF.add hG
  zero_mem' := contDiffOn_const
  smul_mem' c _ hF := hF.const_smul c

private theorem isOpen_OmegaSet' : IsOpen (OmegaSet n) := by
  show IsOpen {z : Matrix (Fin n) (Fin n) ℂ | ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0}
  rw [Set.setOf_forall]
  refine isOpen_iInter_of_finite fun i => isOpen_ne_fun ?_ continuous_const
  show Continuous fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z
  by_cases h : (i : ℕ) + 1 ≤ n
  · have e : (fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z) =
        fun z => (z.submatrix (Fin.castLE h) (Fin.castLE h)).det := funext fun z => dif_pos h
    rw [e]
    exact (continuous_id.matrix_submatrix _ _).matrix_det
  · have e : (fun z : Matrix (Fin n) (Fin n) ℂ => lead ((i : ℕ) + 1) z) = fun _ => 0 :=
      funext fun z => dif_neg h
    rw [e]
    exact continuous_const

theorem lhol_congr {X : Matrix (Fin n) (Fin n) ℂ} {G H : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : Set.EqOn G H (OmegaSet n)) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Lhol X G z = Lhol X H z := by
  show fderiv ℂ G z (X * z) = fderiv ℂ H z (X * z)
  rw [Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (isOpen_OmegaSet'.mem_nhds hz) h)]

theorem lhol_mem {X : Matrix (Fin n) (Fin n) ℂ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaSet n)) : ContDiffOn ℂ ∞ (Lhol X F) (OmegaSet n) := by
  have h1 :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_OmegaSet').1 hF).2
  have h2 : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => X * z) := by
    refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
    simp only [Matrix.mul_apply]
    exact ContDiff.sum fun c _ => contDiff_const.mul (contDiff_pi.1 (contDiff_pi.1 contDiff_id c) b)
  exact h1.clm_apply h2.contDiffOn

def ltOp (X : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  (OmegaSet n).indicator (Lhol X F)

theorem ltOp_of_mem {X : Matrix (Fin n) (Fin n) ℂ} (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) : ltOp X F z = Lhol X F z := by
  exact Set.indicator_of_mem hz _

theorem ltOp_of_not_mem {X : Matrix (Fin n) (Fin n) ℂ} (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∉ OmegaSet n) : ltOp X F z = 0 := by
  simp [ltOp, hz]

theorem ltOp_mem {X : Matrix (Fin n) (Fin n) ℂ} {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaSet n)) : ContDiffOn ℂ ∞ (ltOp X F) (OmegaSet n) := by
  exact (lhol_mem hF).congr fun z hz => ltOp_of_mem F hz

theorem differentiableAt_of_mem {F : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hF : ContDiffOn ℂ ∞ F (OmegaSet n)) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    DifferentiableAt ℂ F z := by
  exact ((hF.differentiableOn (by simp <;> exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) z hz).differentiableAt (isOpen_OmegaSet'.mem_nhds hz)

def eOp (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (smoothS n) where
  toFun F := ⟨ltOp X F, ltOp_mem F.2⟩
  map_add' F G := by
    apply Subtype.ext
    funext z
    by_cases hz : z ∈ OmegaSet n
    · simp only [Submodule.coe_add, Pi.add_apply, ltOp_of_mem _ hz]
      show fderiv ℂ (F.1 + G.1) z (X * z) = fderiv ℂ F.1 z (X * z) + fderiv ℂ G.1 z (X * z)
      erw [((differentiableAt_of_mem F.2 hz).hasFDerivAt.add (differentiableAt_of_mem G.2 hz).hasFDerivAt).fderiv]
      rfl
    · simp only [Submodule.coe_add, Pi.add_apply, ltOp_of_not_mem _ hz, add_zero]
  map_smul' c F := by
    apply Subtype.ext
    funext z
    by_cases hz : z ∈ OmegaSet n
    · simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply, ltOp_of_mem _ hz]
      show fderiv ℂ (c • F.1) z (X * z) = c • fderiv ℂ F.1 z (X * z)
      erw [fderiv_const_smul (differentiableAt_of_mem F.2 hz)]
      rfl
    · simp only [SetLike.val_smul, Pi.smul_apply, RingHom.id_apply, ltOp_of_not_mem _ hz, smul_zero]

theorem eOp_apply (X : Matrix (Fin n) (Fin n) ℂ) (F : smoothS n) :
    ((eOp X F : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) = ltOp X F := rfl

theorem eOp_sub (X Y : Matrix (Fin n) (Fin n) ℂ) : eOp (X - Y) = eOp X - eOp Y := by
  apply LinearMap.ext
  intro F
  apply Subtype.ext
  funext z
  show ltOp (X - Y) F.1 z = ltOp X F.1 z - ltOp Y F.1 z
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz, ltOp_of_mem _ hz, ltOp_of_mem _ hz]
    show fderiv ℂ F.1 z ((X - Y) * z) = fderiv ℂ F.1 z (X * z) - fderiv ℂ F.1 z (Y * z)
    rw [Matrix.sub_mul, map_sub]
  · rw [ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, sub_zero]

theorem eOp_zero : eOp (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  apply LinearMap.ext; intro F
  apply Subtype.ext; funext z
  show ltOp 0 F z = 0
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz]
    show fderiv ℂ F.1 z (0 * z) = 0
    rw [Matrix.zero_mul, map_zero]
  · rw [ltOp_of_not_mem _ hz]

private theorem Lhol_commutator_on_OmegaSet {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : ContDiffOn ℂ ∞ F (OmegaSet n))
    (X Y : Matrix (Fin n) (Fin n) ℂ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    Lhol X (Lhol Y F) z - Lhol Y (Lhol X F) z = Lhol (Y * X - X * Y) F z := by
  have hc := hF.contDiffAt (isOpen_OmegaSet'.mem_nhds hz)
  have h1 := ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_OmegaSet').1 hF).2
  have hd := ((h1.differentiableOn (by simp <;> exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) z hz).differentiableAt
    (isOpen_OmegaSet'.mem_nhds hz) |>.hasFDerivAt
  have hs := hc.isSymmSndFDerivAt (by first | exact le_top | (simp; done) | (simp <;> exact (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤) : ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω))) | (simp <;> decide))
  let LX : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun w => X * w
      map_add' := fun a b => Matrix.mul_add X a b
      map_smul' := fun c a => Matrix.mul_smul X c a }
  let LY : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun w => Y * w
      map_add' := fun a b => Matrix.mul_add Y a b
      map_smul' := fun c a => Matrix.mul_smul Y c a }
  show fderiv ℂ (fun w => fderiv ℂ F w (LY w)) z (X * z) -
      fderiv ℂ (fun w => fderiv ℂ F w (LX w)) z (Y * z) = fderiv ℂ F z ((Y * X - X * Y) * z)
  erw [(hd.clm_apply LY.hasFDerivAt).fderiv, (hd.clm_apply LX.hasFDerivAt).fderiv]
  show fderiv ℂ F z (Y * (X * z)) + fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) -
      (fderiv ℂ F z (X * (Y * z)) + fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z)) = _
  rw [show fderiv ℂ (fderiv ℂ F) z (X * z) (Y * z) = fderiv ℂ (fderiv ℂ F) z (Y * z) (X * z) from
    hs (X * z) (Y * z)]
  rw [Matrix.sub_mul, map_sub, Matrix.mul_assoc, Matrix.mul_assoc]
  abel

theorem eOp_comm (X Y : Matrix (Fin n) (Fin n) ℂ) :
    eOp X * eOp Y - eOp Y * eOp X = eOp (Y * X - X * Y) := by
  apply LinearMap.ext; intro F
  apply Subtype.ext; funext z
  show ltOp X (ltOp Y F) z - ltOp Y (ltOp X F) z = ltOp (Y * X - X * Y) F z
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz, ltOp_of_mem _ hz, ltOp_of_mem _ hz,
      lhol_congr (fun w hw => ltOp_of_mem F hw) hz, lhol_congr (fun w hw => ltOp_of_mem F hw) hz]
    exact Lhol_commutator_on_OmegaSet F.2 X Y hz
  · rw [ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, ltOp_of_not_mem _ hz, sub_zero]

theorem isGlRep_eOp (X : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ)
    (hX : ∀ a b c d, X c d * X a b - X a b * X c d =
      (if b = c then X a d else 0) - (if d = a then X c b else 0)) :
    IsGlRep (fun a b => eOp (X a b)) := by
  intro a b c d
  rw [eOp_comm, hX a b c d, eOp_sub]
  split_ifs <;> simp [eOp_zero]

theorem opPow_eqOn (X Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (c : ℂ)
    (hY : ∀ a b, Y a b = c • X (σ a) (σ b)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n)
    (hFG : Set.EqOn F G (OmegaSet n)) (k : ℕ) (a b : Fin n) :
    Set.EqOn (opPow (fun a b => Lhol (Y a b)) k a b F)
      (fun z => c ^ k * ((ePow (fun a b => eOp (X a b)) k (σ a) (σ b) G : smoothS n) :
        Matrix (Fin n) (Fin n) ℂ → ℂ) z) (OmegaSet n) := by
  unfold ePow
  simp only [Bl.ThirdBlockLemmaA.goal1]
  induction k generalizing a b with
  | zero =>
    intro z hz
    by_cases hab : a = b
    · subst hab
      simp [opPow, Matrix.one_apply, hFG hz]
    · have hs : σ a ≠ σ b := fun h => hab (σ.injective h)
      simp [opPow, Matrix.one_apply, hab, hs]
  | succ k ih =>
    intro z hz
    have hterm : ∀ d, Lhol (Y a d) (opPow (fun a b => Lhol (Y a b)) k d b F) z =
        c ^ (k + 1) * ((eOp (X (σ a) (σ d)) ((((Matrix.of fun a b => eOp (X a b)) ^ k) (σ d) (σ b)) G) :
          smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
      intro d
      set g : smoothS n := (((Matrix.of fun a b => eOp (X a b)) ^ k) (σ d) (σ b)) G with hg
      rw [lhol_congr (ih d b) hz, eOp_apply, ltOp_of_mem _ hz]
      show fderiv ℂ (fun w => c ^ k * (g : Matrix (Fin n) (Fin n) ℂ → ℂ) w) z (Y a d * z) =
        c ^ (k + 1) * fderiv ℂ (g : Matrix (Fin n) (Fin n) ℂ → ℂ) z (X (σ a) (σ d) * z)
      erw [fderiv_const_mul (differentiableAt_of_mem g.2 hz) (c ^ k)]
      rw [hY a d, Matrix.smul_mul]
      show c ^ k * fderiv ℂ (g : Matrix (Fin n) (Fin n) ℂ → ℂ) z (c • (X (σ a) (σ d) * z)) = _
      rw [map_smul, smul_eq_mul]
      ring
    simp only [opPow, Finset.sum_apply]
    rw [Finset.sum_congr rfl fun d _ => hterm d, pow_succ' (Matrix.of fun a b => eOp (X a b)) k,
      Matrix.mul_apply]
    simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply, Module.End.mul_apply,
      Matrix.of_apply, Finset.mul_sum]
    exact Fintype.sum_equiv σ _ _ (fun d => rfl)

theorem opGelfand_eq (X Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) (c : ℂ)
    (hY : ∀ a b, Y a b = c • X (σ a) (σ b)) (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (G : smoothS n)
    (hFG : Set.EqOn F G (OmegaSet n)) (k : ℕ) {z : Matrix (Fin n) (Fin n) ℂ} (hz : z ∈ OmegaSet n) :
    opGelfand (fun a b => Lhol (Y a b)) k F z =
      c ^ k * ((gelfand (fun a b => eOp (X a b)) k G : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) z := by
  simp only [opGelfand, gelfand, Finset.sum_apply, LinearMap.sum_apply, Submodule.coe_sum,
    Finset.mul_sum]
  exact Fintype.sum_equiv σ (fun a => opPow (fun a b => Lhol (Y a b)) k a a F z)
    (fun a => c ^ k * ((ePow (fun a b => eOp (X a b)) k a a G : smoothS n) :
      Matrix (Fin n) (Fin n) ℂ → ℂ) z)
    fun a => opPow_eqOn X Y σ c hY F G hFG k a a hz

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.TauPart
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def upPart (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if a < b then B a b else 0

def lowPart (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if b < a then B a b else 0

def diagPart (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun a => B a a

lemma decomp_up (B : Matrix (Fin n) (Fin n) ℂ) :
    B = lowMinusUp B + (2 : ℂ) • upPart B + diagPart B := by
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, lowMinusUp, upPart, diagPart, Matrix.of_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg (lt_asymm h), if_pos h, if_pos h, if_neg h.ne]
    ring
  · simp
  · rw [if_pos h, if_neg (lt_asymm h), if_neg h.ne']
    ring

lemma decomp_low (B : Matrix (Fin n) (Fin n) ℂ) :
    B = -lowMinusUp B + (2 : ℂ) • lowPart B + diagPart B := by
  ext a b
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, lowMinusUp, lowPart, diagPart,
    Matrix.of_apply, Matrix.diagonal_apply, smul_eq_mul]
  rcases lt_trichotomy a b with h | rfl | h
  · rw [if_neg (lt_asymm h), if_pos h, if_neg (lt_asymm h), if_neg h.ne]
    ring
  · simp
  · rw [if_pos h, if_pos h, if_neg h.ne']
    ring

lemma single_eq_smul (a b : Fin n) (c : ℂ) :
    Matrix.single a b c = c • Matrix.single a b (1 : ℂ) := by
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

lemma dtau_upPart_w (T : KType ε Λ) {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsBlock ε B) :
    T.dτ (upPart B) T.w = 0 := by
  rw [Matrix.matrix_eq_sum_single (upPart B), map_sum, _root_.sum_apply]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  rw [map_sum, _root_.sum_apply]
  refine Finset.sum_eq_zero (fun b _ => ?_)
  rw [single_eq_smul, map_smul, ContinuousLinearMap.smul_apply]
  simp only [upPart, Matrix.of_apply]
  split_ifs with h
  · by_cases he : ε a = ε b
    · rw [T.w_hw a b h he, smul_zero]
    · rw [hB a b he, zero_smul]
  · rw [zero_smul]

lemma dtau_diagPart_w (T : KType ε Λ) (B : Matrix (Fin n) (Fin n) ℂ) :
    T.dτ (diagPart B) T.w = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • T.w := by
  rw [Matrix.matrix_eq_sum_single (diagPart B), map_sum, _root_.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_sum, _root_.sum_apply, Finset.sum_eq_single a]
  · rw [single_eq_smul, map_smul, ContinuousLinearMap.smul_apply, T.w_wt, smul_smul]
    simp only [diagPart, Matrix.diagonal_apply_eq]
    rw [mul_comm]
  · intro b _ hb
    rw [single_eq_smul, map_smul, ContinuousLinearMap.smul_apply]
    simp only [diagPart, Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    rw [zero_smul]
  · intro h
    exact absurd (Finset.mem_univ a) h

lemma isBlock_lowPart {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsBlock ε B) : IsBlock ε (lowPart B) := by
  intro a b h
  simp only [lowPart, Matrix.of_apply]
  split_ifs
  · exact hB a b h
  · rfl

lemma isBlock_diagPart (B : Matrix (Fin n) (Fin n) ℂ) : IsBlock ε (diagPart B) := by
  intro a b h
  have hab : a ≠ b := by
    rintro rfl
    exact h rfl
  simp only [diagPart]
  exact Matrix.diagonal_apply_ne _ hab

lemma lowPart_conjTranspose {B : Matrix (Fin n) (Fin n) ℂ} (hBh : Bᴴ = B) :
    (lowPart B)ᴴ = upPart B := by
  ext a b
  simp only [Matrix.conjTranspose_apply, lowPart, upPart, Matrix.of_apply]
  split_ifs
  · have h := congrFun (congrFun hBh a) b
    rw [Matrix.conjTranspose_apply] at h
    exact h
  · exact star_zero _

lemma diagPart_conjTranspose {B : Matrix (Fin n) (Fin n) ℂ} (hBh : Bᴴ = B) :
    (diagPart B)ᴴ = diagPart B := by
  ext a b
  rw [Matrix.conjTranspose_apply]
  simp only [diagPart]
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq]
    have h' := congrFun (congrFun hBh a) a
    rw [Matrix.conjTranspose_apply] at h'
    exact h'
  · rw [Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h, star_zero]

theorem tau_part {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) {B : Matrix (Fin n) (Fin n) ℂ}
    (hB : IsBlock ε B) (hBh : Bᴴ = B) :
    T.dτ B * projW T + projW T * T.dτ B =
      (T.dτ (lowMinusUp B) * projW T - projW T * T.dτ (lowMinusUp B)) +
        (2 * ∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
  have hP : ∀ v, projW T v = inner ℂ T.w v • T.w := fun v => by
    simp only [projW, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  have hBaa : ∀ a, (starRingEnd ℂ) (B a a) = B a a := fun a => by
    have h := congrFun (congrFun hBh a) a
    rw [Matrix.conjTranspose_apply] at h
    exact h
  have hc : (starRingEnd ℂ) (∑ a, ((Λ a : ℝ) : ℂ) * B a a) = ∑ a, ((Λ a : ℝ) : ℂ) * B a a := by
    simp only [map_sum, map_mul, Complex.conj_ofReal, hBaa]
  have h1 : T.dτ (upPart B) * projW T = 0 := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, map_smul, dtau_upPart_w T hB, smul_zero,
      ContinuousLinearMap.zero_apply]
  have h2 : T.dτ (diagPart B) * projW T = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, map_smul, dtau_diagPart_w, ContinuousLinearMap.smul_apply,
      hP, smul_comm]
  have h3 : projW T * T.dτ (lowPart B) = 0 := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, ← ContinuousLinearMap.adjoint_inner_left,
      dtau_adj T (isBlock_lowPart hB), lowPart_conjTranspose hBh, dtau_upPart_w T hB, inner_zero_left,
      zero_smul, ContinuousLinearMap.zero_apply]
  have h4 : projW T * T.dτ (diagPart B) = (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    ext v
    rw [ContinuousLinearMap.mul_apply, hP, ← ContinuousLinearMap.adjoint_inner_left,
      dtau_adj T (isBlock_diagPart B), diagPart_conjTranspose hBh, dtau_diagPart_w, inner_smul_left, hc,
      ContinuousLinearMap.smul_apply, hP, mul_smul]
  have eB1 : T.dτ B = T.dτ (lowMinusUp B) + (2 : ℂ) • T.dτ (upPart B) + T.dτ (diagPart B) := by
    conv_lhs => rw [decomp_up B]
    rw [map_add, map_add, map_smul]
  have eB2 : T.dτ B = -T.dτ (lowMinusUp B) + (2 : ℂ) • T.dτ (lowPart B) + T.dτ (diagPart B) := by
    conv_lhs => rw [decomp_low B]
    rw [map_add, map_add, map_smul, map_neg]
  have hL : T.dτ B * projW T =
      T.dτ (lowMinusUp B) * projW T + (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    rw [eB1, add_mul, add_mul, smul_mul_assoc, h1, smul_zero, add_zero, h2]
  have hR : projW T * T.dτ B =
      -(projW T * T.dτ (lowMinusUp B)) + (∑ a, ((Λ a : ℝ) : ℂ) * B a a) • projW T := by
    rw [eB2, mul_add, mul_add, mul_smul_comm, h3, smul_zero, add_zero, h4, mul_neg]
  rw [hL, hR, two_mul, add_smul]
  abel

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

