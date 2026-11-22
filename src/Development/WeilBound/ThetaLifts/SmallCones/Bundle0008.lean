import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.ThetaLifts.SmallCones.Bundle0006
import Development.WeilBound.ThetaLifts.SmallCones.ExpAlg
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.Bundle0001

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.ConeLawAB
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cA_cA (hσ : IsCMExt F E σ) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp [cA, cm_conj_conj hσ]
  | add a b ha hb => simp [ha, hb]

theorem chi_conj (hσ : IsCMExt F E σ) {χ : Chr F E} {k : ℕ}
    (h : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ k) (t : (AE F E)ˣ) :
    χ (GlobalTheory.Doubling.conjUnit σ t) = (χ t)⁻¹ := by
  have h1 := h (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t)
  rw [if_pos (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨t, rfl⟩)), Circle.coe_eq_one,
    show Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) (Units.map (Algebra.norm (AF F) : AE F E →* AF F) t) =
      t * GlobalTheory.Doubling.conjUnit σ t from Units.ext (GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := AF F) t.1), map_mul] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem conjUnit_val (t : (AE F E)ˣ) : (GlobalTheory.Doubling.conjUnit σ t : (AE F E)ˣ).1 = cA σ t.1 := rfl

section

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E} {M : Model σ X W}
  {om : Rep σ X W} {om₀ : Rep σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {χX χW : Chr F E}
  {r s r' s' : ℕ} {rX rW : ℝ}

theorem isLevi_inv' {t h₁ p} (h : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' t h₁ p) :
    mat p⁻¹ *ᵥ incV F H'.x = (t⁻¹ : (AE F E)ˣ).1 • incV F H'.x :=
  mat_inv_mulVec p (by rw [Matrix.mulVec_smul, h.1, smul_smul, Units.inv_mul, one_smul])

theorem levi_inv_y {t h₁ p} (h : IsLevi (σ := σ) (W := W) (W₁ := W₁) H' t h₁ p) :
    mat p⁻¹ *ᵥ incV F H'.y = cA σ t.1 • incV F H'.y :=
  mat_inv_mulVec p (by rw [Matrix.mulVec_smul, h.2.1, smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul])

theorem Mix2.levi (h : Mix2 H H' χX χW rX rW om om₀ e) {t g₁ p t' h₁ p'} (h1 : IsLevi H t g₁ p) (h2 : IsLevi H' t' h₁ p') {Φ}
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : e (om (p, p') Φ) = ((χW t : ℂ) * (((absE F E t : ℝ) ^ rX : ℝ) : ℂ) *
      ((χX t' : ℂ) * (((absE F E t' : ℝ) ^ rW : ℝ) : ℂ))) • om₀ (g₁, h₁) (e Φ) := by
  simpa using h t g₁ p h1 1 (one_mem _) t' h₁ p' h2 1 (one_mem _) Φ hΦ

theorem Mix2.uni (h : Mix2 H H' χX χW rX rW om om₀ e) {m} (hm : m ∈ unip σ X H) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    e (om (m, 1) Φ) = e Φ := by
  simpa [← Prod.one_eq_mk] using h 1 1 1 (levi_one H) m hm 1 1 1 (levi_one H') 1 (one_mem _) Φ hΦ

theorem rpow_c {a : ℝ} (ha : 0 < a) (x y : ℝ) : ((a ^ x : ℝ) : ℂ) * ((a ^ y : ℝ) : ℂ) = ((a ^ (x + y) : ℝ) : ℂ) := by
  rw [Real.rpow_add ha, Complex.ofReal_mul]

theorem lawsTA (hp : IsPair B M χX χW om r s r' s') (hM : Mix2 H H' χX χW ((d₁ : ℝ) / 2) ((n : ℝ) / 2) om om₀ e)
    (hx : ∀ m ∈ unip σ X H, mat m *ᵥ incV F H.x = incV F H.x) :
    LawsT B M om om₀ H H' e (shiftA H H') (fun l => (χW⁻¹ l : ℂ) * (((absE F E l : ℝ) ^ ((n : ℝ) - 1 - d₁ / 2) : ℝ) : ℂ))
      fun l => l⁻¹ := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  refine ⟨inv_one, by simp, fun m hm Ψ hΨ => ?_, fun l g₁ p h₁ p' h1 h2 Ψ hΨ => ?_⟩
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.uni hm (hs _ _ hΨ), mat_inv_mulVec m (hx m hm), inv_one, mat_one', Matrix.one_mulVec]
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi h1 h2 (hs _ _ hΨ), isLevi_inv' h1, levi_inv_y h2, smul_smul]
    simp only [inv_inv, Units.val_one, map_one, one_smul, Matrix.smul_vecMulVec, NNReal.coe_one, Real.one_rpow, Circle.coe_one,
      Complex.ofReal_one, mul_one, map_inv, MonoidHom.inv_apply]
    congr 1
    have ha := absE_pos (F := F) l
    rw [mul_left_comm, NNReal.coe_inv, rpow_c (inv_pos.2 ha), Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
    congr 3
    ring

theorem lawsA (hp : IsPair B M χX χW om r s r' s') (hM : Mix2 H H' χX χW ((d₁ : ℝ) / 2) ((n : ℝ) / 2) om om₀ e) {z : ℕ}
    (hz : 2 * n = d + 2 * z) (hd : d = d₁ + 2) (hx : ∀ m ∈ unip σ X H, mat m *ᵥ incV F H.x = incV F H.x) :
    Laws B M om om₀ H H' e (shiftA H H') χW⁻¹ (χX / χW) z fun l => l⁻¹ := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  have hd' : (d : ℝ) = d₁ + 2 := by exact_mod_cast hd
  have hz' : (2 * n : ℝ) = d + 2 * z := by exact_mod_cast hz
  refine ⟨?_, fun t h₁ p' h2 => ⟨GlobalTheory.Doubling.conjUnit σ t, fun l Ψ hΨ => ?_⟩⟩
  · convert lawsTA hp hM hx using 3 with l
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast]
    congr 2
    linarith
  · unfold shiftA
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi (levi_one H) h2 (hs _ _ hΨ), levi_inv_y h2, inv_one, mat_one', Matrix.one_mulVec,
      Matrix.vecMulVec_smul, smul_smul, Units.val_mul, conjUnit_val]
    congr 1
    have ha := absE_pos (F := F) t
    simp only [map_one, NNReal.coe_one, Real.one_rpow, Circle.coe_one, Complex.ofReal_one, mul_one, one_mul, MonoidHom.inv_apply,
      chi_conj hp.base.cm hp.resW, inv_inv, GlobalTheory.Doubling.absE_conjUnit, MonoidHom.div_apply, Circle.coe_div]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, show (n : ℝ) / 2 = (d - n) / 2 + z by linarith, ← rpow_c ha]
    field_simp

theorem sy_iso (hx : form σ W.J H'.x H'.x = 0) (a b : Fin n → AE F E) :
    sy σ X W (Matrix.vecMulVec a (incV F H'.x)) (Matrix.vecMulVec b (incV F H'.x)) = 0 := by
  have h0 : ∑ j, ∑ l, incV F H'.x j * incM F W.J j l * cA σ (incV F H'.x l) = 0 := by
    have := congrArg (inclR (F := F) (AF F)) hx
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, map_zero] at this
    simpa [incV, incM, cA, inclR, mul_assoc] using this
  have : hTens (cA σ) (incM F X.J) (incM F W.J) (Matrix.vecMulVec a (incV F H'.x)) (Matrix.vecMulVec b (incV F H'.x)) = 0 := by
    calc _ = ∑ i, ∑ k, a i * incM F X.J i k * cA σ (b k) * ∑ j, ∑ l, incV F H'.x j * incM F W.J j l * cA σ (incV F H'.x l) := by
          simp only [hTens, Matrix.vecMulVec_apply, map_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
      _ = 0 := by simp [h0]
  simp only [sy, symp, this, mul_zero, map_zero]

theorem lawsB {M₀ : Model σ X₁ W₁} (hp : IsPair B M χX χW om r s r' s') (he : IsEv B M M₀ H.ι H'.ι (isoB H H') e)
    (hM : Mix2 H H' χX χW ((d : ℝ) / 2) ((n₁ : ℝ) / 2) om om₀ e) {z : ℕ}
    (hz : d + 2 = 2 * n + 2 * z) (hn : n = n₁ + 2) (hxx : form σ W.J H'.x H'.x = 0)
    (hy : ∀ m ∈ unip σ X H, ∃ (y : Fin n₁ → AE F E) (c : AE F E),
      mat m *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ y + c • incV F H.x) :
    Laws B M om om₀ H H' e (shiftB σ H H') χW (χX / χW) z id := by
  have hs := fun w Ψ h => rho_mem M hp.base.std w (Φ := Ψ) h
  have hz' : (d : ℝ) + 2 = 2 * n + 2 * z := by exact_mod_cast hz
  have hn' : (n : ℝ) = n₁ + 2 := by exact_mod_cast hn
  refine ⟨⟨rfl, by simp, fun m hm Ψ hΨ => ?_, fun l g₁ p h₁ p' h1 h2 Ψ hΨ => ?_⟩,
    fun t h₁ p' h2 => ⟨(GlobalTheory.Doubling.conjUnit σ t)⁻¹, fun l Ψ hΨ => ?_⟩⟩
  · unfold shiftB
    obtain ⟨y, c, hy'⟩ := hy m⁻¹ (inv_mem hm)
    rw [rho_om hp _ _ _ _ _ hΨ, hM.uni hm (hs _ _ hΨ), hy', inv_one, mat_one', Matrix.one_mulVec, Units.val_one, map_one, one_smul,
      one_smul, Matrix.add_vecMulVec, Matrix.add_vecMulVec, add_comm, ← rho_rho_of M.co B.ψ _ _ (by
        rw [← Matrix.add_vecMulVec]; exact sy_iso hxx _ _), he.inv _ (Or.inl ⟨c • incV F H'.x, by
        rw [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]⟩) _ (hs _ _ hΨ), add_comm, ← rho_rho_of M.co B.ψ _ _ (sy_iso hxx _ _),
      he.inv _ (Or.inr ⟨y, rfl⟩) _ (hs _ _ hΨ)]
  · unfold shiftB
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi h1 h2 (hs _ _ hΨ), levi_inv_y h1, isLevi_inv' h2, smul_smul]
    simp only [id, inv_one, Units.val_one, map_one, one_smul, Matrix.smul_vecMulVec, NNReal.coe_one, Real.one_rpow, Circle.coe_one,
      Complex.ofReal_one, mul_one]
    congr 1
    have ha := absE_pos (F := F) l
    rw [mul_left_comm, rpow_c ha, ← Complex.ofReal_pow, ← Real.rpow_natCast]
    congr 3
    linarith
  · unfold shiftB
    have hc : cA σ (l * (GlobalTheory.Doubling.conjUnit σ t)⁻¹ : (AE F E)ˣ).1 = cA σ l.1 * (t⁻¹ : (AE F E)ˣ).1 := by
      rw [Units.val_mul, map_mul, ← map_inv, conjUnit_val, cA_cA hp.base.cm]
    rw [rho_om hp _ _ _ _ _ hΨ, hM.levi (levi_one H) h2 (hs _ _ hΨ), isLevi_inv' h2, inv_one, mat_one', Matrix.one_mulVec,
      Matrix.vecMulVec_smul, smul_smul, hc]
    congr 1
    have ha := absE_pos (F := F) t
    simp only [map_one, NNReal.coe_one, Real.one_rpow, Circle.coe_one, Complex.ofReal_one, mul_one, one_mul, map_inv,
      chi_conj hp.base.cm hp.resW, inv_inv, GlobalTheory.Doubling.absE_conjUnit, MonoidHom.div_apply, Circle.coe_div, NNReal.coe_inv]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le,
      show (n₁ : ℝ) / 2 = (d - n) / 2 + -z by linarith, ← rpow_c ha]
    field_simp

end

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.KerGeo
section
set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.ThKCT.Ker

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst PositivityTheory.ThKG PositivityTheory.ThKG.Tow PositivityTheory.Mix
open GlobalTheory.Doubling (absE)
open Matrix (vecMulVec)

section Alg

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {c : S →ₐ[R] S} {n d n₁ d₁ : ℕ}
  {J : Matrix (Fin n) (Fin n) S} {J' : Matrix (Fin d) (Fin d) S}

theorem hT_vv (a a' : Fin n → S) (b b' : Fin d → S) :
    hTens c J J' (vecMulVec a b) (vecMulVec a' b') = bf c.toRingHom J a a' * bf c.toRingHom J' b b' := by
  simp only [hTens, bf, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, map_mul, Finset.sum_mul, Finset.mul_sum]
  refine Eq.trans Finset.sum_comm (Finset.sum_congr rfl fun j _ => ?_)
  refine Eq.trans (Finset.sum_congr rfl fun i _ => Finset.sum_comm) (Eq.trans Finset.sum_comm ?_)
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

theorem hT_add_l (x x' y : Matrix (Fin n) (Fin d) S) : hTens c J J' (x + x') y = hTens c J J' x y + hTens c J J' x' y := by
  simp only [hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem hT_add_r (x y y' : Matrix (Fin n) (Fin d) S) : hTens c J J' x (y + y') = hTens c J J' x y + hTens c J J' x y' := by
  simp only [hTens, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hT_smul_l (a : S) (x y : Matrix (Fin n) (Fin d) S) : hTens c J J' (a • x) y = a * hTens c J J' x y := by
  simp only [hTens, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem hT_smul_r (a : S) (x y : Matrix (Fin n) (Fin d) S) : hTens c J J' x (a • y) = c a * hTens c J J' x y := by
  simp only [hTens, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  simp only [mul_left_comm]

theorem hT_sum_r {k : ℕ} (x : Matrix (Fin n) (Fin d) S) (y : Fin k → Matrix (Fin n) (Fin d) S) :
    hTens c J J' x (∑ i, y i) = ∑ i, hTens c J J' x (y i) := by
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => simp [hTens]
  | insert a s h ih => rw [Finset.sum_insert h, Finset.sum_insert h, hT_add_r, ih]

theorem mid_eq (ι : Matrix (Fin n) (Fin n₁) S) (ι' : Matrix (Fin d) (Fin d₁) S) (w : Matrix (Fin n₁) (Fin d₁) S) :
    ι * w * ι'ᵀ = ∑ i, vecMulVec (ι *ᵥ Pi.single i 1) (ι' *ᵥ w i) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mulVec_single_one, Matrix.col_apply,
    Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp [Pi.single_apply, mul_comm, mul_left_comm]

theorem hT_vm {ι : Matrix (Fin n) (Fin n₁) S} {ι' : Matrix (Fin d) (Fin d₁) S} {a : Fin n → S} {b : Fin d → S}
    (h : (∀ z, bf c.toRingHom J a (ι *ᵥ z) = 0) ∨ ∀ z, bf c.toRingHom J' b (ι' *ᵥ z) = 0) (w : Matrix (Fin n₁) (Fin d₁) S) :
    hTens c J J' (vecMulVec a b) (ι * w * ι'ᵀ) = 0 := by
  rw [mid_eq, hT_sum_r]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases h with h | h <;> simp only [hT_vv, h, mul_zero, zero_mul]

theorem hT_trace (z z' : Matrix (Fin n) (Fin d) S) : hTens c J J' z z' = (zᵀ * J * z'.map c * J'ᵀ).trace := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => by ring

theorem hT_mm (P : Matrix (Fin n) (Fin n₁) S) (P' : Matrix (Fin d) (Fin d₁) S) (z z' : Matrix (Fin n₁) (Fin d₁) S) :
    hTens c J J' (P * z * P'ᵀ) (P * z' * P'ᵀ) = hTens c (Pᵀ * J * P.map c) (P'ᵀ * J' * P'.map c) z z' := by
  have hm : (P * z' * P'ᵀ).map c = P.map c * z'.map c * (P'.map c)ᵀ := by
    rw [show (P * z' * P'ᵀ).map c = (P * z').map c * P'ᵀ.map c from Matrix.map_mul (f := c.toRingHom),
      show (P * z').map c = P.map c * z'.map c from Matrix.map_mul (f := c.toRingHom)]
    rfl
  rw [hT_trace, hT_trace, hm]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem vv_mul_r (a : Fin n → S) (b : Fin d₁ → S) (P : Matrix (Fin d) (Fin d₁) S) : vecMulVec a b * Pᵀ = vecMulVec a (P *ᵥ b) := by
  rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

theorem span_r {c : S →+* S} {ε x y} {ι : Matrix (Fin d) (Fin d₁) S} (h : PlaneOK c J' ε x y ι) (v : Matrix (Fin n) (Fin d) S) :
    ∃ (s t : Fin n → S) (z : Matrix (Fin n) (Fin d₁) S), v = vecMulVec s x + z * ιᵀ + vecMulVec t y := by
  choose s t z e using fun i => h.span (v i)
  refine ⟨s, t, Matrix.of z, Matrix.ext fun i j => ?_⟩
  have := congrFun (e i) j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at this
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, this, mul_comm]

theorem span_l {c : S →+* S} {ε x y} {ι : Matrix (Fin n) (Fin n₁) S} (h : PlaneOK c J ε x y ι) (v : Matrix (Fin n) (Fin d) S) :
    ∃ (s t : Fin d → S) (z : Matrix (Fin n₁) (Fin d) S), v = vecMulVec x s + ι * z + vecMulVec y t := by
  obtain ⟨s, t, z, e⟩ := span_r h vᵀ
  refine ⟨s, t, zᵀ, ?_⟩
  rw [← Matrix.transpose_transpose v, e]
  simp only [Matrix.transpose_add, Matrix.transpose_vecMulVec, Matrix.transpose_mul, Matrix.transpose_transpose]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

theorem tr_inc (e : E) : Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem hT_inc (x y : Matrix (Fin n) (Fin d) E) : hTens (cA σ) (incM F X.J) (incM F W.J) (incM F x) (incM F y) =
    inclR (F := F) (AF F) (hTens σ X.J W.J x y) := by
  simp only [hTens, incM, Matrix.map_apply, cA_inc, map_mul, map_sum]

theorem sy_inc (x y : Matrix (Fin n) (Fin d) E) :
    sy σ X W (incM F x) (incM F y) = algebraMap F (AF F) (Algebra.trace F E (-hTens σ X.J W.J x y)) := by
  rw [sy, symp, hT_inc, ← tr_inc, map_neg, neg_one_mul]

theorem sy_of_hT {x y : Ten F E n d} (h : hTens (cA σ) (incM F X.J) (incM F W.J) x y = 0) : sy σ X W x y = 0 := by
  rw [sy, symp, h, mul_zero, map_zero]

theorem incM_vv (a : Fin n → E) (b : Fin d → E) : incM F (vecMulVec a b) = vecMulVec (incV F a) (incV F b) := by
  ext i j
  simp [incM, incV, Matrix.vecMulVec_apply]

theorem incM_add (a b : Matrix (Fin n) (Fin d) E) : incM F (a + b) = incM F a + incM F b := Matrix.map_add _ (map_add _) _ _

theorem incM_one : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_gram {ι : Matrix (Fin n) (Fin n₁) E} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} (h : ιᵀ * J * ι.map σ = J₁) :
    (incM F ι)ᵀ * incM F J * (incM F ι).map (cA σ) = incM F J₁ := by
  rw [← h]
  simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rfl

structure PG (σ : E →ₐ[F] E) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (ε : ℤ) : Prop where
  rat : PlaneOK σ.toRingHom Y.J (ε : E) H.x H.y H.ι
  ad : PlaneOK (cA σ).toRingHom (incM F Y.J) (ε : AE F E) (incV F H.x) (incV F H.y) (incM F H.ι)
  inj : ∀ u, H.ι *ᵥ u = 0 → u = 0
  gram : H.ιᵀ * Y.J * H.ι.map σ = Y₁.J

theorem nd_of_det {J : Matrix (Fin n) (Fin n) E} (hd : J.det ≠ 0) (v : Fin n → E) (h : ∀ w, bf σ.toRingHom J w v = 0) : v = 0 := by
  have h0 : J *ᵥ (fun i => σ (v i)) = 0 := funext fun j => by simpa [bf] using h (Pi.single j 1)
  have := Matrix.eq_zero_of_mulVec_eq_zero hd h0
  exact funext fun i => σ.toRingHom.injective ((congrFun this i).trans (map_zero _).symm)

theorem pg_of (hB : B.IsGood σ) {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ : ℕ}
    (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (ε : ℤˣ) (hJ : ∀ i j, σ (Y.J j i) = ((ε : ℤ) : E) * Y.J i j) (hd : Y.J.det ≠ 0)
    (hL : Y.L.IsLattice E) : PG σ Y Y₁ H ε := by
  have sp : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin n₁ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := fun v => by
    have hv : v ∈ Submodule.span E (Y.L : Set (Fin n → E)) := hL.span_eq_top ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, t, u, -, -, -, e⟩ := hH.split z hz
      exact ⟨s, t, u, e⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨s, t, u, rfl⟩ := ha
      obtain ⟨s', t', u', rfl⟩ := hb
      exact ⟨s + s', t + t', u + u', by rw [Matrix.mulVec_add]; module⟩
    | smul a b _ hb =>
      obtain ⟨s, t, u, rfl⟩ := hb
      exact ⟨a * s, a * t, a • u, by rw [Matrix.mulVec_smul]; module⟩
  refine ⟨⟨conj_conj hB, by rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp, map_intCast _ _, hJ, hH.xx, hH.yy, hH.xy,
    fun z => (hH.orth z).1, fun z => (hH.orth z).2, sp, fun v hv => ?_⟩, planeOK hB hH ε hJ hd hL, fun u hu => ?_, hH.gram⟩
  · refine Matrix.eq_zero_of_vecMul_eq_zero hd (funext fun j => ?_)
    have := hv (Pi.single j 1)
    have e : (fun l => σ.toRingHom ((Pi.single j 1 : Fin n → E) l)) = Pi.single j 1 := funext fun l => by
      by_cases h : l = j <;> simp [Pi.single_apply, h]
    rw [bf, e, Matrix.dotProduct_mulVec] at this
    simpa using this
  · let L : (E × (Fin n₁ → E) × E) →ₗ[E] (Fin n → E) :=
      (LinearMap.toSpanSingleton E _ H.x).coprod ((Matrix.mulVecLin H.ι).coprod (LinearMap.toSpanSingleton E _ H.y))
    have hs : Function.Surjective L := fun v => by
      obtain ⟨s, t, u, e⟩ := sp v
      exact ⟨(s, u, t), by simp [L, e, add_assoc]⟩
    have hi := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := L) (by simp [hH.rank]; ring)).2 hs
    have : ((0, u, 0) : E × (Fin n₁ → E) × E) = 0 := hi (by simp [L, hu])
    exact congrArg (·.2.1) this

theorem herm_det {r s : ℕ} (hY : X.IsHerm σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine det_ne_of_sig (hY.sig w) ?_
  have := RingHom.map_det (B.emb w).1 X.J
  rw [h0, map_zero] at this
  exact this.symm

theorem skew_det {r s : ℕ} (hY : X.IsSkew σ B r s) : X.J.det ≠ 0 := fun h0 => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine det_ne_of_sig (hY.sig w) ?_
  have := RingHom.map_det (B.emb w).1 X.J
  rw [h0, map_zero] at this
  rw [Matrix.det_smul]
  exact mul_eq_zero_of_right _ this.symm

theorem pg_herm (hB : B.IsGood σ) {H : Plane E n n₁} {i₀ i₁ r s : ℕ} (hH : H.IsAdapted σ B X X₁ i₀ i₁) (hY : X.IsHerm σ B r s) :
    PG σ X X₁ H 1 := pg_of hB hH 1 (fun i j => by simp [hY.herm]) (herm_det hY) hY.lat

theorem pg_skew (hB : B.IsGood σ) {H : Plane E n n₁} {i₀ i₁ r s : ℕ} (hH : H.IsAdapted σ B X X₁ i₀ i₁) (hY : X.IsSkew σ B r s) :
    PG σ X X₁ H (-1) := pg_of hB hH (-1) (fun i j => by simp [hY.skew]) (skew_det hY) hY.lat

theorem polar_of {T : Type} [AddCommGroup T] [Module E T] [Module F T] [IsScalarTower F E T] [FiniteDimensional F T]
    {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Ten F E n d)}
    (U Z : T →ₗ[E] Matrix (Fin n) (Fin d) E) (hI : ∀ t (a : AF F), a • incM F (Z t) ∈ I)
    (nd : ∀ t, (∀ t', hTens σ X.J W.J (Z t') (U t) = 0) → t = 0)
    (uu : ∀ t t', hTens σ X.J W.J (U t) (U t') = 0) (zz : ∀ t t', hTens σ X.J W.J (Z t) (Z t') = 0)
    (um : ∀ t (w : Ten F E n₁ d₁), hTens (cA σ) (incM F X.J) (incM F W.J) (incM F (U t)) (incM F ι * w * (incM F ι')ᵀ) = 0)
    (zm : ∀ t (w : Ten F E n₁ d₁), hTens (cA σ) (incM F X.J) (incM F W.J) (incM F (Z t)) (incM F ι * w * (incM F ι')ᵀ) = 0)
    (g : ιᵀ * X.J * ι.map σ = X₁.J) (g' : ι'ᵀ * W.J * ι'.map σ = W₁.J)
    (span : ∀ x, ∃ (a b : T) (x₁ : Matrix (Fin n₁) (Fin d₁) E), x = U a + Z b + ι * x₁ * ι'ᵀ) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m) F T) (z : Fin m → Matrix (Fin n) (Fin d) E),
      Polar σ X W X₁ W₁ ι ι' I (fun j => U (b j)) z := by
  let β : LinearMap.BilinForm F T := LinearMap.mk₂ F (fun t' t => Algebra.trace F E (-hTens σ X.J W.J (Z t') (U t)))
    (fun a b c => by rw [map_add, hT_add_l, neg_add, map_add])
    (fun a b c => by rw [← algebraMap_smul E a b, map_smul, hT_smul_l, ← mul_neg, ← Algebra.smul_def, map_smul])
    (fun a b c => by rw [map_add, hT_add_r, neg_add, map_add])
    (fun a b c => by
      rw [← algebraMap_smul E a c, map_smul, hT_smul_r, σ.commutes, ← mul_neg, ← Algebra.smul_def, map_smul])
  have hβ : β.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingRight fun t ht => nd t fun t' => by
    refine neg_eq_zero.1 ((traceForm_nondegenerate F E).1 _ fun a => ?_)
    have := ht (a • t')
    simp only [β, LinearMap.mk₂_apply, map_smul, hT_smul_l] at this
    rw [Algebra.traceForm_apply, ← this]
    congr 1
    ring
  let b := Module.finBasis F T
  refine ⟨_, b, fun j => Z (β.dualBasis hβ b j), ⟨fun j a => hI _ a, fun i j => ?_⟩, fun i j => ?_, fun i j => ?_,
    fun i w => sy_of_hT (um _ w), fun i w => sy_of_hT (zm _ w), fun w w' => ?_, fun x => ?_⟩
  · have := LinearMap.BilinForm.apply_dualBasis_left hβ b i j
    simp only [β, LinearMap.mk₂_apply] at this
    rw [sy_inc, this]
    by_cases h : i = j <;> simp [h, eq_comm]
  · rw [sy_inc, uu]; simp
  · rw [sy_inc, zz]; simp
  · rw [sy, sy, symp, symp, hT_mm, incM_gram g, incM_gram g']
  · obtain ⟨s, t, x₁, rfl⟩ := span x
    refine ⟨b.repr s, (β.dualBasis hβ b).repr t, x₁, ?_⟩
    simp only [← LinearMap.map_smul_of_tower, ← map_sum, Module.Basis.sum_repr]

end PositivityTheory.ThKCT.Ker

end
end

