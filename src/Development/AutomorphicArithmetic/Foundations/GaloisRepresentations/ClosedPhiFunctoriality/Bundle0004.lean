import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrLimHolds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trLim_holds :
    TrStep → TrLim := by
  intro hstep l _ P AI T K bk Γ _ _ L₀ a r Cl Cv s V V' p θ pv hs hV hV' hlink hθ
  by_contra hne
  have hpθ : p - θ ≠ 0 := sub_ne_zero.mpr hne
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hlnorm : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    have h := PadicAlgCl.norm_extends l ((l : ℚ_[l]))
    rw [Padic.norm_p] at h
    simpa using h
  have hnp : ∀ (c : ℕ) (x : Om l), ‖(l : Om l) ^ c * x‖ = ((l : ℝ) ^ c)⁻¹ * ‖x‖ := by
    intro c x
    rw [norm_mul, norm_pow, hlnorm, inv_pow]
  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt (‖p - θ‖ + ∑ i, ‖(Cv.b i).trace‖) hl1
  have hsmall : ∀ x : Om l, ‖x‖ ≤ ‖p - θ‖ + ∑ i, ‖(Cv.b i).trace‖ → ‖(l : Om l) ^ c₁ * x‖ ≤ 1 := by
    intro x hx
    rw [hnp, inv_mul_le_iff₀ (pow_pos hl0 c₁), mul_one]
    exact hx.trans hc₁.le
  have hsum0 : 0 ≤ ∑ i, ‖(Cv.b i).trace‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have ht : ∀ i, ‖(l : Om l) ^ c₁ * (Cv.b i).trace‖ ≤ 1 := fun i =>
    hsmall _ (((Finset.single_le_sum (f := fun i => ‖(Cv.b i).trace‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))).trans
      (le_add_of_nonneg_left (norm_nonneg _)))
  have hd : ‖(l : Om l) ^ c₁ * (p - θ)‖ ≤ 1 := hsmall _ (le_add_of_nonneg_right hsum0)
  have hpos : 0 < ‖(l : Om l) ^ c₁ * (p - θ)‖ := by
    rw [hnp]
    exact mul_pos (inv_pos.mpr (pow_pos hl0 c₁)) (norm_pos_iff.mpr hpθ)
  obtain ⟨c₂, hc₂⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
  have hc₂' : ((l : ℝ) ^ c₂)⁻¹ ≤ ‖(l : Om l) ^ c₁ * (p - θ)‖ := by
    rw [← inv_pow]
    exact hc₂.le
  have hdvd : ∀ M : ℕ, (l : Per.Acris l) ^ M ∣ (l : Per.Acris l) ^ c₂ * s := by
    intro M
    obtain ⟨m, hMm, hm⟩ := hlink M
    have hle : ((l : ℝ) ^ m)⁻¹ ≤ ((l : ℝ) ^ M)⁻¹ :=
      inv_anti₀ (pow_pos hl0 M) (pow_le_pow_right₀ hl1.le hMm)
    refine hstep l P AI T s Cv.d (Cv.tw.d' m) (Cv.lay m).m M c₁ c₂ (fun i => (Cv.b i).trace)
      (fun j k => ((Cv.lay m).b j k).trace) (Cv.lay m).c (pv m) p θ (Cv.tw.Pi m) Cv.e (Cv.lay m).e V (V' m)
      hV (hV' m) hm (fun i => (pow_dvd_pow _ hMm).trans (Cv.unit m i)) (fun j => ?_) ((hθ m).trans hle) ht hd hc₂'
    have h := Cv.trace m j
    rw [Matrix.trace_sum] at h
    simp only [Matrix.trace_smul, smul_eq_mul] at h
    exact h.trans hle
  obtain ⟨htor, hcomp, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  have hz := GlobalTheory.CrZero.eq_zero_of_forall_dvd _ hcomp.toIsHausdorff _ hdvd
  have hs0 : s = 0 := GlobalTheory.CrZero.pow_cancel (l : Per.Acris l) htor c₂ s 0 (by simpa using hz)
  haveI : Nontrivial P.R.B := GlobalTheory.Pst.nontrivial_B P
  haveI : Nontrivial (Per.Bcris l) := T.eB.injective.nontrivial
  rw [hs0, map_zero] at hs
  exact not_isUnit_zero hs
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrLinHolds
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trLin_holds :
    TrLin := by
  intro k B W J _ _ _ _ _ _ a ha κ ψ hψ T x w h
  classical
  let bW : Module.Basis (Fin a) k W := Module.finBasisOfFinrankEq k W ha
  have hexp : ∀ (y : W) (i : Fin a), ψ y i = ∑ m, κ (bW.repr y m) * ψ (bW m) i := by
    intro y i
    conv_lhs => rw [← bW.sum_repr y]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hψ, Pi.smul_apply, smul_eq_mul]
  let X : Matrix (Fin a) (Fin a) B := Matrix.of fun i m => ψ (bW m) i
  let X' : Matrix (Fin a) (Fin a) B := Matrix.of fun m i' => ∑ j, w j * κ (bW.repr (x j i') m)
  have hXX : X * X' = 1 := by
    ext i i'
    rw [Matrix.mul_apply, Matrix.one_apply, ← h i i']
    simp only [X, X', Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hexp (x j i') i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hXX' : X' * X = 1 := mul_eq_one_comm.mp hXX
  let Tm : Matrix (Fin a) (Fin a) B := (LinearMap.toMatrix bW bW T).map κ
  have hrepr : ∀ (y : W) (m : Fin a),
      bW.repr (T y) m = ∑ m', LinearMap.toMatrix bW bW T m m' * bW.repr y m' := by
    intro y m
    rw [← LinearMap.toMatrix_mulVec_repr bW bW T y]
    rfl
  have hentry : ∀ i i', ∑ j, w j * ψ (T (x j i')) i = (X * Tm * X') i i' := by
    intro i i'
    have hTX : ∀ y : W, ψ (T y) i = ∑ m, (X * Tm) i m * κ (bW.repr y m) := by
      intro y
      rw [hexp (T y) i]
      simp only [hrepr, map_sum, map_mul, Matrix.mul_apply, X, Tm, Matrix.of_apply,
        Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring
    rw [Matrix.mul_apply]
    simp only [hTX, X', Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by ring
  have htr : Matrix.trace Tm = κ (LinearMap.trace k W T) := by
    rw [LinearMap.trace_eq_matrix_trace k bW T]
    simp [Matrix.trace, Tm, map_sum]
  calc ∑ i, ∑ j, w j * ψ (T (x j i)) i = Matrix.trace (X * Tm * X') := by
        simp only [Matrix.trace, Matrix.diag_apply, hentry]
    _ = Matrix.trace (X' * X * Tm) := by
        rw [Matrix.trace_mul_cycle]
    _ = κ (LinearMap.trace k W T) := by
        rw [hXX', one_mul, htr]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.TrStep
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem core {Z R B : Type} [CommRing Z] [CommRing R] [CommRing B] (f : R →+* B) (zc : Z →+* R) (zb : Z →+* B)
    (hz : ∀ x, f (zc x) = zb x) (n a s g : R) (nZ : Z) (hn : zc nZ = n) {d d' : ℕ}
    (V : Matrix (Fin d) (Fin d) R) (V' : Matrix (Fin d') (Fin d') R) (Pm : Matrix (Fin d) (Fin d') Z)
    (e : Fin d → Z) (e' : Fin d' → Z) (h3 : ∀ i j, n ∣ (V * Pm.map zc - Pm.map zc * V') i j)
    (h4 : ∀ i, nZ ∣ (Pm *ᵥ e' - e) i) (ui : Fin d → B) (vj : Fin d' → B) (w : B) (ai : Fin d → R) (bj : Fin d' → R)
    (ha : ∀ i, f (ai i) = f a * ui i) (hv : ∀ j, vj j = f n * f (bj j)) (hw : w = f n * f g) :
    ∃ Y : R, f a * (∑ i, (((V.map f * Pm.map zb - Pm.map zb * V'.map f) *ᵥ (fun j => zb (e' j))) -
        V.map f *ᵥ fun i => zb ((Pm *ᵥ e' - e) i)) i * ui i +
      ∑ j, (V'.map f *ᵥ fun i => zb (e' i)) j * vj j - f s * w) = f (n * Y) := by
  choose W hW using h3
  choose r hr using h4
  have hPb : Pm.map zb = (Pm.map zc).map f := by
    ext i j; simp [hz]
  have hE : (fun j => zb (e' j)) = f ∘ (fun j => zc (e' j)) := by
    ext j; simp [hz]
  have hD : V * Pm.map zc - Pm.map zc * V' = n • Matrix.of W := by
    ext i j; simp [hW]
  have hM : V.map f * Pm.map zb - Pm.map zb * V'.map f = (n • Matrix.of W).map f := by
    rw [← hD, hPb, Matrix.map_sub _ (map_sub f), Matrix.map_mul, Matrix.map_mul]
  have hq : (fun i => zb ((Pm *ᵥ e' - e) i)) = f ∘ (fun i => n * zc (r i)) := by
    ext i; simp only [Function.comp, hr i, map_mul, hz, ← hn]
  have h1 : ∀ i, (((V.map f * Pm.map zb - Pm.map zb * V'.map f) *ᵥ (fun j => zb (e' j))) -
        V.map f *ᵥ fun i => zb ((Pm *ᵥ e' - e) i)) i =
      f n * f ((Matrix.of W *ᵥ fun j => zc (e' j)) i - (V *ᵥ fun i => zc (r i)) i) := by
    intro i
    rw [hM, hE, hq, Pi.sub_apply, ← RingHom.map_mulVec, ← RingHom.map_mulVec, ← map_mul, ← map_sub]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum, mul_sub]
    congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∀ j, (V'.map f *ᵥ fun i => zb (e' i)) j = f ((V' *ᵥ fun i => zc (e' i)) j) := by
    intro j; rw [hE, ← RingHom.map_mulVec]
  refine ⟨∑ i, ((Matrix.of W *ᵥ fun j => zc (e' j)) i - (V *ᵥ fun i => zc (r i)) i) * ai i +
    ∑ j, a * (V' *ᵥ fun i => zc (e' i)) j * bj j - a * s * g, ?_⟩
  simp only [h1, h2, hv, hw, map_mul, map_add, map_sub, map_sum, ha, Finset.mul_sum, mul_add, mul_sub]
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  · ring

variable {l : ℕ} [Fact l.Prime]

private theorem u_alg {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (z : ℤ_[l]) :
    uB T (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l])) = Per.zB l z := by
  show T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) (z : ℚ_[l]))) = _
  rw [← IsScalarTower.algebraMap_apply]
  exact T.zB z

private theorem iB_zC (z : ℤ_[l]) : iB l (zC l z) = Per.zB l z := rfl

private theorem exists_iB {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (c : ↥(MaximalUnramifiedExtension l))
    (hc : ‖(c : Om l)‖ ≤ 1) : ∃ y : Per.Acris l, iB l y = uB T c := by
  obtain ⟨w, hw⟩ := GlobalTheory.ExpImage.exists_lifts_of_norm_le_one l P AI T (adjExt (c : Om l)) ⟨c, mem_adjExt _, c.2⟩ hc
  refine ⟨iA l w, ?_⟩
  have h : AI.ιA w = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c := hw
  show _ = T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c)
  rw [← h, T.ιA]
  rfl

private theorem norm_l : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [Padic.norm_p] at h
  rw [← h]
  congr 1

private theorem scale {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (lam : Om l →ₗ[↥(MaximalUnramifiedExtension l)] ↥(MaximalUnramifiedExtension l)) (n : ℕ) (y : Om l) :
    uB T (lam ((n : Om l) * y)) = (n : Per.Bcris l) * uB T (lam y) := by
  rw [← nsmul_eq_mul, map_nsmul, map_nsmul, nsmul_eq_mul]

end UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trStep_holds :
    Func → TrId → TrStep := by
  intro hF hI l _ P AI T s d d' m M c₁ c₂ t t' c pv p θ Pi e e' V V' h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hn : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := norm_l
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl0 : (l : Om l) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact (inv_pos.2 hlpos).ne hn
  have hlK : (l : ↥(MaximalUnramifiedExtension l)) ≠ 0 := by
    intro h0
    apply hl0
    have := congrArg (fun x : ↥(MaximalUnramifiedExtension l) => (x : Om l)) h0
    simpa using this
  have hsmall : ∀ y : Om l, ‖y‖ ≤ ((l : ℝ) ^ M)⁻¹ → ‖y / (l : Om l) ^ M‖ ≤ 1 := by
    intro y hy
    rw [norm_div, norm_pow, hn, inv_pow]
    exact div_le_one_of_le₀ (by simpa using hy) (by positivity) |>.trans le_rfl
  let δ : Fin d' → Om l := fun j => ∑ i, zOm l (Pi i j) * t i - ∑ k, c k * t' j k
  let η : Om l := θ - ∑ k, c k * pv k
  let x : Fin d ⊕ Fin d' ⊕ Unit → Om l := Sum.elim (fun i => (l : Om l) ^ c₁ * t i)
    (Sum.elim (fun j => δ j / (l : Om l) ^ M) (fun _ => η / (l : Om l) ^ M))
  have hx : ∀ i, ‖x i‖ ≤ 1 := by
    rintro (i | j | _)
    · exact h7 i
    · exact hsmall _ (h5 j)
    · exact hsmall _ h6
  obtain ⟨lam, hl1, hl2, hl3⟩ := hF l (MaximalUnramifiedExtension l) (Fin d ⊕ Fin d' ⊕ Unit) x ((l : Om l) ^ c₁ * (p - θ)) hx h8
  have hid := hI l (Per.Bcris l) (uB T) (Per.zB l) (u_alg T) (iB l s) d d' m t t' c pv p θ Pi e e'
    (V.map (iB l)) (V'.map (iB l)) h1 h2 lam
  choose ai hai using fun i => exists_iB T (lam (x (Sum.inl i))) (hl1 _)
  choose bj hbj using fun j => exists_iB T (lam (x (Sum.inr (Sum.inl j)))) (hl1 _)
  obtain ⟨g, hg⟩ := exists_iB T (lam (x (Sum.inr (Sum.inr ())))) (hl1 _)
  have hpow : ∀ (k : ℕ) (y : Om l), uB T (lam ((l : Om l) ^ k * y)) = (l : Per.Bcris l) ^ k * uB T (lam y) := by
    intro k y
    have := scale T lam (l ^ k) y
    push_cast at this
    exact this
  have hdiv : ∀ y : Om l, uB T (lam y) = (l : Per.Bcris l) ^ M * uB T (lam (y / (l : Om l) ^ M)) := by
    intro y
    rw [← hpow, mul_div_cancel₀ _ (pow_ne_zero _ hl0)]
  obtain ⟨Y, hY⟩ := core (iB l) (zC l) (Per.zB l) iB_zC ((l : Per.Acris l) ^ M) ((l : Per.Acris l) ^ c₁) s g
    ((l : ℤ_[l]) ^ M) (by simp) V V' Pi e e' h3 h4
    (fun i => uB T (lam (t i))) (fun j => uB T (lam (δ j))) (uB T (lam η)) ai bj
    (fun i => by
      rw [hai i]
      simp only [map_pow, map_natCast]
      exact hpow c₁ (t i))
    (fun j => by
      rw [hbj j]
      simp only [map_pow, map_natCast]
      exact hdiv (δ j))
    (by
      rw [hg]
      simp only [map_pow, map_natCast]
      exact hdiv η)
  rw [← hid] at hY
  set q : ↥(MaximalUnramifiedExtension l) := lam ((l : Om l) ^ c₁ * (p - θ)) with hq
  have huq : uB T q = (l : Per.Bcris l) ^ c₁ * uB T (lam (p - θ)) := hpow c₁ (p - θ)
  have hqn : ((l : ℝ) ^ c₂)⁻¹ ≤ ‖(q : Om l)‖ := h9.trans hl2
  have hq0 : q ≠ 0 := by
    intro h0
    have h00 : (0 : ℝ) < ((l : ℝ) ^ c₂)⁻¹ := by positivity
    rw [h0, ZeroMemClass.coe_zero, norm_zero] at hqn
    exact absurd hqn (not_le.2 h00)
  have hq' : ‖(((l : ↥(MaximalUnramifiedExtension l)) ^ c₂ / q : ↥(MaximalUnramifiedExtension l)) : Om l)‖ ≤ 1 := by
    push_cast
    rw [norm_div, norm_pow, hn, inv_pow]
    exact div_le_one_of_le₀ hqn (norm_nonneg _)
  obtain ⟨y', hy'⟩ := exists_iB T _ hq'
  refine ⟨Y * y', GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l ?_⟩
  have hqq : q * ((l : ↥(MaximalUnramifiedExtension l)) ^ c₂ / q) = (l : ↥(MaximalUnramifiedExtension l)) ^ c₂ := mul_div_cancel₀ _ hq0
  have hu : uB T q * iB l y' = (l : Per.Bcris l) ^ c₂ := by
    rw [hy', ← map_mul, hqq, map_pow, map_natCast]
  show iB l _ = iB l _
  rw [← mul_assoc, map_mul (iB l) _ y', ← hY]
  simp only [map_mul, map_pow, map_natCast]
  rw [← hu, huq]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.ZeroAp
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.zeroAp_holds :
    ZeroAp := by
  intro l _ K bk c M
  obtain ⟨htor, -, -, hphi, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.primePow_dvd_tiltUniformizer_pow_acris_eventually l K bk c M
  refine ⟨c * n₀ + M, ?_⟩
  intro d d' D F F' hdiv hcong
  have hdiv' : ∀ i j, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ∣ D i j := hdiv
  set u := ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X with hu
  have hφu : phiA l u = u ^ l := by
    rw [hu, RingHom.comp_apply, hphi, ← bk.ev_frob]
    have : frobS l bk.a X = X ^ l := by simp [frobS]
    rw [this, map_pow, map_pow]
  have hφl : ∀ k : ℕ, phiA l ((l : Per.Acris l) ^ k) = (l : Per.Acris l) ^ k := by
    intro k; simp
  set P : Per.Acris l := (l : Per.Acris l) ^ (c * n₀ + M) with hP
  have hφP : phiA l P = P := hφl _
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin d) (Fin d') (Per.Acris l),
      (l : Per.Acris l) ^ c • D = F * D.map (phiA l) * F' + P • G := by
    refine ⟨Matrix.of fun i j => (hcong i j).choose, ?_⟩
    ext i j
    have h := (hcong i j).choose_spec
    rw [Matrix.add_apply, Matrix.smul_apply (P), Matrix.of_apply, smul_eq_mul, ← h,
      Matrix.sub_apply]
    ring
  have key : ∀ t : ℕ, ∃ N H : Matrix (Fin d) (Fin d') (Per.Acris l),
      (l : Per.Acris l) ^ (c * t) • D = u ^ (l ^ t) • N + P • H := by
    intro t
    induction t with
    | zero =>
      refine ⟨Matrix.of fun i j => (hdiv' i j).choose, 0, ?_⟩
      ext i j
      simp only [mul_zero, pow_zero, pow_one, one_smul, smul_zero, add_zero, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul]
      rw [one_mul]
      exact (hdiv' i j).choose_spec
    | succ t ih =>
      obtain ⟨N, H, hNH⟩ := ih
      refine ⟨F * N.map (phiA l) * F', F * H.map (phiA l) * F' + (l : Per.Acris l) ^ (c * t) • G, ?_⟩
      have hmap : ((l : Per.Acris l) ^ (c * t) • D).map (phiA l)
          = (l : Per.Acris l) ^ (c * t) • D.map (phiA l) := by
        ext i j; simp [hφl]
      have hmap2 : (u ^ (l ^ t) • N + P • H).map (phiA l)
          = u ^ (l ^ (t + 1)) • N.map (phiA l) + P • H.map (phiA l) := by
        ext i j
        simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add,
          map_mul, map_pow, hφu, hφP]
        rw [← pow_mul, pow_succ' l t]
      calc (l : Per.Acris l) ^ (c * (t + 1)) • D
          = (l : Per.Acris l) ^ (c * t) • ((l : Per.Acris l) ^ c • D) := by
            rw [smul_smul, ← pow_add, mul_add, mul_one]
        _ = F * (((l : Per.Acris l) ^ (c * t) • D).map (phiA l)) * F'
              + P • ((l : Per.Acris l) ^ (c * t) • G) := by
            rw [hG, hmap, smul_add, Matrix.mul_smul, Matrix.smul_mul, smul_comm P]
        _ = u ^ (l ^ (t + 1)) • (F * N.map (phiA l) * F')
              + P • (F * H.map (phiA l) * F' + (l : Per.Acris l) ^ (c * t) • G) := by
            rw [hNH, hmap2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
              Matrix.mul_smul, Matrix.smul_mul, smul_add, add_assoc]
  intro i j
  obtain ⟨N, H, hNH⟩ := key n₀
  obtain ⟨y, hy⟩ := hn₀ n₀ le_rfl
  have hent : (l : Per.Acris l) ^ (c * n₀) * D i j = u ^ (l ^ n₀) * N i j + P * H i j := by
    have := congrFun (congrFun hNH i) j
    simpa using this
  have hpos : 1 ≤ l ^ n₀ := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  have hsplit : u ^ (l ^ n₀) = u * u ^ (l ^ n₀ - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  refine ⟨u * y * N i j + H i j, ?_⟩
  apply GlobalTheory.CrZero.pow_cancel _ htor (c * n₀)
  rw [hent, hsplit, hy, hP, pow_add]
  ring
end

