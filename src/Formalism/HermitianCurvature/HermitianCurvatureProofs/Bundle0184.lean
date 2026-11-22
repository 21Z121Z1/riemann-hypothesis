import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveDensityModerateGrowth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SesquilinearLevelZeroPairing

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
section
noncomputable section

open Complex

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem norm_iter_cexp (i : ℕ) (z : ℂ) : ‖iteratedFDeriv ℝ i Complex.exp z‖ = Real.exp z.re := by
  have hc : ContDiffAt ℂ (i : ℕ) Complex.exp z := Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp]
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_cexp_const_mul i 1) z
  simp only [one_mul, one_pow] at h
  rw [h, Complex.norm_exp]

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def phaseL (s : ℂ) (D : Mat k r →L[ℝ] ℂ) : Mat k r →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => s * D g - starRingEnd ℂ (s * D g)
      map_add' := by intro g g'; simp only [map_add, mul_add]; ring
      map_smul' := by
        intro c g
        simp only [map_smul, Complex.real_smul, map_mul, Complex.conj_ofReal, RingHom.id_apply]
        ring }

theorem phaseL_apply (s : ℂ) (D : Mat k r →L[ℝ] ℂ) (g : Mat k r) :
    phaseL s D g = s * D g - starRingEnd ℂ (s * D g) := rfl

theorem phaseL_re (s : ℂ) (D : Mat k r →L[ℝ] ℂ) (g : Mat k r) : (phaseL s D g).re = 0 := by
  rw [phaseL_apply, Complex.sub_re, Complex.conj_re, sub_self]

theorem good_cexp (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (θ : Mat k r →L[ℝ] ℂ) (hθ : ∀ g, (θ g).re = 0) :
    JCx2.mnGood Bs ε (fun g => Complex.exp (θ g)) := by
  intro F hF
  obtain ⟨hF1, hF2, hF3⟩ := hF
  have hexp : ContDiff ℝ ⊤ Complex.exp := Complex.contDiff_exp
  have hc : ContDiff ℝ ⊤ (fun g : Mat k r => Complex.exp (θ g)) := hexp.comp θ.contDiff
  refine ⟨?_, fun A m => ?_, fun g hg h => hF3 g hg (fun h0 => h (by simp [h0]))⟩
  · intro g₀ hg₀
    obtain ⟨U, f, hU, hgU, hf, hff⟩ := hF1 g₀ hg₀
    have hc' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g : Mat k r => Complex.exp (θ g)) U :=
      (hc.of_le le_top).contDiffOn
    exact ⟨U, fun g => Complex.exp (θ g) • f g, hU, hgU, hc'.smul hf,
      fun g hg hG => by simp only [hff g hg hG]⟩
  · obtain ⟨b, hb⟩ := hF2 (A + m) m
    set Lid : ℂ →L[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) :=
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℂ) (ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
      with hLid
    set Λ : Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) := fun g => Lid (Complex.exp (θ g)) with hΛdef
    have hΛ : ∀ g, Λ g = Complex.exp (θ g) • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := fun g => by
      simp [Λ, Lid]
    have hΛc : ContDiff ℝ ⊤ Λ := Lid.contDiff.comp hc
    obtain ⟨C1, hC1, hdlr⟩ := JCx4.dlr_bound (k := k) (r := r)
      (E := (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) m
    obtain ⟨K0, hK0⟩ : ∃ K : ℝ, ∀ M : Mat k r, ‖θ M‖ ≤ K * ‖M‖ := ⟨_, θ.le_opNorm⟩
    set K : ℝ := max K0 0 with hKdef
    have hK : ∀ M : Mat k r, ‖θ M‖ ≤ K * ‖M‖ := fun M =>
      (hK0 M).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hKnn : 0 ≤ K := le_max_right _ _
    have hθK := θ.opNorm_le_bound hKnn hK
    have hit : ∀ i g, ‖iteratedFDeriv ℝ i Λ g‖ ≤ ‖Lid‖ * K ^ i := by
      intro i g
      have h1 := Lid.norm_iteratedFDeriv_comp_left (f := fun g => Complex.exp (θ g)) (x := g) (N := ⊤) (n := i)
        hc.contDiffAt (by exact_mod_cast le_top)
      have h2 : iteratedFDeriv ℝ i (fun g => Complex.exp (θ g)) g =
          (iteratedFDeriv ℝ i Complex.exp (θ g)).compContinuousLinearMap (fun _ => θ) :=
        θ.iteratedFDeriv_comp_right (f := Complex.exp) hexp g (by exact_mod_cast le_top)
      have h3 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
        (iteratedFDeriv ℝ i Complex.exp (θ g)) (fun _ : Fin i => θ)
      have h5 := h3.trans (mul_le_mul (le_of_eq (by rw [norm_iter_cexp, hθ, Real.exp_zero]))
        (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hθK))
        (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one)
      rw [one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h5
      calc ‖iteratedFDeriv ℝ i Λ g‖ ≤ ‖Lid‖ * ‖iteratedFDeriv ℝ i (fun g => Complex.exp (θ g)) g‖ := h1
        _ ≤ ‖Lid‖ * K ^ i := by rw [h2]; exact mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
    set C : ℝ := C1 * 2 ^ m * ((m + 1 : ℕ) * (‖Lid‖ * (1 + K) ^ m)) with hC
    have hab : ∀ u v : List (Mat k r), (∀ X ∈ u, unitLie k r X) → (∀ X ∈ v, unitLie k r X) →
        u.length + v.length ≤ m → ∀ g ∈ GV k r, g ∉ (∅ : Set (Mat k r)) →
          ‖dLR u v Λ g‖ ≤ C * gN g ^ (m : ℝ) := by
      intro u v hu hv hl g hg _
      rw [Real.rpow_natCast]
      have h1 := hdlr Λ (hΛc.of_le (by exact_mod_cast le_top)) u v hu hv hl g
      have hg1 : 1 ≤ gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
      have hng : ‖g‖ ≤ gN g := JCx2.mn_norm_le_gN g
      have hsum : ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ ≤
          (m + 1 : ℕ) * (‖Lid‖ * (1 + K) ^ m) := by
        calc ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖
            ≤ ∑ _i ∈ Finset.range (m + 1), ‖Lid‖ * (1 + K) ^ m := by
              refine Finset.sum_le_sum fun i hi => (hit i g).trans ?_
              refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
              have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
              calc K ^ i ≤ (1 + K) ^ i := pow_le_pow_left₀ hKnn (by linarith) i
                _ ≤ (1 + K) ^ m := pow_le_pow_right₀ (by linarith) hi'
          _ = (m + 1 : ℕ) * (‖Lid‖ * (1 + K) ^ m) := by simp
      have hpow : (1 + ‖g‖) ^ m ≤ 2 ^ m * gN g ^ m := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) m
      have hS0 : 0 ≤ ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      calc ‖dLR u v Λ g‖ ≤ C1 * (1 + ‖g‖) ^ m * ∑ i ∈ Finset.range (m + 1), ‖iteratedFDeriv ℝ i Λ g‖ := h1
        _ ≤ C1 * (2 ^ m * gN g ^ m) * ((m + 1 : ℕ) * (‖Lid‖ * (1 + K) ^ m)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpow hC1) hsum hS0
          exact mul_nonneg hC1 (by positivity)
        _ = C * gN g ^ m := by rw [hC]; ring
    have ha : CkOn (m : ℕ∞) Set.univ Λ := fun g₀ _ =>
      ⟨Set.univ, Λ, isOpen_univ, trivial, (hΛc.of_le (by exact_mod_cast le_top)).contDiffOn, fun _ _ _ => rfl⟩
    have hb' := Formalism.FourierDecayAlt.P.BetaSesquilinearity.prodBound (O := ∅) (UU := Set.univ) isOpen_empty (fun g _ => Or.inr trivial)
      (A := A) (d := (m : ℝ)) ha hab hb (fun g _ h => h.elim)
    have e : (fun g => Complex.exp (θ g) • F g) = Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap Λ F := by
      funext g
      simp [Formalism.FourierDecayAlt.P.BetaSesquilinearity.ap, hΛ]
    rw [e]
    exact ⟨_, hb'⟩

theorem dmin_one (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) (h : 1 < r + 2) :
    Dmin k r z z' g ⟨1, h⟩ = herm (Hpk k r) (g *ᵥ fvec k r z' 0) (fvec k r z 0) := by
  unfold Dmin
  rw [Matrix.det_fin_one]
  rfl

theorem fsv_dmin_one (s : ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) (h : 1 < r + 2) :
    P5.fsv s (Dmin k r z z' g ⟨1, h⟩) =
      Complex.exp (phaseL s (JCx2.mnLinHerm (fvec k r z' 0) (fvec k r z 0)) g) := by
  rw [dmin_one, phaseL_apply, P5.fsv, map_mul]
  rfl

theorem good_fsv_dmin (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) (h : 1 < r + 2) :
    JCx2.mnGood Bs ε (fun g => P5.fsv s (Dmin k r Bs.z Bs.z' g ⟨1, h⟩)) := by
  intro F hF
  have := good_cexp Bs ε (phaseL s (JCx2.mnLinHerm (fvec k r Bs.z' 0) (fvec k r Bs.z 0))) (phaseL_re _ _) F hF
  simpa only [fsv_dmin_one] using this

theorem uInv_nice (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) :
    ∀ (w : List C.Letter) (x : Wd.Ix (Fin w.length) → Mat k r → (Wq →L[ℂ] Wp)),
      (∀ e, JC.NiceCoef Bs ε (x e)) → ∀ e, JC.NiceCoef Bs ε (KB.uInv s w x e)
  | [], x, hx, e => hx e
  | l :: w, x, hx, e => by
    unfold KB.uInv
    split_ifs
    · exact uInv_nice Bs ε s w _ (fun e' => hx _) _
    · exact JCx2.mn_nice_add (uInv_nice Bs ε s w _ (fun e' => hx _) _)
        (JCx2.mn_nice_smul _ (uInv_nice Bs ε s w _ (fun e' => hx _) _))
    · exact JCx2.mn_nice_add (uInv_nice Bs ε s w _ (fun e' => hx _) _)
        (JCx2.mn_nice_smul _ (uInv_nice Bs ε s w _ (fun e' => hx _) _))

theorem waveG_nice (Bs : RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) (w : List C.Letter)
    (x : Wd.Ix (Fin w.length) → Mat k r → (Wq →L[ℂ] Wp)) (hx : ∀ e, JC.NiceCoef Bs ε (x e)) :
    ∀ e, JC.NiceCoef Bs ε (KB.waveG Bs s w x e) := fun e =>
  good_fsv_dmin Bs ε s (by omega) _ (uInv_nice Bs ε s w x hx e)

end Formalism.FourierDecayAlt.P.PBFV
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PictureMemLevelZeroClass
section
namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section Tower

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}

def IsPic (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ y ∈ DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
    (Φ : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) F) y.1 y.2

theorem radSp_ext {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (Φ Ψ : RadSp k r z z' π π')
    (h : ∀ y ∈ DomR k r z z', (Φ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) : Φ = Ψ := by
  apply Subtype.ext
  funext c g
  by_cases hy : ((c, g) : (Fin r → ℂ) × Mx k r) ∈ DomR k r z z'
  · exact h _ hy
  · rw [Φ.2.1 (c, g) hy, Ψ.2.1 (c, g) hy]

theorem resG_JF_zero {k r : ℕ} (Bs : B.RealPlaceData k r Wp Wq) (i : Fin (r + 1)) :
    resG k r i (B.JF Bs (fun _ => (0 : Wq →L[ℂ] Wp))) = 0 := by
  funext c g
  simp [resG, Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero]

theorem transport {X : ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
    {μ : MeasureTheory.Measure (Mt (JC.parLev P0 j).k (JC.parLev P0 j).r)}
    {L : R.LevelData (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (JC.parLev P0 j).r}
    {st : Fr.Start (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))}
    {l0 : ℕ} (hD : IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0)
    {ε : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)} (hF : JC.NiceCoef (T.bs j) ε F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) (Y : ℝ) (a b : Fin 2) :
    ∃ F', JC.NiceCoef (T.bs j) ε F' ∧ IsPic T j ((QQi L st 0 (Y : ℂ) a b).1 Φ) F' := by
  let w : List C.Letter := [(true, Y)]
  let Fv : Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := Pi.single (eS 0 b) F
  have hFv : ∀ e, JC.NiceCoef (T.bs j) ε (Fv e) := by
    intro e
    by_cases h : e = eS 0 b
    · subst h; simpa [Fv] using hF
    · simp only [Fv, Pi.single_eq_of_ne h]; exact Formalism.FourierDecayAlt.P.JCx2.mn_nice_zero
  let xv : Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp) := fun e => B.JF (T.bs j) (Fv e)
  let Φv : Ix (Fin w.length) →
      RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' :=
    Pi.single (eS 0 b) Φ
  have hx : ∀ e, xv e ∈ FFl (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' 0
      (OmPlus (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z') := fun e =>
    Formalism.FourierDecayAlt.P.bessel_function_finite_class _ _ Wp Wq (T.bs j) (Fv e) ε hε (hFv e)
  have hΦv : ∀ e, ∀ y ∈ DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
      (Φv e : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
        resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (xv e) y.1 y.2 := by
    intro e y hy
    by_cases h : e = eS 0 b
    · subst h
      have := hΦ y hy
      simp only [Φv, xv, Fv, Pi.single_eq_same]
      exact this
    · simp only [Φv, xv, Fv, Pi.single_eq_of_ne h]
      have h0 := congrFun (congrFun (resG_JF_zero (T.bs j) (Fin.last (JC.parLev P0 j).r)) y.1) y.2
      exact h0.symm
  refine ⟨D.actOp (D.RRlev T (M.sgn P0 l0) j w) Fv (eS 0 a),
    Formalism.FourierDecayAlt.P.module_regularity Wp Wq P0 T (M.sgn P0 l0) j w Fv ε hε hFv (eS 0 a), fun y hy => ?_⟩
  have hact := Formalism.FourierDecayAlt.P.radial_module_action Wp Wq P0 T j X μ L st l0 hD w xv Φv hx hΦv (eS 0 a) y hy
  have hbes := Formalism.FourierDecayAlt.P.bessel_module Wp Wq P0 T (M.sgn P0 l0) j w Fv ε hε hFv (eS 0 a) y hy
  have e : P5.act (RRi L st 0 (D.positionted w)) Φv (eS 0 a) = (QQi L st 0 (Y : ℂ) a b).1 Φ := by
    show actP (RRw (QQi L st 0) [(⟨true, 0, (Y : ℂ)⟩ : Letter ℂ (Fin 1))]) (Pi.single (eS 0 b) Φ) (eS 0 a) = _
    exact blockMulVec_one_letter _ _ _ _ _ _
  have e' := congrArg (fun Ψ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
    (T.bs j).π' => (Ψ : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2) e
  exact e'.symm.trans (hact.trans hbes.symm)

end Tower

section Cls

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P0 : M.Par} {T : D.LevTower P0.k P0.r Wp Wq} {j : Fin (P0.r + 1)}
  {X : ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'}
  {μ : MeasureTheory.Measure (Mt (JC.parLev P0 j).k (JC.parLev P0 j).r)}
  {L : R.LevelData (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))
      (JC.parLev P0 j).r}
  {st : Fr.Start (Pr (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'))}
  {l0 : ℕ}
  {K : Fin ((JC.parLev P0 j).r + 1) →
    Submodule ℂ (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')}

def PicsIn (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (K0 : Submodule ℂ (RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')) :
    Prop :=
  ∀ (F : Mx (JC.parLev P0 j).k (JC.parLev P0 j).r → (Wq →L[ℂ] Wp)) (ε : ℝ), 0 < ε →
    (∀ (A' : ℝ) (m' : ℕ), B.InCC A' m' F) →
    (∀ g ∈ B.GV (JC.parLev P0 j).k (JC.parLev P0 j).r, F g ≠ 0 →
      ε ≤ Gf (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' g) →
    ∃ Φ ∈ K0, ∀ x ∈ DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
      (Φ : Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) x.1 x.2 =
        resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last (JC.parLev P0 j).r) (B.JF (T.bs j) F) x.1 x.2

theorem picture_mem_level_zero_class (hJ : PicsIn T j (K 0)) {ε : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}
    (hF : JC.NiceCoef (T.bs j) ε F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) : Φ ∈ K 0 := by
  obtain ⟨Φ', hK, hΦ'⟩ := hJ F ε hε hF.2.1 hF.2.2
  have e : Φ = Φ' := radSp_ext Φ Φ' (fun y hy => (hΦ y hy).trans (hΦ' y hy).symm)
  rw [e]; exact hK

theorem pic_mem_Ucls (hD : IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0)
    (hJ : PicsIn T j (K 0)) (Pts : Set ℝ) {ε : ℝ} (hε : 0 < ε) {F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp)}
    (hF : JC.NiceCoef (T.bs j) ε F)
    (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (hΦ : IsPic T j Φ F) : Φ ∈ Ucls (K 0) (Gen L st Pts) := by
  intro m hm
  have key : ∀ m ∈ Submonoid.closure (Gen L st Pts), ∀ (F : B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
      (Φ : RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π'),
      JC.NiceCoef (T.bs j) ε F → IsPic T j Φ F → ∃ F', JC.NiceCoef (T.bs j) ε F' ∧ IsPic T j (m.1 Φ) F' := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem a ha =>
      intro F Φ hF hΦ
      obtain ⟨Y, _, i, i', rfl⟩ := ha
      exact transport hD hε hF Φ hΦ Y i i'
    | one => intro F Φ hF hΦ; exact ⟨F, hF, hΦ⟩
    | mul a b _ _ iha ihb =>
      intro F Φ hF hΦ
      obtain ⟨F1, h1, h1'⟩ := ihb F Φ hF hΦ
      obtain ⟨F2, h2, h2'⟩ := iha F1 _ h1 h1'
      exact ⟨F2, h2, h2'⟩
  obtain ⟨F', hF', hΦ'⟩ := key m hm F Φ hF hΦ
  exact picture_mem_level_zero_class hJ hε hF' _ hΦ'

end Cls

section Words

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {S : Type}

theorem wordOK_gen (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hOK : P.OK) (hl1 : 1 ≤ l0) (hlk : l0 ≤ P.k) (hq : st.q = M.qC P)
    (hinv : st.inv = {Y | ∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0}) (u : List (Letter ℂ S))
    (hnd : (u.map Letter.intersection_update_fsHerm_neg_one).Nodup) (hpt : ∀ l ∈ u, ∃ Y : ℝ, l.pt = (Y : ℂ) ∧ I.OnCut P.u P.u' l0 Y)
    (hsep : u.Pairwise fun l l' => 2 < |l.pt.re - l'.pt.re|) : WordOK P z z' π π' st l0 u := by
  refine ⟨⟨hnd, ?_, ?_, ?_⟩, ?_, hsep⟩
  · intro l hl
    obtain ⟨Y, e, -⟩ := hpt l hl
    rw [e]; exact Complex.conj_ofReal Y
  · intro l hl
    obtain ⟨Y, e, hc⟩ := hpt l hl
    rw [e]
    have hx : ∀ e : ℝ, -1 ≤ e → e ≤ 1 → ∀ ρ, M.xC P ρ ((Y + e : ℝ) : ℂ) ≠ 0 :=
      fun e h1 h2 ρ => Formalism.FourierDecayAlt.P.JCTx5.xC_ne P hOK l0 hl1 hlk _ hc e h1 h2 ρ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hinv]; intro ρ; simpa using hx 0 (by norm_num) (by norm_num) ρ
    · rw [hinv]; intro ρ; simpa using hx 1 (by norm_num) (by norm_num) ρ
    · rw [hinv]; intro ρ; simpa [sub_eq_add_neg] using hx (-1) (by norm_num) (by norm_num) ρ
    · rw [hq]; simpa using Formalism.FourierDecayAlt.P.JCTx5.qC_ne P hOK l0 hl1 hlk _ hc 0 (by norm_num) (by norm_num)
    · rw [hq]; simpa [sub_eq_add_neg] using Formalism.FourierDecayAlt.P.JCTx5.qC_ne P hOK l0 hl1 hlk _ hc (-1) (by norm_num) (by norm_num)
  · refine hsep.imp fun {l l'} h n hn e => ?_
    have hre : l.pt.re - l'.pt.re = (n : ℝ) := by
      have := congrArg Complex.re e
      simpa using this
    have h2 : |(n : ℝ)| ≤ 2 := by exact_mod_cast hn
    rw [hre] at h
    linarith
  · intro l hl
    obtain ⟨Y, e, hc⟩ := hpt l hl
    rw [e]
    exact ⟨by simp, by simpa using hc⟩

end Words

end

end Formalism.FourierDecayAlt.P.PBF
end

