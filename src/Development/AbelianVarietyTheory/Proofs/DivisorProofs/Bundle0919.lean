import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0036
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacSign

open GlobalTheory.LatVac

variable {D : D7} {S T : HSp D}

def sgnW (ψ : AddChar (AF D.host.F) ℂ) (w : AE D) (u : WO S T) : ℂ := ψ (symplOH S T u (w • u))

theorem symplOH_self (u : WO S T) : symplOH S T u u = 0 := by
  have h := SplitScalar.symplOH_skew S T u u
  have h2 : symplO S T u u = 0 := by
    rw [← SplitScalar.symplOH_add_self]
    exact add_eq_zero_iff_eq_neg.2 h
  rw [symplOH, h2, mul_zero]

theorem symplOH_smul (a : AE D) (x y : WO S T) : symplOH S T (a • x) y = symplOH S T x (cA D a • y) := by
  rw [symplOH, symplOH, SplitScalar.symplO_smul]

theorem symplOH_quad {w : AE D} (hw : w + cA D w = 1) (u u' : WO S T) :
    symplOH S T u u' + symplOH S T (u + u') (w • (u + u')) =
      symplOH S T u (w • u) + symplOH S T u' (w • u') + symplO S T u (w • u') := by
  have h1 : symplOH S T u u' = symplOH S T u (w • u') + symplOH S T u (cA D w • u') := by
    rw [← SplitScalar.symplOH_add_right, ← add_smul, hw, one_smul]
  have h2 : symplOH S T u' (w • u) = -symplOH S T u (cA D w • u') := by
    rw [SplitScalar.symplOH_skew, symplOH_smul]
  rw [smul_add, SplitScalar.symplOH_add_left, SplitScalar.symplOH_add_right, SplitScalar.symplOH_add_right, h1, h2,
    ← SplitScalar.symplOH_add_self]
  ring

theorem sgnW_add (ψ : AddChar (AF D.host.F) ℂ) {w : AE D} (hw : w + cA D w = 1) {u u' : WO S T}
    (h : ψ (symplO S T u (w • u')) = 1) :
    ψ (symplOH S T u u') * sgnW ψ w (u + u') = sgnW ψ w u * sgnW ψ w u' := by
  rw [sgnW, ← ψ.map_add_eq_mul, symplOH_quad hw, ψ.map_add_eq_mul, ψ.map_add_eq_mul, h, mul_one, sgnW, sgnW]

theorem sgnW_zero (ψ : AddChar (AF D.host.F) ℂ) (w : AE D) : sgnW ψ w (0 : WO S T) = 1 := by
  rw [sgnW, symplOH, SplitScalar.symplO_zero_left, mul_zero, ψ.map_zero_eq_one]

theorem char_ne_zero {A : Type} [AddCommGroup A] (ψ : AddChar A ℂ) (a : A) : ψ a ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul a (-a)
  rw [add_neg_cancel, ψ.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem sgnW_half (ψ : AddChar (AF D.host.F) ℂ) (w : AE D) {e : AE D} (he : IsSplitIdem D e) {u : WO S T}
    (hu : IsHalf e u) : sgnW ψ w u = 1 := by
  have h : symplO S T u (w • u) = 0 :=
    SplitScalar.symplO_eq_zero S T (a := e) (b := e) (by rw [mul_comm, he.2.1]) hu fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hu i j]
  rw [sgnW, symplOH, h, mul_zero, ψ.map_zero_eq_one]

theorem sgnW_two (ψ : AddChar (AF D.host.F) ℂ) {w : AE D} (hw : w + cA D w = 1) {u : WO S T}
    (h : ψ (symplO S T u (w • u)) = 1) : sgnW ψ w (2 • u) = 1 := by
  have h1 := sgnW_add ψ hw h
  rw [symplOH_self, ψ.map_zero_eq_one, one_mul] at h1
  rw [two_nsmul, h1]
  exact char_half h

def sgnGroup (ψ : AddChar (AF D.host.F) ℂ) {w : AE D} (hw : w + cA D w = 1) (Λ : AddSubgroup (WO S T))
    (hΛ : ∀ u ∈ Λ, ∀ u' ∈ Λ, ψ (symplO S T u (w • u')) = 1) (f : WO S T → ℂ) : AddSubgroup (WO S T) where
  carrier := {u | u ∈ Λ ∧ heisO ψ S T u f = sgnW ψ w u • f}
  zero_mem' := ⟨zero_mem _, by rw [heisO_zero, sgnW_zero, one_smul]⟩
  add_mem' := by
    rintro u u' ⟨hu, h⟩ ⟨hu', h'⟩
    refine ⟨add_mem hu hu', ?_⟩
    have h1 := heisO_heisO ψ u u' f
    rw [h', heisO_smul, h, smul_smul, mul_comm, ← sgnW_add ψ hw (hΛ u hu u' hu'), mul_smul] at h1
    exact (smul_right_injective _ (char_ne_zero ψ _) h1).symm
  neg_mem' := by
    rintro u ⟨hu, h⟩
    refine ⟨neg_mem hu, ?_⟩
    have h1 := heisO_heisO ψ (-u) u f
    have h2 := sgnW_add ψ hw (hΛ (-u) (neg_mem hu) u hu)
    rw [neg_add_cancel, sgnW_zero, mul_one] at h2
    rw [h, heisO_smul, neg_add_cancel, heisO_zero, h2, mul_comm, mul_smul] at h1
    exact smul_right_injective _ (char_ne_zero ψ _) h1

theorem incA_smul_finTens {m n : ℕ} (x : D.host.E) (α : Af D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    incA D x • finTens α M = finTens α (x • M) := by
  ext i j
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] x : AE D) * pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j =
    pairA D.host.F 0 α ⊗ₜ[D.host.F] (x * M i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem smul_mem_latO {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} (c : 𝓞 D.host.E)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    incA D (c : D.host.E) • u ∈ latO S T LS LT fun _ => True := by
  refine latO_induction (p := fun u => incA D (c : D.host.E) • u ∈ latO S T LS LT fun _ => True) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    rw [incA_smul_finTens]
    exact finTens_mem_latO hα (smul_mem_latRat c hM)
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

theorem isFinOf_iff (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (u : WO S T) :
    IsFinOf S T γ u ↔ u = finTens 1 γ := by
  constructor
  · rintro ⟨h1, h2⟩
    ext i j
    refine SplitScalar.adele_ext ?_ ?_
    · exact (congrFun (congrFun h1 i) j).trans (infPart_pair _ _).symm
    · exact congrFun (congrFun h2 i) j
  · rintro rfl
    exact ⟨Matrix.ext fun i j => infPart_pair _ _, rfl⟩

theorem continuous_finTens {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    Continuous fun α : Af D.host.F => finTens α M := by
  have hp : Continuous fun α : Af D.host.F => pairA D.host.F 0 α := continuous_const.prodMk continuous_id
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have e : (fun α : Af D.host.F => finTens α M i j) = fun α => pairA D.host.F 0 α • incA D (M i j) := by
    funext α
    change pairA D.host.F 0 α ⊗ₜ[D.host.F] M i j = pairA D.host.F 0 α • ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i j)
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e]
  exact Continuous.smul (g := fun _ : Af D.host.F => incA D (M i j)) hp continuous_const

theorem pair_tmul_smul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (a : F) (x : E) :
    pairA F 0 (algebraMap F (Af F) a) ⊗ₜ[F] x = pairA F 0 1 ⊗ₜ[F] (a • x) := by
  rw [← TensorProduct.smul_tmul]
  congr 1
  exact Prod.ext (smul_zero _).symm (Algebra.algebraMap_eq_smul_one a)

theorem finTens_algebraMap {m n : ℕ} (a : D.host.F) (M : Matrix (Fin m) (Fin n) D.host.E) :
    finTens (algebraMap D.host.F (Af D.host.F) a) M = finTens 1 (a • M) := by
  ext i j
  change pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) a) ⊗ₜ[D.host.F] M i j =
    pairA D.host.F 0 1 ⊗ₜ[D.host.F] (a • M i j)
  exact pair_tmul_smul a (M i j)

theorem sgn_of_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) (w : AE D) {f : WO S T → ℂ} (hf : Continuous f)
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    (h : ∀ γ, finTens 1 γ ∈ (latO S T LS LT fun _ => True) →
      heisO ψ S T (finTens 1 γ) f = sgnW ψ w (finTens 1 γ : WO S T) • f)
    {α : Af D.host.F} (hα : α ∈ intAf D.host.F) {M : Matrix (Fin T.rank) (Fin S.rank) D.host.E}
    (hM : M ∈ latRat S T LS LT) : heisO ψ S T (finTens α M) f = sgnW ψ w (finTens α M : WO S T) • f := by
  have hc := continuous_finTens (D := D) M
  funext x
  refine IntDense.mem_of_isClosed D.host.F
    (C := {α | heisO ψ S T (finTens α M) f x = (sgnW ψ w (finTens α M : WO S T) • f) x})
    (isClosed_eq ?_ ?_) (fun a => ?_) α hα
  · exact (hψ.comp (continuous_const.mul (SplitScalar.continuous_symplO S T continuous_const hc))).mul
      (hf.comp (continuous_const.add hc))
  · have hc' : Continuous fun α : Af D.host.F => w • finTens α M :=
      continuous_pi fun i => continuous_pi fun j =>
        continuous_const.mul ((continuous_apply j).comp ((continuous_apply i).comp hc))
    exact (hψ.comp (continuous_const.mul (SplitScalar.continuous_symplO S T hc hc'))).mul continuous_const
  · have hm : finTens (algebraMap D.host.F (Af D.host.F) (a : D.host.F)) M ∈ latO S T LS LT fun _ => True :=
      finTens_mem_latO (fun v => by
        rw [AlgHom.commutes]; exact v.coe_algebraMap_mem (𝓞 D.host.F) D.host.F a) hM
    rw [Set.mem_setOf_eq, finTens_algebraMap] at *
    exact congrFun (h _ hm) x

theorem sum_EF {r : ℕ} (hr : T.rank = r) (X : Data D.host.E r) (hS : S.gram = 1) (hX : IsMod T hr X)
    (γ γ' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ∑ k, EF X (colsR hr γ k) (colsR hr γ' k) = -Algebra.trace ℚ D.host.E (D.host.xi0 * hRat S T γ γ') := by
  subst hr
  simp only [EF_def]
  rw [← map_sum, ← map_neg, hX.kap, ← Finset.mul_sum]
  congr 1
  rw [show ∀ x : D.host.E, -(-(2 * x) / 2) = x from fun x => by ring, ← mul_neg]
  congr 1
  rw [hRat, hS, inv_one, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Matrix.one_apply_ne hb.symm]) (by simp), herm, Finset.sum_comm,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [hX.model.1, Matrix.one_apply_eq]
  change γ d a * -(T.gram c d) * star (γ' c a) = _
  ring

theorem sgnW_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {r : ℕ} (hr : T.rank = r)
    (X : Data D.host.E r) (hS : S.gram = 1) (hX : IsMod T hr X) (w : D.host.E)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    sgnW ψ (incA D w) (finTens 1 γ : WO S T) * epsW X w (colsR hr γ) = 1 := by
  have h1 := sum_EF hr X hS hX γ (w • γ)
  have h2 : epsW X w (colsR hr γ) = cexp (Real.pi * I * ((∑ k, EF X (colsR hr γ k) (colsR hr (w • γ) k) : ℚ) : ℂ)) := rfl
  have h3 : symplOH S T (finTens 1 γ) (finTens 1 (w • γ)) = pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F)
      (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * hRat S T γ (w • γ)))) := by
    rw [symplOH, symplO_finTens, one_mul, one_mul, RingHom.map_mul]
    exact Prod.ext (mul_zero _) rfl
  rw [h2, h1, sgnW, incA_smul_finTens, h3, GlobalTheory.T.stdChar_finitePart_rational_eq_exp_trace D ψ hψ, ← Complex.exp_add,
    show (1 / 2 : D.host.F) = algebraMap ℚ D.host.F (1 / 2) by simp, ← Algebra.smul_def, map_smul,
    Algebra.trace_trace, smul_eq_mul]
  refine Eq.trans (congrArg cexp ?_) Complex.exp_zero
  push_cast
  ring

theorem isLatVac_iff_epsW : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSelfDualC V ΛV → IsSelfDualC W ΛW → ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → (IsLatVac (heisO ψ V W) (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) f ↔ ∀ γ u, IsFinOf V W γ u → u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) → heisO ψ V W u f = epsW X (H.w0 : D.host.E) (colsR hr γ) • f) := by
  intro D ψ θ V W r g hr X bas idx hψ _ hV _ hX _ H hH ΛV ΛW hΛV hΛW f hf
  have hw0 : (H.w0 : D.host.E) + star (H.w0 : D.host.E) = 1 := by
    have h1 : 2 * (H.w0 : D.host.E) = 1 + D.host.sqrtMinusD := by
      rw [← hH]; exact congrArg Subtype.val H.two_weight_eq_one_add_root
    have h2 := congrArg star h1
    rw [star_mul', star_add, star_one, star_ofNat, SplitIdem.star_eq_conj D D.host.sqrtMinusD,
      D.host.conj_sqrtMinusD] at h2
    linear_combination (1 / 2 : D.host.E) * h1 + (1 / 2 : D.host.E) * h2
  have hw : incA D (H.w0 : D.host.E) + cA D (incA D (H.w0 : D.host.E)) = 1 := by
    rw [DualPairCheck.cA_incA, ← RingHom.map_add, hw0, RingHom.map_one]
  have hΛ : ∀ u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
      ∀ u' ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
        ψ (symplO V W u (incA D (H.w0 : D.host.E) • u')) = 1 :=
    fun u hu u' hu' => char_sympl_eq_one hψ hΛV hΛW hu (smul_mem_latO H.w0 hu')
  have he : ∀ γ, (finTens 1 γ : WO V W) ∈
      (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) →
      epsW X (H.w0 : D.host.E) (colsR hr γ) = sgnW ψ (incA D (H.w0 : D.host.E)) (finTens 1 γ : WO V W) := by
    intro γ hγ
    have h1 := sgnW_rat hψ hr X hV hX (H.w0 : D.host.E) γ
    have h2 : sgnW ψ (incA D (H.w0 : D.host.E)) (finTens 1 γ : WO V W) *
        sgnW ψ (incA D (H.w0 : D.host.E)) (finTens 1 γ : WO V W) = 1 := char_half (hΛ _ hγ _ hγ)
    exact mul_left_cancel₀ (char_ne_zero ψ _) (h1.trans h2.symm)
  constructor
  · intro hv γ u hu hm
    rw [isFinOf_iff] at hu
    subst hu
    rw [he γ hm]
    exact (le_of_two_of_half (sgnGroup ψ hw _ hΛ f)
      (fun u hu => ⟨nsmul_mem hu 2, by rw [hv.1 u hu, sgnW_two ψ hw (hΛ u hu u hu), one_smul]⟩)
      (fun e he u hu hh => ⟨hu, by rw [hv.2 e he u hu hh, sgnW_half ψ _ he hh, one_smul]⟩) hm).2
  · intro h
    have hall : ∀ u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
        u ∈ sgnGroup ψ hw _ hΛ f := fun u hu =>
      latO_induction (p := fun u => u ∈ sgnGroup ψ hw _ hΛ f)
        (fun α hα M hM => ⟨finTens_mem_latO hα hM, sgn_of_rat hψ.1.1 _ hf.cont
          (fun γ hγ => by rw [h γ _ ((isFinOf_iff _ _).2 rfl) hγ, he γ hγ]) hα hM⟩)
        (zero_mem _) (fun _ _ => add_mem) (fun _ => neg_mem) hu
    refine ⟨fun u hu => ?_, fun e hs u hu hh => ?_⟩
    · rw [(hall _ (nsmul_mem hu 2)).2, sgnW_two ψ hw (hΛ u hu u hu), one_smul]
    · rw [(hall _ hu).2, sgnW_half ψ _ hs hh, one_smul]

end GlobalTheory.VacSign

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicities
section
noncomputable section

open GlobalTheory.CuspMult

namespace GlobalTheory.RepCount

variable {H W X : Type} [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]

def modMap {σ : Representation ℂ H W} {ρ : Representation ℂ H X} (f : W →ₗ[ℂ] X)
    (hf : ∀ g s, f (σ g s) = ρ g (f s)) : σ.asModule →ₗ[MonoidAlgebra ℂ H] ρ.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule σ ρ
    (f.intertwiningMap_of_isIntertwiningMap σ ρ hf)

theorem modMap_apply {σ : Representation ℂ H W} {ρ : Representation ℂ H X} (f : W →ₗ[ℂ] X)
    (hf : ∀ g s, f (σ g s) = ρ g (f s)) (x : σ.asModule) :
    ρ.asModuleEquiv (modMap f hf x) = f (σ.asModuleEquiv x) := rfl

def subEquiv {ρ : Representation ℂ H X} (U : Subrepresentation ρ) :
    U.toRepresentation.asModule ≃ₗ[MonoidAlgebra ℂ H] U.asSubmodule :=
  LinearEquiv.ofBijective
    ((modMap (σ := U.toRepresentation) (ρ := ρ) U.toSubmodule.subtype (fun _ _ => rfl)).codRestrict
      U.asSubmodule (fun x => (U.toRepresentation.asModuleEquiv x).2))
    ⟨fun a b h => U.toRepresentation.asModuleEquiv.injective (Subtype.ext (congrArg Subtype.val h)),
     fun y => ⟨U.toRepresentation.asModuleEquiv.symm ⟨ρ.asModuleEquiv y.1, y.2⟩, rfl⟩⟩

variable [TopologicalSpace H]

theorem isAdmissible_of_injective {σ : Representation ℂ H W} {ρ : Representation ℂ H X}
    (f : W →ₗ[ℂ] X) (hf : ∀ g s, f (σ g s) = ρ g (f s)) (hi : Function.Injective f)
    (h : GlobalTheory.PRep.IsAdmissible ρ) : GlobalTheory.PRep.IsAdmissible σ := by
  refine ⟨fun v => ?_, fun K hK hK' => ?_⟩
  · have : {g : H | σ g v = v} = {g : H | ρ g (f v) = f v} := by
      ext g
      simp only [Set.mem_setOf_eq, ← hf, hi.eq_iff]
    rw [this]
    exact h.1 _
  · haveI := h.2 K hK hK'
    refine FiniteDimensional.of_injective
      (f.restrict (p := GlobalTheory.PRep.fixed σ K) (q := GlobalTheory.PRep.fixed ρ K) (fun v hv k => ?_)) ?_
    · rw [← hf, hv k, map_smul]
    · intro a b hab
      exact Subtype.ext (hi (congrArg Subtype.val hab))

def pieces (ρ : Representation ℂ H X) (C : Submodule ℂ X) :
    Set (Submodule (MonoidAlgebra ℂ H) ρ.asModule) :=
  {m | ∃ U : Subrepresentation ρ, (U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧
    GlobalTheory.PRep.IsAdmissible U.toRepresentation) ∧ U.asSubmodule = m}

theorem simple_of_mem_pieces {ρ : Representation ℂ H X} {C : Submodule ℂ X}
    {m : Submodule (MonoidAlgebra ℂ H) ρ.asModule} (hm : m ∈ pieces ρ C) :
    IsSimpleModule (MonoidAlgebra ℂ H) m := by
  obtain ⟨U, ⟨-, hU, -⟩, rfl⟩ := hm
  exact IsSimpleModule.congr (subEquiv U).symm

theorem mem_sSup_pieces_of_mem {ρ : Representation ℂ H X} {C : Submodule ℂ X} {x : X}
    (hx : x ∈ irrSum ρ C) : ρ.asModuleEquiv.symm x ∈ sSup (pieces ρ C) := by
  have : irrSum ρ C ≤ ((sSup (pieces ρ C)).restrictScalars ℂ).comap
      ρ.asModuleEquiv.symm.toLinearMap := by
    refine iSup₂_le fun U hU y hy => ?_
    exact (le_sSup (s := pieces ρ C) ⟨U, hU, rfl⟩ : U.asSubmodule ≤ _) hy
  exact this hx

theorem mem_of_mem_sSup_pieces {ρ : Representation ℂ H X} {C : Submodule ℂ X} {x : ρ.asModule}
    (hx : x ∈ sSup (pieces ρ C)) : ρ.asModuleEquiv x ∈ C := by
  rw [sSup_eq_iSup'] at hx
  refine Submodule.iSup_induction _ (motive := fun x => ρ.asModuleEquiv x ∈ C) hx ?_ ?_ ?_
  · rintro ⟨_, U, hU, rfl⟩ y hy
    exact hU.1 hy
  · simp
  · intro a b ha hb
    rw [map_add]
    exact C.add_mem ha hb

theorem semisimple_sSup_pieces (ρ : Representation ℂ H X) (C : Submodule ℂ X) :
    IsSemisimpleModule (MonoidAlgebra ℂ H) ↥(sSup (pieces ρ C)) := by
  rw [sSup_eq_iSup]
  refine isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m hm => ?_
  haveI := simple_of_mem_pieces hm
  infer_instance

theorem apply_mem_irrSum {σ : Representation ℂ H W} {ρ : Representation ℂ H X} {C : Submodule ℂ X}
    (h1 : σ.IsIrreducible) (h2 : GlobalTheory.PRep.IsAdmissible σ) {f : W →ₗ[ℂ] X}
    (hf : f ∈ homInto σ ρ C) (s : W) : f s ∈ irrSum ρ C := by
  let F := f.intertwiningMap_of_isIntertwiningMap σ ρ hf.2
  rcases Representation.IsIrreducible.injective_or_eq_zero F with hi | h0
  · have hi' : Function.Injective f := hi
    let e : W ≃ₗ[ℂ] F.range.toSubmodule := LinearEquiv.ofInjective f hi'
    have he : ∀ g s, e (σ g s) = F.range.toRepresentation g (e s) :=
      fun g s => Subtype.ext (hf.2 g s)
    have he' : ∀ g s, e.symm (F.range.toRepresentation g s) = σ g (e.symm s) := by
      intro g s
      rw [LinearEquiv.symm_apply_eq, he, e.apply_symm_apply]
    have hirr : F.range.toRepresentation.IsIrreducible := by
      rw [Representation.irreducible_iff_isSimpleModule_asModule]
      exact IsSimpleModule.congr
        (LinearEquiv.ofBijective (modMap e.symm.toLinearMap he') e.symm.bijective)
    have hle : F.range.toSubmodule ≤ irrSum ρ C :=
      le_iSup₂_of_le (f := fun (U : Subrepresentation ρ) (_ : U.toSubmodule ≤ C ∧
        U.toRepresentation.IsIrreducible ∧ GlobalTheory.PRep.IsAdmissible U.toRepresentation) =>
          U.toSubmodule) F.range ⟨by rintro _ ⟨t, rfl⟩; exact hf.1 t, hirr,
            isAdmissible_of_injective e.symm.toLinearMap he' e.symm.injective h2⟩ le_rfl
    exact hle ⟨s, rfl⟩
  · have : f s = 0 := DFunLike.congr_fun h0 s
    rw [this]
    exact Submodule.zero_mem _

theorem rank_homInto {σ : Representation ℂ H W} (ρ : Representation ℂ H X) (C : Submodule ℂ X)
    (h1 : σ.IsIrreducible) (h2 : GlobalTheory.PRep.IsAdmissible σ) :
    Module.rank ℂ (homInto σ ρ C) =
      Module.rank ℂ (σ.asModule →ₗ[MonoidAlgebra ℂ H] ↥(sSup (pieces ρ C))) := by
  refine LinearEquiv.rank_eq (LinearEquiv.ofBijective
    { toFun := fun f => (modMap f.1 f.2.2).codRestrict _
        (fun s => mem_sSup_pieces_of_mem (apply_mem_irrSum h1 h2 f.2 (σ.asModuleEquiv s)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } ⟨fun a b hab => ?_, fun g => ?_⟩)
  · ext s
    exact congrArg Subtype.val (LinearMap.congr_fun hab (σ.asModuleEquiv.symm s))
  · refine ⟨⟨ρ.asModuleEquiv.toLinearMap ∘ₗ
      (((sSup (pieces ρ C)).subtype ∘ₗ g).restrictScalars ℂ) ∘ₗ σ.asModuleEquiv.symm.toLinearMap,
      fun s => mem_of_mem_sSup_pieces (g _).2, fun x s => ?_⟩, rfl⟩
    change ρ.asModuleEquiv (g (σ.asModuleEquiv.symm (σ x s))).1 =
      ρ x (ρ.asModuleEquiv (g (σ.asModuleEquiv.symm s)).1)
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Submodule.coe_smul,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]

theorem exists_rep {ρ : Representation ℂ H X} {C : Submodule ℂ X}
    (U : Submodule (MonoidAlgebra ℂ H) ↥(sSup (pieces ρ C)))
    (hU : IsSimpleModule (MonoidAlgebra ℂ H) U) :
    ∃ V : Subrepresentation ρ, V.toRepresentation.IsIrreducible ∧
      GlobalTheory.PRep.IsAdmissible V.toRepresentation ∧
      Nonempty (U ≃ₗ[MonoidAlgebra ℂ H] V.toRepresentation.asModule) := by
  let e := Submodule.equivMapOfInjective _ (sSup (pieces ρ C)).injective_subtype U
  haveI : IsSimpleModule (MonoidAlgebra ℂ H) (U.map (sSup (pieces ρ C)).subtype) :=
    IsSimpleModule.congr e.symm
  haveI : ∀ m : pieces ρ C, IsSimpleModule (MonoidAlgebra ℂ H) m :=
    fun m => simple_of_mem_pieces m.2
  obtain ⟨_, ⟨V, hV, rfl⟩, ⟨e'⟩⟩ := (U.map (sSup (pieces ρ C)).subtype).linearEquiv_of_le_sSup
    (pieces ρ C) (Submodule.map_subtype_le _ _)
  exact ⟨V, hV.2.1, hV.2.2, ⟨(e.trans e').trans (subEquiv V).symm⟩⟩

def killedEquiv {ρ : Representation ℂ H X} {C : Submodule ℂ X} (I : Set (MonoidAlgebra ℂ H))
    (hC : IsDecomp ρ C) (ho : ∀ x ∈ killed ρ I, IsOpen {g : H | ρ g x = x}) :
    (C ⊓ killed ρ I : Submodule ℂ X) ≃ₗ[ℂ]
      GlobalTheory.SemisimpleCount.killed I ↥(sSup (pieces ρ C)) where
  toFun x := ⟨⟨ρ.asModuleEquiv.symm x.1, mem_sSup_pieces_of_mem (hC _ x.2.1 (ho _ x.2.2))⟩,
    fun r hr => Subtype.ext (mem_killed.1 x.2.2 r hr)⟩
  invFun y := ⟨ρ.asModuleEquiv y.1.1, mem_of_mem_sSup_pieces y.1.2,
    mem_killed.2 fun r hr => congrArg Subtype.val (y.2 r hr)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [TopologicalSpace H] in
theorem killed_ne_bot {σ : Representation ℂ H W} {I : Set (MonoidAlgebra ℂ H)} {S : Type}
    [AddCommGroup S] [Module (MonoidAlgebra ℂ H) S]
    (e : S ≃ₗ[MonoidAlgebra ℂ H] σ.asModule) {s : S} (hs : s ≠ 0) (hI : ∀ x ∈ I, x • s = 0) :
    killed σ I ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨σ.asModuleEquiv (e s), mem_killed.2 fun r hr => ?_, by simpa using hs⟩
  rw [← Representation.asModuleEquiv_map_smul, ← map_smul, hI r hr, map_zero, map_zero]

theorem finrank_inf_killed_eq : ∀ (H : Type) [Group H] [TopologicalSpace H] (X Y : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ H X) (ρ' : Representation ℂ H Y) (C : Submodule ℂ X) (C' : Submodule ℂ Y) (I : Set (MonoidAlgebra ℂ H)), IsDecomp ρ C → IsDecomp ρ' C' → (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ H W), σ.IsIrreducible → GlobalTheory.PRep.IsAdmissible σ → killed σ I ≠ ⊥ → Module.rank ℂ (homInto σ ρ C) = Module.rank ℂ (homInto σ ρ' C')) → (∀ x ∈ killed ρ I, IsOpen {g : H | ρ g x = x}) → (∀ y ∈ killed ρ' I, IsOpen {g : H | ρ' g y = y}) → FiniteDimensional ℂ (C ⊓ killed ρ I : Submodule ℂ X) → FiniteDimensional ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) → Module.finrank ℂ (C ⊓ killed ρ I : Submodule ℂ X) = Module.finrank ℂ (C' ⊓ killed ρ' I : Submodule ℂ Y) := by
  intro H _ _ X Y _ _ _ _ ρ ρ' C C' I hC hC' hm ho ho' f f'
  have e := killedEquiv I hC ho
  have e' := killedEquiv I hC' ho'
  rw [e.finrank_eq, e'.finrank_eq]
  refine GlobalTheory.SemisimpleCount.finrank_killed_eq (MonoidAlgebra ℂ H) _ _ I _ _
    (semisimple_sSup_pieces ρ C) (semisimple_sSup_pieces ρ' C') (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    e.finiteDimensional e'.finiteDimensional ?_ ?_
  · rintro U hU ⟨u, hu, h0, hI⟩
    obtain ⟨V, h1, h2, ⟨φ⟩⟩ := exists_rep U hU
    rw [GlobalTheory.SemisimpleCount.rank_hom_congr_left φ, GlobalTheory.SemisimpleCount.rank_hom_congr_left φ,
      ← rank_homInto ρ C h1 h2, ← rank_homInto ρ' C' h1 h2]
    exact hm _ _ h1 h2 (killed_ne_bot φ (s := ⟨u, hu⟩) (fun h => h0 (congrArg Subtype.val h))
      fun r hr => Subtype.ext (hI r hr))
  · rintro U hU ⟨u, hu, h0, hI⟩
    obtain ⟨V, h1, h2, ⟨φ⟩⟩ := exists_rep U hU
    rw [GlobalTheory.SemisimpleCount.rank_hom_congr_left φ, GlobalTheory.SemisimpleCount.rank_hom_congr_left φ,
      ← rank_homInto ρ C h1 h2, ← rank_homInto ρ' C' h1 h2]
    exact hm _ _ h1 h2 (killed_ne_bot φ (s := ⟨u, hu⟩) (fun h => h0 (congrArg Subtype.val h))
      fun r hr => Subtype.ext (hI r hr))

end GlobalTheory.RepCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSourceGlActionSymmetrisedSameSigns
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ColLie

theorem fockS_eq_colDer_of_same_signs : ∀ {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (Y : Matrix (Fin a) (Fin a) ℂ),
    (∀ i j, ε' i = ε j) →
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' Y = (GlobalTheory.ColLie.colDer τ Y : Module.End ℂ (PolF D b a)) + (((b : ℂ) / 2) * Y.trace) • 1 := by
  intro D a b τ ε ε' Y h
  have hs : ∀ (i : Fin b) (j k : Fin a), GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO τ ε ε' i j * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO τ ε ε' i k =
      (LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j) : PolF D b a) ∘ₗ
        (MvPolynomial.pderiv (τ, i, k)).toLinearMap : Module.End ℂ (PolF D b a)) := by
    intro i j k
    have hjk : ε j = ε k := (h i j).symm.trans (h i k)
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε j) * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε k) = 1 := by
      rw [hjk]; unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn; split_ifs <;> simp
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO
    rw [if_pos (h i j), if_pos (h i k), smul_mul_smul_comm, h1, one_smul]
    rfl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS GlobalTheory.ColLie.colDer
  simp only [hs, Finset.sum_add_distrib, smul_add, Finset.smul_sum]
  congr 1
  · rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin b)))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
  · simp only [smul_ite, smul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, Matrix.trace, Matrix.diag, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
    congr 1
    ring

end GlobalTheory.ColLie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HigherDegreeClassDiesOnFinerEtaleNeighbourhoodStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.higherDegree_class_dies_on_finer_etaleNeighbourhood : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsNbhd B A' f → ∀ (m i : ℤ), 2 ≤ m → ∀ z : Ht q (sp (Localization.Away (algebraMap B A' f))) m i, ∃ (A'' : Type) (_ : CommRing A'') (_ : Algebra B A'') (_ : Algebra.Etale B A'') (φ : A' →ₐ[B] A''), IsNbhd B A'' f ∧ pull _ (spMap (awayHom φ f)) _ _ z = 0 := by
  first | (exact @GlobalTheory.KillFiner.main) | (exact GlobalTheory.KillFiner.main) | (intros; apply GlobalTheory.KillFiner.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzRapidDecayColumnStatement
section
open Classical MeasureTheory NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_rapid_decay_column : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (r : ℕ) (f : SchwartzMap (Fin a → GlobalTheory.CuspRep.Cinf E) ℂ), GlobalTheory.JSW.IsRapidInf (volume : Measure (Fin a → GlobalTheory.CuspRep.Cinf E)) (fun x => f x) (GlobalTheory.JSW.colU r) := by
  first | exact @GlobalTheory.JSW.isRapidInf_colU | exact GlobalTheory.JSW.isRapidInf_colU | (intros; apply GlobalTheory.JSW.isRapidInf_colU <;> assumption)
end

