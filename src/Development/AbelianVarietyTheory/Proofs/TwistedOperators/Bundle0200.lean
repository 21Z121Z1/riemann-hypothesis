import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0261
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianPairingIntegralContDiffNeZeroDiag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaLocalFactorsStableHeisenbergAway
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceStable

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem symplO_of_place {p : Place D} {x y : WO S T} (hx : wAt p x = x) (hy : wAt p y = 0) : symplO S T x y = 0 := by
  rw [← hx, wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p, ← wAt_eq_smul, hy,
    GlobalTheory.SplitScalar.symplO_zero_right]

theorem wAt_wAt (p : Place D) (w : WO S T) : wAt p (wAt p w) = wAt p w := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p]

theorem wAt_wAt_ne {p q : Place D} (h : q ≠ p) (w : WO S T) : wAt q (wAt p w) = 0 := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 q p h, zero_smul]

theorem heisO_swap {u w : WO S T} (h : symplO S T u w = 0) (f : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T w f) = heisO ψ S T w (heisO ψ S T u f) := by
  rw [GlobalTheory.SplitScalar.heisO_comm, h, AddChar.map_zero_eq_one, one_smul]

theorem isLatVac_map {Λ : AddSubgroup (WO S T)} {A : (WO S T → ℂ) → WO S T → ℂ} {f : WO S T → ℂ}
    (h : ∀ u ∈ Λ, heisO ψ S T u (A f) = A (heisO ψ S T u f)) (hf : IsLatVac (heisO ψ S T) Λ f) :
    IsLatVac (heisO ψ S T) Λ (A f) :=
  ⟨fun u hu => by rw [h _ (Λ.nsmul_mem hu 2), hf.1 u hu], fun e he u hu hh => by rw [h u hu, hf.2 e he u hu hh]⟩

theorem latO_empty {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {P : FinPl D → Prop}
    (hP : ∀ v, ¬ P v) {u : WO S T} (hu : u ∈ latO S T LS LT P) : u = 0 := by
  have h : latO S T LS LT P ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨α, -, h0, a, -, s, -, t, -, rfl⟩
    have hα : α = 0 := RestrictedProduct.ext _ _ fun v => h0 v (hP v)
    subst hα
    refine AddSubgroup.mem_bot.2 (Matrix.ext fun i j => ?_)
    exact TensorProduct.zero_tmul _ _
  exact AddSubgroup.mem_bot.1 (h hu)

theorem wAt_lineAt (hθ : IsInfFam θ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    wAt (.inr τ) (lineAt θ τ z t : WO S T) = lineAt θ τ z t := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, h1, h2⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  obtain ⟨-, -, -, -, h3, -, h4⟩ := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  refine funext fun i => funext fun j => ?_
  show idem D (.inr τ) * lineAt θ τ z t i j = lineAt θ τ z t i j
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [← sub_eq_zero, ← RingHom.map_sub]
    refine GlobalTheory.FockCompare.ThetaCont.infPart_eq_zero hσ _ fun τ' => ?_
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul]
    by_cases h : τ' = τ
    · subst h
      rw [(h4 θ hθ τ').1, one_mul, sub_self]
    · have h5 : θ τ' (infPart D (lineAt θ τ z t i j)) = 0 := by
        have := h2 t τ'
        rw [if_neg h] at this
        exact congrFun (congrFun this i) j
      rw [h5, mul_zero, sub_self]
  · have h5 : finPart D (lineAt θ τ z t i j) = 0 := congrFun (congrFun (h1 t) i) j
    rw [RingHom.map_mul, h5, mul_zero]

theorem dRho_heisO (hθ : IsInfFam θ) {τ : D.what₂.Tau} {w : WO S T} (hw : wAt (.inr τ) w = 0)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (heisO ψ S T w g) =
      heisO ψ S T w (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g) := by
  funext x
  unfold Formalism.IndefR.Datum.dRho
  rw [heisO, ← deriv_const_mul_field]
  congr 1
  funext t
  rw [heisO_swap (symplO_of_place (wAt_lineAt hθ τ z t) hw)]
  rfl

theorem isFockVacAt_heisO (hθ : IsInfFam θ) {τ : D.what₂.Tau} {w : WO S T} (hw : wAt (.inr τ) w = 0)
    {J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ} {f : WO S T → ℂ}
    (hf : IsFockVacAt (heisO ψ S T) θ τ J f) : IsFockVacAt (heisO ψ S T) θ τ J (heisO ψ S T w f) := by
  intro z
  have h := congrArg (GlobalTheory.SplitScalar.heisL ψ S T w) (hf z)
  rw [annih, map_add, map_smul, map_zero] at h
  rw [annih, dRho_heisO hθ hw, dRho_heisO hθ hw]
  exact h

theorem heis_stable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (q : Place D) (w : WO S T), wAt q w = 0 → VacAt ψ θ S T sS sT ΛS ΛT q f → VacAt ψ θ S T sS sT ΛS ΛT q (heisO ψ S T w f)) ∧ ∀ (p : Place D), IsLocal ψ θ S T sS sT ΛS ΛT p f → (∀ w : WO S T, IsLocal ψ θ S T sS sT ΛS ΛT p (heisO ψ S T (wAt p w) f)) ∧ (∀ (c : ℂ) g, IsLocal ψ θ S T sS sT ΛS ΛT p g → IsLocal ψ θ S T sS sT ΛS ΛT p (c • f + g)) ∧ ∀ τ : D.what₂.Tau, p = .inr τ → ∀ z, IsLocal ψ θ S T sS sT ΛS ΛT p (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  intro D ψ θ S T sS sT ΛS ΛT hψ hθ f hf
  refine ⟨fun q w hw hv => ?_, fun p hp => ⟨fun w => ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _, ?_, fun τ hτ => ?_⟩,
    fun c g hg => ⟨GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul c hf) hg.1, ?_, fun τ hτ z => ?_⟩,
    fun τ hτ z => ⟨GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hf, ?_, fun τ' hτ' z' => ?_⟩⟩⟩
  · cases q with
    | inl v =>
      refine isLatVac_map (fun u hu => heisO_swap (symplO_of_place ?_ hw) f) hv
      have h := (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu (.inl v)).2.1
      exact (sub_eq_zero.1 (latO_empty (fun v' h' => h'.2 (by rw [h'.1])) h)).symm
    | inr τ => exact isFockVacAt_heisO hθ hw hv
  · refine isLatVac_map (fun u hu => (heisO_swap (symplO_of_place (wAt_wAt p w) ?_) f).symm) hp.2.1
    exact (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu p).2.2 fun _ h => h
  · exact isFockVacAt_heisO hθ (wAt_wAt_ne hτ w) (hp.2.2 τ hτ)
  · have key : ∀ u, heisO ψ S T u f = f → heisO ψ S T u g = g → heisO ψ S T u (c • f + g) = c • f + g := fun u h1 h2 => by
      rw [← GlobalTheory.SplitScalar.heisL_apply, map_add, map_smul, GlobalTheory.SplitScalar.heisL_apply, GlobalTheory.SplitScalar.heisL_apply, h1, h2]
    exact ⟨fun u hu => key _ (hp.2.1.1 u hu) (hg.2.1.1 u hu),
      fun e he u hu hh => key _ (hp.2.1.2 e he u hu hh) (hg.2.1.2 e he u hu hh)⟩
  · have h1 := hp.2.2 τ hτ z
    have h2 := hg.2.2 τ hτ z
    have hc := GlobalTheory.WeilVacMove.isTheta_smul c hf
    rw [annih] at h1 h2 ⊢
    rw [GlobalTheory.FockIndep.dRho_add hψ hθ _ _ hc hg.1, GlobalTheory.FockIndep.dRho_add hψ hθ _ _ hc hg.1,
      GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ c hf, GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ c hf, smul_add, smul_comm,
      add_add_add_comm, ← smul_add, h1, h2, smul_zero, add_zero]
  · refine isLatVac_map (fun u hu => (dRho_heisO hθ ?_ z f).symm) hp.2.1
    exact (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT _ u hu (.inr τ)).2.2 fun _ _ => Sum.inl_ne_inr
  · have hne : τ' ≠ τ := fun h => hτ' (by rw [h, hτ])
    have hc : ∀ y, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' y (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) =
        Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ' y f) := fun y => by
      rw [GlobalTheory.FockIndep.dRho_comm hψ hθ τ' y τ z hf, GlobalTheory.FockIndep.omDir, if_neg hne, Complex.ofReal_zero, mul_zero,
        zero_smul, zero_add]
    have ht := fun y => GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ' y hf
    have h1 := hp.2.2 τ' hτ' z'
    have h0 := GlobalTheory.FockIndep.dRho_smul hψ hθ τ z 0 hf
    rw [zero_smul, zero_smul] at h0
    rw [annih] at h1 ⊢
    rw [hc, hc, ← GlobalTheory.FockIndep.dRho_smul hψ hθ τ z _ (ht _),
      ← GlobalTheory.FockIndep.dRho_add hψ hθ τ z (ht _) (GlobalTheory.WeilVacMove.isTheta_smul _ (ht _)), h1, h0]

end GlobalTheory.PlaceStable

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameExistsSignCompat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameExists

theorem exists_signFrame {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian) (hd : IsUnit H.det) :
    ∃ (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P ∧ Pᴴ * Formalism.REAL.Jm ε * P = H := by
  let U : Matrix (Fin n) (Fin n) ℂ := hH.eigenvectorUnitary
  let l := hH.eigenvalues
  let S : Matrix (Fin n) (Fin n) ℂ := diagonal fun a => ((Real.sqrt |l a| : ℝ) : ℂ)
  have hs : H = U * diagonal (fun a => ((l a : ℝ) : ℂ)) * Uᴴ := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hS : Sᴴ * Formalism.REAL.Jm (fun a => decide (0 < l a)) * S = diagonal (fun a => ((l a : ℝ) : ℂ)) := by
    simp only [S, Formalism.REAL.Jm, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    funext a
    have h1 : ((Real.sqrt |l a| : ℝ) : ℂ) * ((Real.sqrt |l a| : ℝ) : ℂ) = ((|l a| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [mul_right_comm, h1]
    by_cases h : 0 < l a
    · simp [h, abs_of_pos h]
    · simp [h, abs_of_nonpos (not_lt.1 h)]
  have key : (S * Uᴴ)ᴴ * Formalism.REAL.Jm (fun a => decide (0 < l a)) * (S * Uᴴ) = H := by
    rw [hs, ← hS, conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  refine ⟨_, S * Uᴴ, ?_, key⟩
  rw [Matrix.isUnit_iff_isUnit_det]
  rw [← key, det_mul] at hd
  exact isUnit_of_mul_isUnit_right hd

theorem exists_perm_of_card {n : ℕ} {ε η : Fin n → Bool}
    (h : Nat.card {a // ε a = true} = Nat.card {a // η a = true}) :
    ∃ σ : Fin n ≃ Fin n, ∀ a, ε (σ a) = η a := by
  have hf : ∀ b : Bool, Nonempty ({a // η a = b} ≃ {a // ε a = b}) := by
    intro b
    rw [← Finite.card_eq]
    cases b
    · have e : ∀ θ : Fin n → Bool, Nat.card {a // θ a = false} = n - Nat.card {a // θ a = true} := by
        intro θ
        have := Fintype.card_subtype_compl (fun a => θ a = true)
        simp only [Nat.card_eq_fintype_card]
        simpa using this
      rw [e, e, h]
    · exact h.symm
  exact ⟨Equiv.ofFiberEquiv fun b => (hf b).some, fun a => Equiv.ofFiberEquiv_map _ a⟩

theorem exists_signCompat {n p q : ℕ} {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature (Pᴴ * Formalism.REAL.Jm ε * P) p q) :
    ∃ e : Fin p ⊕ Fin q ≃ Fin n, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat ε e := by
  obtain ⟨e, Q, hQ⟩ := h
  have hc : Formalism.UG.cT (starRingEnd ℂ) (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) =
      (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := rfl
  rw [hc] at hQ
  have h1 : (P * (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e e)ᴴ * Formalism.REAL.Jm ε *
      (P * (Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e e) =
      Formalism.REAL.Jm fun a => (e a).isLeft := by
    have h2 := congrArg (fun M => Matrix.submatrix M e e) hQ
    simp only [← submatrix_mul_equiv _ _ _ e, reindex_apply, submatrix_submatrix, Equiv.symm_comp_self,
      submatrix_id_id] at h2
    rw [conjTranspose_mul, conjTranspose_submatrix]
    simp only [Matrix.mul_assoc] at h2 ⊢
    rw [h2]
    ext a b
    obtain ⟨x, rfl⟩ := e.symm.surjective a
    obtain ⟨y, rfl⟩ := e.symm.surjective b
    simp only [submatrix_apply, Formalism.REAL.Jm, Formalism.UG.Jpq, diagonal_apply, Equiv.apply_symm_apply]
    rcases x with i | i <;> rcases y with j | j <;> simp [Matrix.one_apply]
    split_ifs <;> simp
  obtain ⟨σ, hσ⟩ := exists_perm_of_card (GlobalTheory.SignCount.card_true_eq _ h1)
  exact ⟨e.symm.trans σ, fun a => by simp [hσ]⟩

theorem frame_exists_signCompat : ∀ (D : D7) (V : HSp D), Nonempty (GlobalTheory.ChainFr.Fr V) ∧ ∀ (A : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau) (p q : ℕ), Formalism.UG.HasSignature (gramAt D V τ) p q → ∃ e : Ix p q ≃ Fin V.rank, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.SignCompat (A.ε τ) e := by
  intro D V
  refine ⟨?_, fun A τ p q h => exists_signCompat (P := A.fr τ) (by rw [A.fr_gram]; exact h)⟩
  choose ε P h1 h2 using fun τ => exists_signFrame (H := gramAt D V τ)
    (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  exact ⟨⟨ε, P, h1, h2⟩⟩

end GlobalTheory.FrameExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointJointAction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdjAct

variable {D : D7}

theorem mt_mul_mt_inv (T : HSp D) (g : GA D T) : Formalism.L2.Theta.mt T g * Formalism.L2.Theta.mt T g⁻¹ = 1 := by
  show (matHom T g).1 * (matHom T g⁻¹).1 = 1
  rw [map_inv]; exact (matHom T g).mul_inv

theorem mt_one_inv (S : HSp D) : Formalism.L2.Theta.mt S 1⁻¹ = 1 := by
  show (matHom S 1⁻¹).1 = 1
  simp

theorem cT_mt_gram (T : HSp D) (g : GA D T) : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g) * T.gram.map (incA D) =
    T.gram.map (incA D) * Formalism.L2.Theta.mt T g⁻¹ := by
  have hU : Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g) * T.gram.map (incA D) * Formalism.L2.Theta.mt T g =
      T.gram.map (incA D) := (show HR (AF D.host.F) D.sp.cm.sig T.gram from g).2
  calc _ = Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g) * T.gram.map (incA D) *
        (Formalism.L2.Theta.mt T g * Formalism.L2.Theta.mt T g⁻¹) := by rw [mt_mul_mt_inv, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, hU]

theorem finE_inv_val (T : HSp D) (g : GA D T) :
    ((Formalism.IndefR.Lev.finE T g)⁻¹).1 = (Formalism.L2.Theta.mt T g⁻¹).map (toEAf D) := by
  rw [← map_inv]; rfl

theorem conj_inv_val {n : ℕ} (β y : GL (Fin n) (EAf D)) :
    ((β⁻¹ * y * β)⁻¹ : GL (Fin n) (EAf D)).1 = (β⁻¹).1 * (y⁻¹).1 * β.1 := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]

theorem conj_transpose_mul (S T : HSp D) (g : GA D T) (x : WO S T) :
    ((HMul.hMul (Formalism.L2.Theta.mt T g) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) :
        Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ =
      HMul.hMul ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ
        (Formalism.UG.cT (cA D) (Formalism.L2.Theta.mt T g)) := by
  rw [Matrix.map_mul, Matrix.transpose_mul]; rfl

theorem assoc_swap {R : Type} [CommRing R] {s t : ℕ} (A : Matrix (Fin s) (Fin s) R) (X : Matrix (Fin s) (Fin t) R)
    (C G N : Matrix (Fin t) (Fin t) R) (h : C * G = G * N) : A * (X * C) * G = A * X * G * N := by
  simp only [Matrix.mul_assoc]
  rw [h]

theorem frame_assoc {R : Type} [CommRing R] {s t : ℕ} (bS : Matrix (Fin s) (Fin s) R) (Y : Matrix (Fin s) (Fin t) R)
    (N bT bTi : Matrix (Fin t) (Fin t) R) (hb : bT * bTi = 1) :
    bS * (Y * N) * bT = bS * Y * bT * (bTi * N * bT) := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc bT, hb, Matrix.one_mul]

theorem frMapAdj_actO : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (g : GA D T) (x : WO S T), frMapAdj S T βS βT (actO S T 1 g x) = HMul.hMul (frMapAdj S T βS βT x) ((βT⁻¹ * Formalism.IndefR.Lev.finE T g * βT)⁻¹ : GL (Fin T.rank) (EAf D)).1 := by
  intro D S T βS βT g x
  rw [frMapAdj, frMapAdj, actO, mt_one_inv, Matrix.mul_one, conj_transpose_mul, conj_inv_val, finE_inv_val,
    assoc_swap _ _ _ _ _ (cT_mt_gram T g), Matrix.map_mul]
  exact frame_assoc _ _ _ _ _ (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one])

end GlobalTheory.AdjAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameMatrixAdjointSupportedOfConjHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfSupp

theorem smul_mul_mul_of_smul_eq {R : Type} [CommRing R] {a b c d : Type} [Fintype b] [Fintype c]
    (r : R) (A : Matrix a b R) (N : Matrix b c R) (B : Matrix c d R) (h : r • N = N) :
    r • (A * N * B) = A * N * B := by
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]

theorem map_smul_of_smul_eq {R S : Type} [CommRing R] [CommRing S] {a b : Type} (f : R →+* S)
    (r : R) (N : Matrix a b R) (h : r • N = N) : f r • N.map f = N.map f := by
  ext k l
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [← map_mul]
  congr 1
  simpa [Matrix.smul_apply, smul_eq_mul] using congrFun (congrFun h k) l

theorem frMapAdj_supp : ∀ {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (x : WO S T), e * e = e → IsHalf (cA D e) x → ∀ i j, toEAf D e * frMapAdj S T βS βT x i j = frMapAdj S T βS βT x i j := by
  intro D S T βS βT e x he hx i j
  have hN : e • (x.map (cA D))ᵀ = (x.map (cA D))ᵀ := by
    ext k l
    simp only [Matrix.smul_apply, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul]
    have h1 := hx l k
    have h2 : cA D (x l k) = e * cA D (x l k) := by
      conv_lhs => rw [← h1]
      rw [map_mul, cA_cA]
    exact h2.symm
  have hM := smul_mul_mul_of_smul_eq e ((S.gram⁻¹).map (incA D)) _ (T.gram.map (incA D)) hN
  have hM' := map_smul_of_smul_eq (toEAf D) e _ hM
  have hF := smul_mul_mul_of_smul_eq (toEAf D e) (βS⁻¹).val _ βT.val hM'
  have := congrFun (congrFun hF i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this

end GlobalTheory.HalfSupp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussianPairingIntegralContDiffNeZeroDiagStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussianPairingIntegral_contDiff_ne_zero_diag : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ),
    (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) →
    (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => ∫ x, Complex.exp (M p.1 x x) * starRingEnd ℂ (Complex.exp (M p.2 x x)) ∂μ) ∧
    ∀ u, ∫ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M u x x)) ∂μ ≠ 0 := by
  first | exact @GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero | exact GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero | (intros; apply GlobalTheory.GaussPairing.gauss_pairing_smooth_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSizeRWordNeTopOfLe
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace
open scoped ENNReal

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {V : HSp D} {φ : GA D V → ℂ} {N : ℕ}

private lemma rderC_sum_smul (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (M : ι → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ (∑ a ∈ s, c a • M a) φ = ∑ a ∈ s, c a • RderC θ V τ (M a) φ := by
  induction s using Finset.induction_on with
  | empty =>

    have h0 := GlobalTheory.Mem.RealTranslate.RderC_smul hθ hs τ (0 : ℂ) (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    rw [zero_smul, zero_smul] at h0
    rw [Finset.sum_empty, Finset.sum_empty, h0]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, GlobalTheory.Mem.RealTranslate.RderC_add hθ hs,
      GlobalTheory.Mem.RealTranslate.RderC_smul hθ hs, ih]

theorem RderC_eq_sum_glDer (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z φ = ∑ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • glDer θ V (τ, a) φ := by

  have hZ : Z = ∑ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • Matrix.single a.1 a.2 (1 : ℂ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Fintype.sum_prod_type]

    rw [Fintype.sum_eq_single i fun x hx => by simp [hx], Fintype.sum_eq_single j fun y hy => by simp [hy]]
    simp
  conv_lhs => rw [hZ]
  rw [rderC_sum_smul hθ hs τ]
  simp only [glDer]

theorem Rder_eq_sum_glDer (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Rder θ V τ X φ = ∑ a : Fin V.rank × Fin V.rank, X a.1 a.2 • glDer θ V (τ, a) φ := by

  rw [← GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX φ]
  exact RderC_eq_sum_glDer hθ hs τ X

variable (θ V N) in

def wordFin (l : List (D.what₂.Tau × Fin V.rank × Fin V.rank)) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | f ∈ SmFun θ V ∧ growthSize V N (wordAct (glDer θ V) l f) ≠ ∞}
  add_mem' h h' := ⟨add_mem h.1 h'.1, by
    rw [(linOnSm_glWord l).add _ h.1 _ h'.1]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h.2, h'.2⟩) growthSize_add_le⟩
  zero_mem' := ⟨zero_mem _, by
    have := (linOnSm_glWord (θ := θ) l).smul 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    exact (growthSize_const (0 : ℂ)).trans_ne enorm_ne_top⟩
  smul_mem' c _ h := ⟨(SmFun θ V).smul_mem c h.1, by
    rw [(linOnSm_glWord l).smul, growthSize_smul]
    exact ENNReal.mul_ne_top enorm_ne_top h.2⟩

theorem rWord_mem_wordFin (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {d : ℕ} (h : growthSob θ V d N φ ≠ ∞)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (hl : IsLieWord V l) :
    ∀ l', l'.length + l.length ≤ d → rWord θ V l φ ∈ wordFin θ V N l' := by
  have hsum : wordSum (glDer θ V) (growthSize V N) d φ ≠ ∞ := h
  induction l with
  | nil =>

    intro l' hl'
    have hlen : l'.length ≤ d := by simpa using hl'
    have hw : rWord θ V [] φ = φ := wordAct_nil _ φ
    rw [hw]
    show φ ∈ SmFun θ V ∧ growthSize V N (wordAct (glDer θ V) l' φ) ≠ ∞
    exact ⟨hs, wordSum_ne_top_iff.1 hsum l' hlen⟩
  | cons p t ih =>

    intro l' hl'
    have hp : p.2 ∈ lieAt V p.1 := hl p (List.mem_cons_self ..)
    have ht : IsLieWord V t := fun q hq => hl q (List.mem_cons_of_mem p hq)
    have hψ : rWord θ V t φ ∈ SmFun θ V :=
      (show _ ∧ _ from ih ht [] (by simp only [List.length_cons, List.length_nil] at hl' ⊢; omega)).1
    have hw : rWord θ V (p :: t) φ = Rder θ V p.1 p.2 (rWord θ V t φ) := wordAct_cons _ p t φ
    rw [hw, Rder_eq_sum_glDer hθ hψ hp]
    refine sum_mem fun a _ => Submodule.smul_mem _ _ ?_
    have hm : growthSize V N (wordAct (glDer θ V) (l' ++ [(p.1, a)]) (rWord θ V t φ)) ≠ ∞ :=
      (show _ ∧ _ from ih ht (l' ++ [(p.1, a)])
        (by simp only [List.length_cons, List.length_append, List.length_nil] at hl' ⊢; omega)).2
    have he : wordAct (glDer θ V) (l' ++ [(p.1, a)]) (rWord θ V t φ) =
        wordAct (glDer θ V) l' (glDer θ V (p.1, a) (rWord θ V t φ)) := by
      rw [wordAct_append, wordAct_cons, wordAct_nil]
    show glDer θ V (p.1, a) (rWord θ V t φ) ∈ SmFun θ V ∧
      growthSize V N (wordAct (glDer θ V) l' (glDer θ V (p.1, a) (rWord θ V t φ))) ≠ ∞
    rw [← he]
    exact ⟨(linOnSm_RderC p.1 _).mem _ hψ, hm⟩

theorem growthSize_rWord_ne_top_of_le (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {d : ℕ} (h : growthSob θ V d N φ ≠ ∞)
    {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)} (hl : IsLieWord V l) (hd : l.length ≤ d) :
    growthSize V N (rWord θ V l φ) ≠ ∞ := by
  have hm := rWord_mem_wordFin hθ hs h l hl [] (by simpa using hd)
  have h2 : growthSize V N (wordAct (glDer θ V) [] (rWord θ V l φ)) ≠ ∞ := (show _ ∧ _ from hm).2
  rwa [wordAct_nil] at h2

theorem growthSize_rWord_ne_top (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (h : ∀ d, growthSob θ V d N φ ≠ ∞) :
    ∀ l, IsLieWord V l → growthSize V N (rWord θ V l φ) ≠ ∞ := fun l hl =>
  growthSize_rWord_ne_top_of_le hθ hs (h l.length) hl le_rfl

theorem unifModGrowth_iff_growthSob (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) :
    UnifModGrowth V θ φ ↔ ∃ N, ∀ d, growthSob θ V d N φ ≠ ∞ := by
  refine ⟨exists_growthSob_ne_top hs, ?_⟩
  rintro ⟨M, hM⟩
  exact unifModGrowth_iff.2 ⟨M, growthSize_rWord_ne_top hθ hs hM⟩

end GlobalTheory.Size

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergEquivariantIsometryStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_equivariant_isometry : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ), (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ w w' : V × V, (∀ (s : ℝ) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β (s • w).1 (s • w).2 ⇑f →
      ⇑(T g) = GlobalTheory.GaussLine.heisFun β (s • w').1 (s • w').2 ⇑(T f)) →
    ∀ f g : SchwartzMap V ℂ, (∀ x, g x = GlobalTheory.GaussLine.dHeis β w ⇑f x) →
    ∀ x, T g x = GlobalTheory.GaussLine.dHeis β w' ⇑(T f) x := by
  first | exact @GlobalTheory.HeisenbergL2.map_dHeis_of_isometry | exact GlobalTheory.HeisenbergL2.map_dHeis_of_isometry | (intros; apply GlobalTheory.HeisenbergL2.map_dHeis_of_isometry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergQuotientOpSumVacuumCommensurableSelfDuStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergQuotientOpSum_vacuum_commensurable_selfDualLattice : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ Λ : Submodule R X, SelfDual γ Λ → ∀ s : M, s ≠ 0 → Fixes W Λ s → Submodule.span ℂ (Set.range fun x => W x s) = ⊤ → ∀ Λ' : Submodule R X, SelfDual γ Λ' → idx Λ Λ' ≠ 0 → (sumOp W Λ Λ' s ≠ 0 ∧ Fixes W Λ' (sumOp W Λ Λ' s) ∧ Submodule.span ℂ (Set.range fun x => W x (sumOp W Λ Λ' s)) = ⊤) ∧ ∀ e : M →ₗ[ℂ] ℂ, e s = 1 → (∀ a ∈ Λ, ∀ v, e (W a v) = e v) → ∀ v, Fixes W Λ' v → v = e v • sumOp W Λ Λ' s := by
  first | exact @GlobalTheory.SphTheta.sumOp_vacuum_lift | exact GlobalTheory.SphTheta.sumOp_vacuum_lift | (intros; apply GlobalTheory.SphTheta.sumOp_vacuum_lift <;> assumption)
end

