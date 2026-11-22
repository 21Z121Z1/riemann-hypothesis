import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0015
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0213
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0244
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0230
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0282
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0135
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantPairingSmallerFockSource
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0281

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LipschitzBoundRealUnipotentAction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.RealMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Eqv

variable {D : D7}

theorem norm_sub_three {G : Type*} (φ : G → ℂ) (a b c d : G) :
    ‖φ d - φ a‖ ≤ ‖φ d - φ c‖ + ‖φ c - φ b‖ + ‖φ b - φ a‖ := by
  have e : φ d - φ a = (φ d - φ c) + (φ c - φ b) + (φ b - φ a) := by ring
  rw [e]
  exact norm_add₃_le

theorem lip_list {ι : Type*} (θ : InfFam D) {V : HSp D} (A : Fr V) (φ : GA D V → ℂ) (c : ℝ) (hL : Lip θ A φ c)
    (τf : ι → D.what₂.Tau) (Xf Yf : ι → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hX : ∀ i, Xf i ∈ lieAt V (τf i)) (hY : ∀ i, Yf i ∈ lieAt V (τf i)) (l : List ι) (y : GA D V) :
    ‖φ (y * (l.map fun i => oneP θ V (τf i) (Xf i) 1 * oneP θ V (τf i) (Yf i) 1).prod) - φ y‖ ≤
      c * (l.map fun i => hsn (A.fr (τf i) * Xf i * (A.fr (τf i))⁻¹) +
        hsn (A.fr (τf i) * Yf i * (A.fr (τf i))⁻¹)).sum := by
  induction l generalizing y with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have h1 := hL y (τf i) (Xf i) (hX i) 1
    have h2 := hL (y * oneP θ V (τf i) (Xf i) 1) (τf i) (Yf i) (hY i) 1
    have h3 := ih (y * oneP θ V (τf i) (Xf i) 1 * oneP θ V (τf i) (Yf i) 1)
    rw [abs_one, mul_one] at h1 h2
    rw [← mul_assoc, ← mul_assoc]
    refine (norm_sub_three φ y (y * oneP θ V (τf i) (Xf i) 1)
      (y * oneP θ V (τf i) (Xf i) 1 * oneP θ V (τf i) (Yf i) 1) _).trans ?_
    rw [show ∀ a b s : ℝ, c * (a + b + s) = c * s + c * b + c * a from fun a b s => by ring]
    linarith

theorem list_prod_mulSingle {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Monoid (M i)] (x : ∀ i, M i)
    (l : List ι) (hl : l.Nodup) (w : ι) :
    (l.map fun i => Pi.mulSingle i (x i)).prod w = if w ∈ l then x w else 1 := by
  first
  | exact @_root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply
  | exact _root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply
  | (apply _root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProdMapMulSingle.prod_map_mulSingle_apply ..)

theorem conj_cancel {n : ℕ} {P M N : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : P * M * P⁻¹ = P * N * P⁻¹) :
    M = N := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have e := congrArg (fun Q => P⁻¹ * Q * P) h
  simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul _ hd,
    Matrix.mul_one] using e

theorem conj_back {n : ℕ} (Q M : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) : Q * (Q⁻¹ * M * Q⁻¹⁻¹) * Q⁻¹ = M := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hQ
  rw [Matrix.nonsing_inv_nonsing_inv Q hd]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ hd]

def expUJ {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) : Formalism.REAL.UJ ε :=
  ⟨(Matrix.isUnit_exp X).unit, by
    have h := Formalism.REAL.exp_indefinite_unitary_holds n ε X hX 1
    show Formalism.REAL.inUJ ε (NormedSpace.exp X)
    simpa using h⟩

theorem isAtTau_unique (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (fr : UI.Frames D V) {τ : D.what₂.Tau}
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} {h h' : GA D V} (hh : IsAtTau θ V τ g h) (hh' : IsAtTau θ V τ g h') :
    h = h' := by
  obtain ⟨-, h2, -⟩ := GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr
  have he : ∀ τ', infMat D.sp.cm.sig V.gram (θ τ') h = infMat D.sp.cm.sig V.gram (θ τ') h' := fun τ' => by
    by_cases e : τ' = τ
    · subst e; rw [hh.2.1, hh'.2.1]
    · rw [hh.2.2 τ' e, hh'.2.2 τ' e]
  have hx : UI.brg fr ((UI.brg fr).symm h) = h := (UI.brg fr).apply_symm_apply h
  have hx' : UI.brg fr ((UI.brg fr).symm h') = h' := (UI.brg fr).apply_symm_apply h'
  have hxx : (UI.brg fr).symm h = (UI.brg fr).symm h' := by
    refine Prod.ext (funext fun (v : InfinitePlace D.host.F) => ?_) ?_
    · have a := h2 ((UI.brg fr).symm h) ((Formalism.L2.Host.tauPl D).symm v) _ rfl
      have a' := h2 ((UI.brg fr).symm h') ((Formalism.L2.Host.tauPl D).symm v) _ rfl
      rw [Equiv.apply_symm_apply] at a a'
      rw [hx] at a
      rw [hx'] at a'
      have e2 := a.symm.trans ((he _).trans a')
      exact Subtype.ext (Units.ext (conj_cancel (fr.unit v) e2))
    · rw [(brg_mem_GinfC fr _).1 (by rw [hx]; exact hh.1), (brg_mem_GinfC fr _).1 (by rw [hx']; exact hh'.1)]
  rw [← hx, ← hx', hxx]

open Classical in

theorem isAtTau_brg (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (fr : UI.Frames D V) (v : InfinitePlace D.host.F)
    (a : Formalism.REAL.UJ (fr.ε v)) :
    IsAtTau θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Formalism.MainNotions.S.uMat a * (fr.P v)⁻¹)
      (UI.brg fr ((Pi.mulSingle v a : (UI.instV fr).Ginf), 1)) := by
  classical
  obtain ⟨-, h2, -⟩ := GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr
  have hs : ∀ w : InfinitePlace (UI.instV fr).F, w = v → Formalism.MainNotions.S.uMat ((Pi.mulSingle v a : (UI.instV fr).Ginf) w) = Formalism.MainNotions.S.uMat a := by
    rintro w rfl
    exact congrArg Formalism.MainNotions.S.uMat
      (Pi.mulSingle_eq_same (M := fun w : InfinitePlace (UI.instV fr).F => Formalism.REAL.UJ ((UI.instV fr).ε w)) w a)
  have hn : ∀ w : InfinitePlace (UI.instV fr).F, w ≠ v → Formalism.MainNotions.S.uMat ((Pi.mulSingle v a : (UI.instV fr).Ginf) w) = 1 := by
    intro w hw
    exact (congrArg Formalism.MainNotions.S.uMat
      (Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace (UI.instV fr).F => Formalism.REAL.UJ ((UI.instV fr).ε w)) hw a)).trans rfl
  refine ⟨(brg_mem_GinfC fr _).2 rfl, ?_, fun τ' hτ' => ?_⟩
  · have e := h2 ((Pi.mulSingle v a : (UI.instV fr).Ginf), 1) ((Formalism.L2.Host.tauPl D).symm v) (Formalism.MainNotions.S.uMat a)
      (hs _ (Equiv.apply_symm_apply _ _)).symm
    rw [e]
    simp only [Equiv.apply_symm_apply]
  · have hw : Formalism.L2.Host.tauPl D τ' ≠ v := fun hv => hτ' (by rw [← hv, Equiv.symm_apply_apply])
    have e := h2 ((Pi.mulSingle v a : (UI.instV fr).Ginf), 1) τ' 1 (hn _ hw).symm
    rw [e]
    have hd := (Matrix.isUnit_iff_isUnit_det _).1 (fr.unit (Formalism.L2.Host.tauPl D τ'))
    rw [Matrix.mul_one, Matrix.mul_nonsing_inv _ hd]

open Classical in

theorem oneP_eq_brg (θ : InfFam D) (hθ : IsInfFam θ) {V : HSp D} (fr : UI.Frames D V) (v : InfinitePlace D.host.F)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (a : Formalism.REAL.UJ (fr.ε v))
    (ha : NormedSpace.exp X = fr.P v * Formalism.MainNotions.S.uMat a * (fr.P v)⁻¹) :
    oneP θ V ((Formalism.L2.Host.tauPl D).symm v) X 1 = UI.brg fr ((Pi.mulSingle v a : (UI.instV fr).Ginf), 1) := by
  have hc := isAtTau_brg θ hθ fr v a
  rw [← ha, ← one_smul ℝ X] at hc
  have hex : ∃ x, IsAtTau θ V ((Formalism.L2.Host.tauPl D).symm v) (NormedSpace.exp ((1 : ℝ) • X)) x := ⟨_, hc⟩
  unfold oneP atTau
  rw [dif_pos hex]
  exact isAtTau_unique θ hθ fr hex.choose_spec hc

theorem map_prod_pairs {ι G H : Type*} [Monoid G] [Monoid H] (f : G →* H) (l : List ι) (a b : ι → G) :
    f (l.map fun i => a i * b i).prod = (l.map fun i => f (a i) * f (b i)).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

theorem conj_mem_lieAt {V : HSp D} (fr : UI.Frames D V) (v : InfinitePlace D.host.F)
    {M : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hM : Formalism.REAL.inG (fr.ε v) M) :
    fr.P v * M * (fr.P v)⁻¹ ∈ lieAt V ((Formalism.L2.Host.tauPl D).symm v) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (fr.unit v)
  have e1 : ((fr.P v)⁻¹)ᴴ * (fr.P v)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  have hG : gramAt D V ((Formalism.L2.Host.tauPl D).symm v) =
      ((fr.P v)⁻¹)ᴴ * Formalism.REAL.Jm (fr.ε v) * (fr.P v)⁻¹ := by
    rw [← fr.spec v]
    calc gramAt D V ((Formalism.L2.Host.tauPl D).symm v) = V.gram.map (UI.phiV D v) := rfl
      _ = ((fr.P v)⁻¹)ᴴ * (fr.P v)ᴴ * V.gram.map (UI.phiV D v) * (fr.P v * (fr.P v)⁻¹) := by
        rw [e1, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e2 : ∀ W : Matrix (Fin V.rank) (Fin V.rank) ℂ, (fr.P v)ᴴ * (((fr.P v)⁻¹)ᴴ * W) = W := fun W => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hd, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have e3 : ∀ W : Matrix (Fin V.rank) (Fin V.rank) ℂ, (fr.P v)⁻¹ * (fr.P v * W) = W := fun W =>
    Matrix.nonsing_inv_mul_cancel_left _ _ hd
  show _ * _ + _ * _ = 0
  rw [hG]
  have key : (fr.P v * M * (fr.P v)⁻¹)ᴴ * (((fr.P v)⁻¹)ᴴ * Formalism.REAL.Jm (fr.ε v) * (fr.P v)⁻¹) +
      ((fr.P v)⁻¹)ᴴ * Formalism.REAL.Jm (fr.ε v) * (fr.P v)⁻¹ * (fr.P v * M * (fr.P v)⁻¹) =
      ((fr.P v)⁻¹)ᴴ * (Mᴴ * Formalism.REAL.Jm (fr.ε v) + Formalism.REAL.Jm (fr.ε v) * M) * (fr.P v)⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, e2, e3, Matrix.mul_add, Matrix.add_mul]
  rw [key, show Mᴴ * Formalism.REAL.Jm (fr.ε v) + Formalism.REAL.Jm (fr.ε v) * M = 0 from hM, Matrix.mul_zero, Matrix.zero_mul]

open Classical in

theorem lip_move_real : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (φ : GA D V → ℂ) (c : ℝ), 0 ≤ c → Lip θ A φ c → ∀ (u : (Formalism.IndefR.Eqv.UI.instV fr).Ginf) (Av Z : InfinitePlace D.host.F → Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ v, Formalism.REAL.inG (fr.ε v) (Av v) ∧ Formalism.REAL.inG (fr.ε v) (Z v)) → (∀ v, Formalism.MainNotions.S.uMat (u v) = NormedSpace.exp (Av v) * NormedSpace.exp (Z v)) → ∀ y : GA D V, ‖φ (y * Formalism.IndefR.Eqv.UI.brg fr (u, 1)) - φ y‖ ≤ c * ∑ v, (Real.sqrt (Formalism.REAL.hs (Av v)) + Real.sqrt (Formalism.REAL.hs (Z v))) := by
  intro D θ hθ V A fr hP φ c hc hL u Av Z hAZ hu y
  have hX : ∀ v, fr.P v * Av v * (fr.P v)⁻¹ ∈ lieAt V ((Formalism.L2.Host.tauPl D).symm v) :=
    fun v => conj_mem_lieAt fr v (hAZ v).1
  have hY : ∀ v, fr.P v * Z v * (fr.P v)⁻¹ ∈ lieAt V ((Formalism.L2.Host.tauPl D).symm v) :=
    fun v => conj_mem_lieAt fr v (hAZ v).2
  have hXe : ∀ v, oneP θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Av v * (fr.P v)⁻¹) 1 =
      UI.brg fr ((Pi.mulSingle v (expUJ (hAZ v).1) : (UI.instV fr).Ginf), 1) :=
    fun v => oneP_eq_brg θ hθ fr v _ _ (Matrix.exp_conj _ _ (fr.unit v))
  have hYe : ∀ v, oneP θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Z v * (fr.P v)⁻¹) 1 =
      UI.brg fr ((Pi.mulSingle v (expUJ (hAZ v).2) : (UI.instV fr).Ginf), 1) :=
    fun v => oneP_eq_brg θ hθ fr v _ _ (Matrix.exp_conj _ _ (fr.unit v))
  have hu' : u = ((Finset.univ : Finset (InfinitePlace D.host.F)).toList.map fun v =>
      (Pi.mulSingle v (expUJ (hAZ v).1) : (UI.instV fr).Ginf) * (Pi.mulSingle v (expUJ (hAZ v).2) : (UI.instV fr).Ginf)).prod := by
    have e : ∀ v : InfinitePlace D.host.F, ((Pi.mulSingle v (expUJ (hAZ v).1) : (UI.instV fr).Ginf) *
        (Pi.mulSingle v (expUJ (hAZ v).2) : (UI.instV fr).Ginf)) = (Pi.mulSingle v (expUJ (hAZ v).1 * expUJ (hAZ v).2) : (UI.instV fr).Ginf) :=
      fun v => (Pi.mulSingle_mul _ _ _).symm
    refine Eq.trans ?_ (congrArg List.prod (List.map_congr_left fun v _ => e v)).symm
    funext w
    refine Eq.trans ?_ (list_prod_mulSingle (M := fun w : InfinitePlace (UI.instV fr).F => Formalism.REAL.UJ ((UI.instV fr).ε w))
      (fun v => expUJ (hAZ v).1 * expUJ (hAZ v).2) _ (Finset.nodup_toList _) w).symm
    refine Eq.trans ?_ (if_pos (Finset.mem_toList.2 (Finset.mem_univ _))).symm
    exact Subtype.ext (Units.ext (hu w))
  have hfac : UI.brg fr (u, 1) = ((Finset.univ : Finset (InfinitePlace D.host.F)).toList.map fun v =>
      oneP θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Av v * (fr.P v)⁻¹) 1 *
        oneP θ V ((Formalism.L2.Host.tauPl D).symm v) (fr.P v * Z v * (fr.P v)⁻¹) 1).prod := by
    have e1 : ((u, 1) : (UI.instV fr).GA) = MonoidHom.inl (UI.instV fr).Ginf (UI.instV fr).Gf u := rfl
    rw [e1, hu']
    refine (map_prod_pairs ((UI.brg fr : (UI.instV fr).GA →* GA D V).comp (MonoidHom.inl _ _)) _
      (fun v => (Pi.mulSingle v (expUJ (hAZ v).1) : (UI.instV fr).Ginf))
      (fun v => (Pi.mulSingle v (expUJ (hAZ v).2) : (UI.instV fr).Ginf))).trans ?_
    refine congrArg List.prod (List.map_congr_left fun v _ => ?_)
    rw [hXe v, hYe v]
    rfl
  rw [hfac]
  refine (lip_list θ A φ c hL (fun v => (Formalism.L2.Host.tauPl D).symm v) (fun v => fr.P v * Av v * (fr.P v)⁻¹)
    (fun v => fr.P v * Z v * (fr.P v)⁻¹) hX hY _ y).trans (le_of_eq ?_)
  rw [Finset.sum_map_toList]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  have hPv : fr.P v = (A.fr ((Formalism.L2.Host.tauPl D).symm v))⁻¹ := by
    have h := hP ((Formalism.L2.Host.tauPl D).symm v)
    rwa [Equiv.apply_symm_apply] at h
  simp only [hPv, conj_back _ _ (A.fr_unit _)]
  rfl

end GlobalTheory.RealMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocKerOfCoverKer
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open Matrix MeasureTheory GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec KMap maxCpt rep_mem_kFin)
open scoped TensorProduct InnerProductSpace Classical
open GlobalTheory.Chain.IoLift GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.IoLift.KerTransfer

theorem locKer_of_coverKer (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S')
    (τ : D.what₂.Tau) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂)
    (e : Ix p q ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m m' : ℤ) (aS aT : ℚ) (U : M.H τ → R₁.U.H)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] R₂.U.H) (κ : LPol W.rank V.rank ≃ₗ[ℂ] Pol p q r s)
    (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ)) (hm' : (m' : ℚ) = 2 * aS)
    (h₁ : Matches R₁ M τ (barMat e) m U) (h₂ : Matches R₂ M' τ (plainMat e') m' U')
    (hκ : IsPolyIso (M.ε τ) (M'.ε τ) e e' κ) (ha : IsKAct M' τ a') (hC : CoverKer p q R₂.HK) :
    LocKer M M' τ aS aT a' := by
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  have hmem : ∀ v, U'.symm (R₂.ι v) ∈ kFin M' τ := fun v =>
    (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩
  let j : R₂.HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ :=
    { toFun := fun v => ⟨U'.symm (R₂.ι v), hmem v⟩
      map_add' := fun v w => Subtype.ext (by simp)
      map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }
  have hj : ∀ v, U' (j v : M'.H τ) = R₂.ι v := fun v => U'.apply_symm_apply _
  have hsurj : Function.Surjective j := fun y => by
    obtain ⟨v, hv⟩ := (h₂.kfin y).1 y.2
    exact ⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩
  have key : ∀ (Z : Type) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z]
      (B : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] Z), IsLocPair M M' τ aS aT a' B →
      ∃ B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z, IsCoverPair R₂.HK B' ∧
        ∀ P v, B' (κ P) v = B P (j v) := by
    intro Z _ _ B hB
    let B' : Pol p q r s →ₗ[ℂ] R₂.HK.V →ₛₗ[starRingEnd ℂ] Z :=
      { toFun := fun P => (B (κ.symm P)).comp j
        map_add' := fun P Q => by ext v; simp
        map_smul' := fun c P => by ext v; simp }
    have hB' : ∀ P v, B' (κ P) v = B P (j v) := fun P v => by simp [B']
    refine ⟨B', ⟨fun X hX P P' y y' => ?_, fun Y hY P y => ?_⟩, hB'⟩
    · obtain ⟨P, rfl⟩ := κ.surjective P
      obtain ⟨P', rfl⟩ := κ.surjective P'
      have hX' : toFrame M τ (barMat e X) ∈ lieAt V τ := h₁.lie ▸ ⟨X, hX, rfl⟩
      have h3 : (barMat e X).map (starRingEnd ℂ) = Matrix.reindex e e X := by ext a b; simp [barMat]
      have h4 : (barMat e X).trace = -X.trace := by
        rw [barMat, trace_reindex', ← trace_conj hX]
        simp [Matrix.trace]
      have h := hB.skew _ hX' P P' (j y) (j y')
      simp only [sOp, fr_toFrame, trace_toFrame, h3, h4, LinearMap.add_apply, LinearMap.smul_apply,
        Module.End.one_apply, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right, map_neg, map_mul, map_ratCast, trace_conj hX] at h
      rw [← hκ.1, ← hκ.1, hB', hB', hB', hB']
      linear_combination h
    · obtain ⟨P, rfl⟩ := κ.surjective P
      have hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ := h₂.lie ▸ ⟨Y, hY, rfl⟩
      have h4 : (plainMat e' Y).trace = Y.trace := trace_reindex' e' Y
      have h5 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j (R₂.HK.act Y y) - ((aS : ℂ) * Y.trace) • j y := by
        have h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) =
            j (R₂.HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y) := by
          refine Subtype.ext (U'.injective ?_)
          rw [hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]
        rw [h6, map_add, LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC',
          sub_eq_add_neg, ← neg_smul]
        congr 2
        ring
      have h := hB.inv _ hY' P (j y)
      rw [h5, tOp, fr_toFrame, trace_toFrame, h4] at h
      rw [← hκ.2, hB', hB', ← h]
      simp [plainMat]
  intro Z₁ Z₂ _ _ _ _ B₁ B₂ hB₁ hB₂ hne n a b hs
  obtain ⟨C₁, hC₁, e₁⟩ := key Z₁ B₁ hB₁
  obtain ⟨C₂, hC₂, e₂⟩ := key Z₂ B₂ hB₂
  choose g hg using hsurj
  have hne' : C₁ ≠ 0 := fun h0 => hne (LinearMap.ext fun P => LinearMap.ext fun y => by
    rw [← hg y, ← e₁, h0]; rfl)
  have h := hC Z₁ Z₂ C₁ C₂ hC₁ hC₂ hne' n (fun i => κ (a i)) (fun i => g (b i)) (by simpa [e₁, hg] using hs)
  simpa [e₂, hg] using h

end GlobalTheory.Chain.IoLift.KerTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalStableOrbitalIntegralsWellDefined
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section
namespace GlobalTheory.TrPhiOK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r n : ℕ}
  {P : PPol σ r} {J : Matrix (Fin n) (Fin n) E}

theorem phiOK_of (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (k : Type) [Field k] [Algebra F k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] [LocallyCompactSpace (HA k σ J)] [SecondCountableTopology (HA k σ J)]
    [T2Space (HA k σ J)] (hfin : Finite (Cls P k))
    (hU : ∀ μ : Measure (HA k σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (hpr : ∀ g : HA k σ J, IsRegSS (matHom k σ J g).1 → IsProperOrbit (cent g) g)
    (μ : Measure (HA k σ J)) (dt : Measure (Tor P k)) (f : HA k σ J → ℂ) [hμ : μ.IsHaarMeasure]
    [hdt : dt.IsHaarMeasure] (hf : Continuous f) (hc : HasCompactSupport f) : PhiOK (J := J) μ dt f := by
  refine ⟨Set.toFinite _, fun x φ h => ?_⟩
  haveI := hU μ hμ
  set q : XSet P k J := ⟨QuotientGroup.mk x, x, φ, rfl, h⟩ with hq
  obtain ⟨hx0, h0⟩ := q.2.choose_spec.choose_spec
  set x0 := q.2.choose
  set φ0 := q.2.choose_spec.choose
  change HasOrbInt μ (gam h) (centMeas h dt) f (orbInt μ (gam h0) (centMeas h0 dt) f)

  have halg0 := GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hσ r n P J hJ k x0 φ0 h0
  obtain ⟨e0, he0, hm0⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hσ r n P J hJ k x0 φ0 h0
  obtain ⟨e, he, hm⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hσ r n P J hJ k x φ h
  haveI : (centMeas h0 dt).IsHaarMeasure := by rw [hm0]; exact e0.isHaarMeasure_map dt
  haveI : (centMeas h0 dt).IsMulRightInvariant :=
    isMulRightInvariant_cent (isMulCommutative_cent_HA halg0.2.1) _
  have H0 : HasOrbInt μ (gam h0) (centMeas h0 dt) f (orbInt μ (gam h0) (centMeas h0 dt) f) :=
    (hpr _ halg0.2.1).hasOrbInt hf hc

  obtain ⟨g, hg⟩ := (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hσ r n P J hJ k x0 φ0 h0 x φ h).1 (by rw [hx0])
  have hgam : g * gam h0 * g⁻¹ = gam h := (hg _).symm
  have hmeas : centMeas h dt = (centMeas h0 dt).map (centEquiv (conjEquiv g) (gam h0) hgam) := by
    rw [hm, hm0, Measure.map_map (map_continuous _).measurable (map_continuous _).measurable]
    congr 1
    funext t
    apply Subtype.ext
    change (e t).1 = g * (e0 t).1 * g⁻¹
    rw [he, he0, hg]
  rw [hmeas]
  exact ((hasOrbInt_conj (dh := μ) (dt := centMeas h0 dt) g hgam f _).1).2 H0

end GlobalTheory.TrPhiOK

open GlobalTheory.TrPhiOK in

theorem GlobalTheory.TrPhiOK.phiOK_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → (∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (GLoc σ J v)) (dt : Measure (Tor P (Fv F v))) (f : GLoc σ J v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f) ∧ ∀ (w : InfinitePlace F) (μ : Measure (GArch σ J w)) (dt : Measure (Tor P w.Completion)) (f : GArch σ J w → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f := by
  intro F E _ _ _ _ _ σ hσ r n P J hJ
  have hfin := GlobalTheory.T.finite_unitaryTorusNormClasses_at_all_places F E σ hσ r P
  refine ⟨fun v μ dt f hμ hdt hf hc => ?_, fun w μ dt f hμ hdt hf hc => ?_⟩
  · have hU := (GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion F E σ hσ n J hJ v).1
    exact phiOK_of hσ hJ (Fv F v) (hfin.1 v) hU.2.2.2.2.2.2 (fun g hg => isProperOrbit_GLoc hσ hJ hg) μ dt f hf hc
  · haveI : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    have hU := (GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_artinian (σ := σ) w.Completion hσ hJ).1
    exact phiOK_of hσ hJ w.Completion (hfin.2 w) hU.2.2.2.2.2.2 (fun g hg => isProperOrbit_GArch hσ hJ hg) μ dt f hf hc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoeffIsotropicTranslatesEqFourierCoeffs
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistCoefUnfold

theorem pcoef : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ κ : ℝ, (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ (y : Mx D W.rank r) (a : Matrix (Fin W.rank) (Fin r) D.host.E), (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) = ∫ t in 𝓨, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * (κ • (∫ y' in 𝓨, ∫ x in 𝓕', (heisO ψ V W (isoPart V W C y) F) (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) * star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ)) ∂μ := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hμ μV 𝓕V hμV h𝓕V μ' 𝓕' hμ' h𝓕' κ hκ F G hF hG y a
  have hth := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W
  have horth := GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hs C' h1 h2 h3
  have hPt : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C y) F) := hth.1 _ F hF
  have hγrat : isoPart V W C (a.map (incA D)) ∈ ratL W V := by
    rw [← GlobalTheory.TwistEquiRat.ratW_eq_isoPart]; exact ⟨_, rfl⟩
  have hfirst : heisO ψ V W (isoPart V W C (y + a.map (incA D))) F =
      heisO ψ V W (isoPart V W C (a.map (incA D))) (heisO ψ V W (isoPart V W C y) F) := by
    rw [hth.2.1, GlobalTheory.TwistEquiRat.symplOH_isoPart V W C hs.frame, AddChar.map_zero_eq_one, one_smul,
      GlobalTheory.TwistEquiRat.isoPart_add, add_comm]
  have hpt : ∀ w, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) =
      ψ (symplO V W w (isoPart V W C (a.map (incA D)))) * (heisO ψ V W (isoPart V W C y) F w * star (G w)) := by
    intro w
    rw [hfirst, GlobalTheory.ThetaSchur.heisO_rat hPt hγrat]
    ring
  have hsym : ∀ t y' x, symplO V W (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)
      (isoPart V W C (a.map (incA D))) = symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))) := by
    intro t y' x
    rw [GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left, horth.1 y' _,
      GlobalTheory.PlaceModel.symplO_skew V W (isoPart V W C (a.map (incA D))) (midPart V V' W B x), horth.2.1 _ x]
    simp
  have hHt : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C (y + a.map (incA D))) F) := hth.1 _ F hF
  have hHc : Continuous fun w => heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) :=
    hHt.cont.mul hG.cont.star
  have hHb : ∃ b : ℝ, ∀ w, ‖heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w)‖ ≤ b := by
    obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
    obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn hHc.continuousOn
    refine ⟨b, fun w => ?_⟩
    obtain ⟨g, hg, h⟩ := hKc w
    rw [← GlobalTheory.ThetaSchur.prod_periodic hψ hHt hG hg w]
    exact hb _ h
  have key := hκ _ hHc hHb (fun g hg w => GlobalTheory.ThetaSchur.prod_periodic hψ hHt hG hg w)
  rw [key]
  simp_rw [hpt, hsym, integral_const_mul]
  rw [← integral_smul]
  congr 1
  funext t
  rw [mul_smul_comm]

end GlobalTheory.TwistCoefUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_smoothVectors_discreteSeriesModel_iff : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ),
    w ∈ M.sm τ ↔ SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w := by
  first | exact @GlobalTheory.SmVecModel.mem_sm_iff | exact GlobalTheory.SmVecModel.mem_sm_iff | (intros; apply GlobalTheory.SmVecModel.mem_sm_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoInvariantPairingSmallerFockDiscreteSeries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.NoLowPairing

theorem no_pairing_of_noLow : ∀ (X : ProvA) (p q r s : ℕ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds r s lam').HK → NoLow X p q lam' → ∀ i : ℕ, 1 ≤ i → i ≤ p → i ≤ q → ∀ b : Formalism.BasicNotions.TH.Pol (p - i) (q - i) r s →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] ℂ, (∀ Z ∈ upq r s, ∀ P y, b (fockAct2 (p - i) (q - i) r s Z P) y + b P ((X.ds r s lam').HK.act Z y) = 0) → b = 0 := by
  intro X p q r s lam' hadm hlow i hi hip hiq b hb
  exact GlobalTheory.NoInvPairing.eq_zero_of_noIntw' (X.ds r s lam') (X.fock (p - i) (q - i) r s) hadm
    (fun M f hf => hlow i hi hip hiq M f hf) b hb

end GlobalTheory.NoLowPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OfMulTrivialAtPlacesSubsetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.of_mul_trivialAtPlaces_subset : ∀ {D : D7} {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (P Q : GlobalTheory.FinPl.Pl D → Prop) (g₁ g₂ : GA D W), (∀ v, Q v → P v) → g₁ ∈ grpAt W Q → g₂ ∈ grpOff W Q → g₁ * g₂ = g₂ * g₁ → Cond dW p x y ψ P (g₁ * g₂) → Cond dW p x y ψ Q g₁ := by
  first | exact @GlobalTheory.AscFin.Cond.of_mul_grpOff | exact GlobalTheory.AscFin.Cond.of_mul_grpOff | (intros; apply GlobalTheory.AscFin.Cond.of_mul_grpOff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFrameStabiliserNormalisesUnipotentRadicaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFrameStabiliser_normalises_unipotentRadical : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L → (∀ γ ∈ GQ W, ∀ γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W γ = γ₀.map (incA D) → γ₀ * L = L → ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) ∧ (∀ n ∈ NI W L, ∀ n₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W n = n₀.map (incA D) → n₀ * L = L) := by
  first | exact @GlobalTheory.FrameStab.stab | exact GlobalTheory.FrameStab.stab | (intros; apply GlobalTheory.FrameStab.stab <;> assumption)
end

