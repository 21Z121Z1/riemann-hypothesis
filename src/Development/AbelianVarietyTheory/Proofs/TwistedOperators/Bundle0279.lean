import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0257
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0336
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVecModel

section Conj

variable {n : ℕ} {J P G : Matrix (Fin n) (Fin n) ℂ}

theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

theorem lie_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * G + G * X = 0) :
    (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹)
      = (P * X * P⁻¹)ᴴ * J * (P * P⁻¹) + (P * P⁻¹)ᴴ * J * (P * X * P⁻¹) := by rw [h1]; simp
    _ = (P⁻¹)ᴴ * (Xᴴ * G + G * X) * P⁻¹ := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX]; simp

theorem lie_conj_inv (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * J + J * X = 0) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * (Xᴴ * ((P * P⁻¹)ᴴ * J) + J * (P * P⁻¹) * X) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]; simp

theorem exp_smul_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P * X * P⁻¹)) = P * NormedSpace.exp (t • X) * P⁻¹ := by
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

theorem prod_conj (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P * g * P⁻¹).prod = P * l.prod * P⁻¹ := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h1]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P * a * P⁻¹ * (P * l.prod * P⁻¹) = P * a * (P⁻¹ * P) * l.prod * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)]
        simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smoothVec_of_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * J + J * X = 0} σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => lie_conj_inv hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

theorem smoothVec_to_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * J + J * X = 0} σ w) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w := by
  intro k Xs hXs
  have h := hw k (fun i => P * Xs i * P⁻¹) fun i => lie_conj hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, (List.ofFn fun i => NormedSpace.exp (t i • (P * Xs i * P⁻¹))).prod =
      P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹ := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P * Xs i * P⁻¹))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P * g * P⁻¹ := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj hP _ _
    rw [this, prod_conj hP]
  simpa only [e] using h

end Conj

theorem mem_sm_iff : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ),
    w ∈ M.sm τ ↔ SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w := by
  intro D V S M τ w
  rw [GlobalTheory.SmVec.sm_eq M τ, GlobalTheory.SmVec.mem_smSub]
  constructor
  · intro h
    exact smoothVec_of_conj (M.fr_unit τ) (M.fr_gram τ) h
  · intro h
    exact smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) h

end GlobalTheory.SmVecModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OfMulTrivialAtPlacesSubset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.CondCut

variable {D : D7}

theorem idOff_sub {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, Q v → P v) {a : AE D} (ha : a ∈ idOff D P) : a ∈ idOff D Q := by
  unfold GlobalTheory.FinPl.idOff at ha ⊢
  rw [Submodule.mem_iInf] at ha ⊢
  exact fun w => ha ⟨w.1, h w.1 w.2⟩

theorem idAt_sup {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, Q v → P v) {a : AE D} (ha : a ∈ idAt D Q) : a ∈ idAt D P := by
  unfold GlobalTheory.FinPl.idAt at ha ⊢
  obtain ⟨h0, hw⟩ := Ideal.mem_inf.1 ha
  refine Ideal.mem_inf.2 ⟨h0, ?_⟩
  rw [Submodule.mem_iInf] at hw ⊢
  exact fun w => hw ⟨w.1, fun hq => w.2 (h w.1 hq)⟩

theorem mt_mul_of_grpOff {W : HSp D} {Q : GlobalTheory.FinPl.Pl D → Prop} {b : GA D W} (hb : b ∈ grpOff W Q) {k : ℕ}
    (M : Matrix (Fin W.rank) (Fin k) (AE D)) (hM : ∀ i j, M i j ∈ idAt D Q) : mt W b ⬝ M = M := by
  have hb' := (GlobalTheory.FinPlLoc.mem_congGrp _ b).1 hb
  have key : (mt W b - 1) ⬝ M = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have h1 := (GlobalTheory.FinPlLoc.mem_idOff_iff Q _).1 (hb' i l)
    have h2 := (GlobalTheory.FinPlLoc.mem_idAt_iff Q _).1 (hM l j)
    rw [Matrix.sub_apply, ← h2]
    calc (mt W b i l - (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) i l) * (GlobalTheory.FinPlLoc.idem D Q * M l j)
        = (GlobalTheory.FinPlLoc.idem D Q * (mt W b i l - (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) i l)) * M l j := by ring
      _ = 0 := by rw [h1, zero_mul]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at key
  exact key

theorem mul_mem_idAt {Q : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (AE D))
    (B : Matrix (Fin n) (Fin k) (AE D)) (hB : ∀ i j, B i j ∈ idAt D Q) (i : Fin m) (j : Fin k) : (A ⬝ B) i j ∈ idAt D Q := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hB l j)

end GlobalTheory.AscFin.CondCut

open GlobalTheory.AscFin.CondCut in

theorem GlobalTheory.AscFin.Cond.of_mul_grpOff : ∀ {D : D7} {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (P Q : GlobalTheory.FinPl.Pl D → Prop) (g₁ g₂ : GA D W), (∀ v, Q v → P v) → g₁ ∈ grpAt W Q → g₂ ∈ grpOff W Q → g₁ * g₂ = g₂ * g₁ → Cond dW p x y ψ P (g₁ * g₂) → Cond dW p x y ψ Q g₁ := by
  intro D V₀ W W₀ ρ σ dW p x y ψ P Q g₁ g₂ hQP _hg₁ hg₂ _hcomm H
  have hg₂i : g₂⁻¹ ∈ grpOff W Q := inv_mem hg₂
  have emt : ∀ {k : ℕ} (M : Matrix (Fin W.rank) (Fin k) (AE D)),
      mt W (g₁ * g₂)⁻¹ ⬝ M = mt W g₂⁻¹ ⬝ (mt W g₁⁻¹ ⬝ M) := by
    intro k M
    rw [_root_.mul_inv_rev]
    exact Matrix.mul_assoc _ _ _
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, a, ha, hoff⟩ := H.pt
    refine ⟨u, a, ha, fun i j => ?_⟩
    have h1 := idOff_sub hQP (hoff i j)
    have h2 : ((mt W g₂⁻¹ - 1) ⬝ (mt W g₁⁻¹ ⬝ (x ⬝ u.1.1))) i j ∈ idOff D Q := by
      rw [Matrix.mul_apply]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (by
        rw [Matrix.sub_apply]; exact (GlobalTheory.FinPlLoc.mem_congGrp _ _).1 hg₂i i l)
    have e : mt W g₁⁻¹ ⬝ (x ⬝ u.1.1) - x - a =
        (mt W (g₁ * g₂)⁻¹ ⬝ (x ⬝ u.1.1) - x - a) - (mt W g₂⁻¹ - 1) ⬝ (mt W g₁⁻¹ ⬝ (x ⬝ u.1.1)) := by
      rw [emt, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, Matrix.sub_apply]
    exact sub_mem h1 h2
  · intro N hN hlow hA
    refine H.shift N (fun i j => idAt_sup hQP (hN i j)) hlow ?_
    rw [emt, mt_mul_of_grpOff hg₂i _ (mul_mem_idAt _ _ (mul_mem_idAt _ _ hN))]
    exact hA
  · intro ξ hξ ξ' hξQ he
    refine H.iso ξ hξ ξ' (fun i j => idAt_sup hQP (hξQ i j)) ?_
    have hinc : ∀ i j, (dW.incX V₀ ξ) i j ∈ idAt D Q := mul_mem_idAt _ _ hξQ
    show mt W g₁ ⬝ mt W g₂ ⬝ dW.incX V₀ ξ = _
    rw [Matrix.mul_assoc, mt_mul_of_grpOff hg₂ _ hinc]
    exact he

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned
  Formalism.L2.SG.EvalTOntoRep MeasureTheory
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowMult

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def contSub : Submodule ℂ (L2X X) where
  carrier := {f | ∃ φ, IsContRep X f φ}
  add_mem' := fun ⟨φ, hφ⟩ ⟨ψ, hψ⟩ => ⟨φ + ψ, contRep_add X hφ hψ⟩
  zero_mem' := ⟨0, contRep_zero X⟩
  smul_mem' := fun a _ ⟨φ, hφ⟩ => ⟨a • φ, contRep_smul X a hφ⟩

def repOn : contSub X →ₗ[ℂ] (X.B.I.GA → ℂ) where
  toFun f := f.2.choose
  map_add' f g := contRep_unique X (f + g).2.choose_spec (contRep_add X f.2.choose_spec g.2.choose_spec)
  map_smul' a f := contRep_unique X (a • f).2.choose_spec (contRep_smul X a f.2.choose_spec)

def contRepL : L2X X →ₗ[ℂ] (X.B.I.GA → ℂ) := (LinearMap.exists_extend (repOn X)).choose

theorem contRepL_spec {f : L2X X} {φ : X.B.I.GA → ℂ} (hf : IsContRep X f φ) : contRepL X f = φ := by
  have e := LinearMap.congr_fun (LinearMap.exists_extend (repOn X)).choose_spec ⟨f, φ, hf⟩
  have e' : contRepL X f = repOn X ⟨f, φ, hf⟩ := e
  rw [e']
  exact contRep_unique X (Exists.choose_spec (p := fun φ => IsContRep X f φ) _) hf

theorem eq_of_inner_tens {p q : X.B.Hs} (h : ∀ y, ⟪p, X.B.tens y⟫_ℂ = ⟪q, X.B.tens y⟫_ℂ) : p = q := by
  let f : X.B.Hs →L[ℂ] ℂ := innerSL ℂ (p - q)
  have hsp : (Submodule.span ℂ (Set.range X.B.tens) : Set X.B.Hs) ⊆ {z | f z = 0} := by
    refine (Submodule.span_le (p := LinearMap.ker (f : X.B.Hs →ₗ[ℂ] ℂ))).2 ?_
    rintro _ ⟨y, rfl⟩
    show ⟪p - q, X.B.tens y⟫_ℂ = 0
    rw [inner_sub_left, h y, sub_self]
  have hcl : closure (Submodule.span ℂ (Set.range X.B.tens) : Set X.B.Hs) ⊆ {z | f z = 0} :=
    closure_minimal hsp (isClosed_eq f.continuous continuous_const)
  rw [X.B.tens_spec.2.2.closure_eq] at hcl
  have h0 : f (p - q) = 0 := hcl (Set.mem_univ _)
  have : ⟪p - q, p - q⟫_ℂ = 0 := h0
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

theorem prod_update {ι : Type} [Fintype ι] [DecidableEq ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)]
    [∀ i, InnerProductSpace ℂ (H i)] (x y : ∀ i, H i) (v : ι) (z : H v) :
    ∏ w, ⟪Function.update x v z w, y w⟫_ℂ = ⟪z, y v⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪x w, y w⟫_ℂ := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]

theorem tens_update_add [DecidableEq (NumberField.InfinitePlace X.B.I.F)] (x : ∀ v, X.B.H v)
    (v : NumberField.InfinitePlace X.B.I.F) (a b : X.B.H v) :
    X.B.tens (Function.update x v (a + b)) =
      X.B.tens (Function.update x v a) + X.B.tens (Function.update x v b) := by
  refine eq_of_inner_tens X fun y => ?_
  rw [inner_add_left, X.B.tens_spec.1, X.B.tens_spec.1, X.B.tens_spec.1, prod_update, prod_update, prod_update,
    inner_add_left, add_mul]

theorem tens_update_smul [DecidableEq (NumberField.InfinitePlace X.B.I.F)] (x : ∀ v, X.B.H v)
    (v : NumberField.InfinitePlace X.B.I.F) (a : ℂ) (b : X.B.H v) :
    X.B.tens (Function.update x v (a • b)) = a • X.B.tens (Function.update x v b) := by
  refine eq_of_inner_tens X fun y => ?_
  rw [inner_smul_left, X.B.tens_spec.1, X.B.tens_spec.1, prod_update, prod_update, inner_smul_left, mul_assoc]

variable {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S)

def vecC (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) : ∀ v, X.B.H v :=
  Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (u τ : M.H τ))

theorem piCongrLeft_update {α β : Type} [DecidableEq α] [DecidableEq β] (P : β → Type) (e : α ≃ β)
    (f : ∀ a, P (e a)) (a : α) (x : P (e a)) :
    Equiv.piCongrLeft P e (Function.update f a x) = Function.update (Equiv.piCongrLeft P e f) (e a) x := by
  apply (Equiv.piCongrLeft P e).symm.injective
  rw [Equiv.symm_apply_apply]
  funext a'
  rw [Equiv.piCongrLeft_symm_apply]
  by_cases ha : a' = a
  · subst ha
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne ha, Function.update_of_ne (e.injective.ne ha), Equiv.piCongrLeft_apply_apply]

theorem vecC_update [DecidableEq D.what₂.Tau] [DecidableEq (NumberField.InfinitePlace X.B.I.F)]
    (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) (τ : D.what₂.Tau) (w : M.sm τ) :
    vecC X M c (Function.update u τ w) = Function.update (vecC X M c u) (X.pl.symm τ) (c τ (w : M.H τ)) := by
  unfold vecC
  rw [← piCongrLeft_update]
  congr 1
  funext τ'
  exact Function.apply_update (fun i (s : M.sm i) => c i (s : M.H i)) u τ w τ'

theorem vecC_eq (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (u : M.Vec) (g : ∀ v, X.B.H v)
    (hg : ∀ τ, c τ (u τ : M.H τ) = g (X.pl.symm τ)) : vecC X M c u = g := by
  unfold vecC
  have : (fun τ => c τ (u τ : M.H τ)) = (Equiv.piCongrLeft X.B.H X.pl.symm).symm g := by
    funext τ
    rw [Equiv.piCongrLeft_symm_apply, hg τ]
  rw [this, Equiv.apply_symm_apply]

def conjMap (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (A : X.B.Hs →L[ℂ] L2X X)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) : MMap M where
  toFun u := fun y => star (contRepL X (A (X.B.tens (vecC X M c u))) (iotaX X h (y * t⁻¹)))
  map_update_add' u τ a b := by
    classical
    funext y
    simp only [vecC_update, Submodule.coe_add, map_add, tens_update_add, Pi.add_apply, star_add]
  map_update_smul' u τ a b := by
    classical
    funext y
    simp only [vecC_update, Submodule.coe_smul, LinearIsometryEquiv.map_smulₛₗ, tens_update_smul, map_smul,
      Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply, star_star]

theorem conjMap_apply (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (A : X.B.Hs →L[ℂ] L2X X)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)) (u : M.Vec) (y : GA D (D.sp.Y 0)) :
    conjMap X M c A h t u y = star (contRepL X (A (X.B.tens (vecC X M c u))) (iotaX X h (y * t⁻¹))) := rfl

end GlobalTheory.ConjRowMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceModelOntoLocal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SymmetricBilinearHalf

variable {D : D7}

theorem sb_zero {m n : ℕ} (e : AE D) (Λ : AddSubgroup (Mx D m n)) : IsSBHalf e Λ 0 :=
  ⟨fun _ h => absurd rfl h, 1, one_pos, fun _ _ _ _ => rfl, fun _ h => absurd rfl h⟩

theorem sb_smul {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ : Mx D m n → ℂ} (c : ℂ)
    (h : IsSBHalf e Λ Φ) : IsSBHalf e Λ (c • Φ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  have ne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by rw [Pi.smul_apply, h0, smul_zero])
  exact ⟨fun t ht => h1 t (ne t ht), k, hk, fun u hu hh t => by rw [Pi.smul_apply, Pi.smul_apply, h2 u hu hh t],
    fun t ht => h3 t (ne t ht)⟩

theorem half_nsmul {m n : ℕ} {e : AE D} {u : Mx D m n} (k : ℕ) (h : IsHalf e u) : IsHalf e (k • u) := by
  rw [GlobalTheory.SplitScalar.isHalf_iff] at h ⊢
  rw [smul_comm, h]

theorem sb_add {m n : ℕ} {e : AE D} {Λ : AddSubgroup (Mx D m n)} {Φ Ψ : Mx D m n → ℂ}
    (h : IsSBHalf e Λ Φ) (h' : IsSBHalf e Λ Ψ) : IsSBHalf e Λ (Φ + Ψ) := by
  obtain ⟨h1, k, hk, h2, h3⟩ := h
  obtain ⟨h1', k', hk', h2', h3'⟩ := h'
  have ne : ∀ t, (Φ + Ψ) t ≠ 0 → Φ t ≠ 0 ∨ Ψ t ≠ 0 := fun t ht => by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    exact ht (by rw [Pi.add_apply, hc.1, hc.2, add_zero])
  refine ⟨fun t ht => (ne t ht).elim (h1 t) (h1' t), k * k', Nat.mul_pos hk hk', fun u hu hh t => ?_,
    fun t ht => ?_⟩
  · have e1 : Φ (t + (k * k') • u) = Φ t := by
      rw [mul_smul]; exact h2 _ (Λ.nsmul_mem hu k') (half_nsmul k' hh) t
    have e2 : Ψ (t + (k * k') • u) = Ψ t := by
      rw [mul_comm, mul_smul]; exact h2' _ (Λ.nsmul_mem hu k) (half_nsmul k hh) t
    rw [Pi.add_apply, Pi.add_apply, e1, e2]
  · rcases ne t ht with h | h
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem (h3 t h) k'
    · rw [mul_smul]; exact Λ.nsmul_mem (h3' t h) k

theorem wAt_of_half {m n : ℕ} {p : Place D} {a c : AE D} (hac : a * c = 0) (hs : a + c = idem D p)
    {x : Mx D m n} (hx : IsHalf a x) : wAt p x = x := by
  funext i j
  show idem D p * x i j = x i j
  have := hx i j
  rw [← hs]
  linear_combination (1 - c) * this + (x i j) * hac

theorem placeModel_onto_local : ∀ (D : Formalism.BasicNotions.D7) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF ↥(Formalism.BasicNotions.D7.host D).F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (S T : Formalism.BasicNotions.TH.HSp D) (sS : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D) → Matrix (Fin (Formalism.BasicNotions.HSpace.rank S)) (Fin (Formalism.BasicNotions.HSpace.rank S)) ℂ) (sT : Formalism.BasicNotions.Rows.Data.Tau (Formalism.BasicNotions.D7.what₂ D) → Matrix (Fin (Formalism.BasicNotions.HSpace.rank T)) (Fin (Formalism.BasicNotions.HSpace.rank T)) ℂ) (ΛS : Submodule (NumberField.RingOfIntegers (Formalism.BasicNotions.D7.host D).E) (Fin (Formalism.BasicNotions.HSpace.rank S) → (Formalism.BasicNotions.D7.host D).E)) (ΛT : Submodule (NumberField.RingOfIntegers (Formalism.BasicNotions.D7.host D).E) (Fin (Formalism.BasicNotions.HSpace.rank T) → (Formalism.BasicNotions.D7.host D).E)) (f₀ : Formalism.IndefR.Datum.WO S T → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsBase ψ θ S T sS sT ΛS ΛT f₀ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.FinPl D) (a : Formalism.L2.Theta.AE D), Formalism.L2.Theta.IsSplitIdem D a → a + (Formalism.L2.Theta.cA D) a = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.idem D (Sum.inl v) → (∃ (Tm : (Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ) →ₗ[ℂ] Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsPlaceModel ψ (Formalism.IndefR.Datum.symplO S T) (Formalism.IndefR.Datum.heisO ψ S T) a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) (1 : ℂ) f₀ Tm) ∧ ∀ (Tm : (Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ) →ₗ[ℂ] Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsPlaceModel ψ (Formalism.IndefR.Datum.symplO S T) (Formalism.IndefR.Datum.heisO ψ S T) a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) (1 : ℂ) f₀ Tm → (∀ (Φ : Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsSBHalf a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) Φ → GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsLocal ψ θ S T sS sT ΛS ΛT (Sum.inl v) (Tm Φ)) ∧ ∀ (x : Formalism.IndefR.Datum.WO S T → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsLocal ψ θ S T sS sT ΛS ΛT (Sum.inl v) x → ∃ (Φ : Formalism.IndefR.Datum.Mx D (Formalism.BasicNotions.HSpace.rank T) (Formalism.BasicNotions.HSpace.rank S) → ℂ), Formalism.IndefR.Datum.IsSBHalf a (Formalism.IndefR.Datum.latO S T ↑ΛS ↑ΛT fun (x : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(Formalism.BasicNotions.D7.host D).F)) ↦ True) Φ ∧ Tm Φ = x := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ hb v a ha hs
  have h1 : a * a = a := ha.1
  have h2 : a * cA D a = 0 := ha.2.1
  have c1 : cA D a * cA D a = cA D a := by rw [← map_mul, h1]
  have hψ := base_std hb
  have hθ := base_inf hb
  have hS := hb.2.2.1
  have hT := hb.2.2.2.1
  obtain ⟨hgen, hspan⟩ := GlobalTheory.T.schwartzBruhatHalf_span_modulated_translates D ψ S T ΛS ΛT hψ hS hT a h1 h2 (GlobalTheory.PlaceModelSum.infPart_split ha)
  have st := fun f (hf : IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) f) =>
    (GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ f hf.1).2 (.inl v) hf
  have l0 := base_isLocal hb (.inl v)
  have lz : IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) 0 := by
    have := (st f₀ l0).2.1 (-1) f₀ l0
    rwa [neg_one_smul, neg_add_cancel] at this
  refine ⟨?_, fun Tm hTm => ⟨fun Φ hΦ => ?_, fun x hx => ?_⟩⟩
  · have ho : GlobalTheory.PlaceModelSum.IsOrthSum a :=
      ⟨Unit, {()}, fun _ => a, fun _ _ => ha, fun _ _ _ _ h => absurd rfl h, by rw [Finset.sum_singleton]⟩
    exact ho.exists_model hψ hS hT h2 hb.2.2.2.2.2.lat
  · refine Submodule.span_induction (p := fun Φ _ => IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) (Tm Φ))
      ?_ ?_ ?_ ?_ (hspan Φ hΦ)
    · rintro _ ⟨x, y, hx, hy, rfl⟩
      rw [(hgen x y hx hy).2 f₀ Tm hTm]
      have e1 := (st f₀ l0).1 x
      rw [wAt_of_half h2 hs hx] at e1
      have e2 := (st _ e1).1 y
      rwa [wAt_of_half ((mul_comm _ _).trans h2) ((add_comm _ _).trans hs) hy] at e2
    · rw [map_zero]; exact lz
    · intro x y _ _ hx hy
      have := (st _ hx).2.1 1 _ hy
      rw [one_smul] at this
      rw [map_add]; exact this
    · intro c x _ hx
      have := (st _ hx).2.1 c _ lz
      rw [add_zero] at this
      rw [map_smul]; exact this
  · refine Submodule.span_induction
      (p := fun x _ => ∃ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ ∧ Tm Φ = x)
      ?_ ?_ ?_ ?_ (GlobalTheory.T.localFactor_mem_span_localHeisenbergTranslates D ψ θ S T sS sT ΛS ΛT f₀ hb v x hx)
    · rintro _ ⟨w, rfl⟩
      have hx : IsHalf a (a • w) := by rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, h1]
      have hy : IsHalf (cA D a) (cA D a • w) := by rw [GlobalTheory.SplitScalar.isHalf_iff, smul_smul, c1]
      obtain ⟨g1, g2⟩ := hgen _ _ hx hy
      refine ⟨_, sb_smul (ψ (-symplOH S T (cA D a • w) (a • w))) g1, ?_⟩
      rw [map_smul, g2 f₀ Tm hTm, GlobalTheory.SplitScalar.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel,
        AddChar.map_zero_eq_one, one_smul, ← add_smul, add_comm, hs]
      rfl
    · exact ⟨0, sb_zero _ _, map_zero _⟩
    · rintro _ _ _ _ ⟨Φ, hΦ, rfl⟩ ⟨Ψ, hΨ, rfl⟩
      exact ⟨Φ + Ψ, sb_add hΦ hΨ, map_add _ _ _⟩
    · rintro c _ _ ⟨Φ, hΦ, rfl⟩
      exact ⟨c • Φ, sb_smul c hΦ, map_smul _ _ _⟩

end GlobalTheory.SymmetricBilinearHalf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceDeterminantPowerMulNeZeroExpStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceDeterminantPower_mul_ne_zero_exp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (m : D.what₂.Tau → ℤ), (∀ a b, detPow θ V m (a * b) = detPow θ V m a * detPow θ V m b) ∧ (∀ a, detPow θ V m a ≠ 0) ∧ (∀ Y : GlobalTheory.SmoothForms.LieN V, detPow θ V m (GlobalTheory.SmoothForms.expInf θ V Y) = cexp (GlobalTheory.AdSpan.ConjHol.trLin V m Y)) := by
  first | exact @GlobalTheory.AdSpan.ConjHol.detPow_mul_ne_zero_exp | exact GlobalTheory.AdSpan.ConjHol.detPow_mul_ne_zero_exp | (intros; apply GlobalTheory.AdSpan.ConjHol.detPow_mul_ne_zero_exp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointIdentificationLeastSizeLinearGrowthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPointIdentification_leastSize_linear_growth : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∀ g ∈ GinfC (D.sp.Y 0), (iotaX X h g).2 = 1) ∧ (1 ≤ (D.sp.Y 0).rank → ∀ x : X.B.I.GA, ∃ C : ℝ, 0 ≤ C ∧ ∀ g ∈ GinfC (D.sp.Y 0), (GlobalTheory.Count.tau1 X.B.I (x * iotaX X h g))⁻¹ ≤ C * normInf R.θ (D.sp.Y 0) g) := by
  first | exact @GlobalTheory.IotaNorm.iotaX_norm | exact GlobalTheory.IotaNorm.iotaX_norm | (intros; apply GlobalTheory.IotaNorm.iotaX_norm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesDiagonalUniformizerPowStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_integralMatrices_diagonal_uniformizer_pow : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (Q : ℕ), ϖ ≠ 0 → Valued.v ϖ ≤ 1 → (∀ e : ℕ, ((Formalism.UG.intL L).toAddSubgroup.map (AddMonoidHom.mulLeft (ϖ ^ e))).relIndex (Formalism.UG.intL L).toAddSubgroup = Q ^ e) → ∀ (r n : ℕ) (d : Fin r → ℤ), (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (Matrix.diagonal (fun i => ϖ ^ d i)))) = Q ^ (n * (∑ i, max (-d i) 0).toNat) := by
  first | exact @GlobalTheory.DiagIdx.relIndex_intMat_diag | exact GlobalTheory.DiagIdx.relIndex_intMat_diag | (intros; apply GlobalTheory.DiagIdx.relIndex_intMat_diag <;> assumption)
end

