import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceSourceLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SliceModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem ι_e (x : k) : p.e * p.ι x = p.ι x := by
  rw [← p.ι_π (p.ι x), p.π_ι]

theorem ι_mul (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have h1 : p.ι (x * y) = p.ι (p.π (p.ι x * p.ι y)) := by rw [map_mul p.π, p.π_ι, p.π_ι]
  rw [h1, p.ι_π, ← mul_assoc, ι_e]

theorem ι_mul_right (x : k) (z : AE D) : p.ι x * z = p.ι (x * p.π z) := by
  rw [ι_mul, p.ι_π, ← mul_assoc, mul_comm (p.ι x) p.e, ι_e]

theorem ι_mul_left (x : k) (z : AE D) : z * p.ι x = p.ι (p.π z * x) := by
  rw [mul_comm, ι_mul_right, mul_comm]

def prH : D.host.E →+* k := p.π.comp (incA D)

theorem prH_apply (a : D.host.E) : prH p a = p.pr a := rfl

theorem map_ι_mul_rat {l m o : Type} [Fintype m] (M : Matrix l m k) (N : Matrix m o D.host.E) :
    M.map p.ι * N.map (incA D) = (M * N.map (prH p)).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul_right]
  rfl

theorem rat_mul_map_ι {l m o : Type} [Fintype m] (N : Matrix l m D.host.E) (M : Matrix m o k) :
    N.map (incA D) * M.map p.ι = (N.map (prH p) * M).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul_left]
  rfl

section Frames

variable {ρ : ℕ} (B : BesLev D ρ) (S : HSp D) (s : k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n)

theorem qA_iA_k : B.o.qA.map (prH p) * B.o.iA.map (prH p) = 1 := by
  rw [← Matrix.map_mul, B.o.qA_iA, Matrix.map_one _ (map_zero _) (map_one _)]

theorem qA_iB_k : B.o.qA.map (prH p) * B.o.iB.map (prH p) = 0 := by
  rw [← Matrix.map_mul, B.o.qA_iB, Matrix.map_zero _ (map_zero _)]

variable {p B s FA F₀}

theorem β_eq (h : p.IsCoreFrame B s FA F₀) :
    F₀.β = B.o.iA.map (prH p) * fromCols FA.β 0 +
      B.o.iB.map (prH p) * fromCols 0 (Matrix.of fun i (_ : Unit) => s * prH p (B.ζ i)) := by
  ext r j
  rcases j with a | u
  · rw [h.1 r a]
    simp [Matrix.mul_apply, fromCols]
    rfl
  · rw [h.2 r]
    have := RingHom.map_mulVec (prH p) B.o.iB B.ζ r
    simp only [vecB] at *
    rw [prH_apply] at this
    rw [this]
    simp [Matrix.mul_apply, fromCols, Matrix.mulVec, dotProduct, Finset.mul_sum]
    ring_nf

theorem qA_β (h : p.IsCoreFrame B s FA F₀) : B.o.qA.map (prH p) * F₀.β = fromCols FA.β 0 := by
  rw [β_eq h, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, qA_iA_k, qA_iB_k, Matrix.one_mul, Matrix.zero_mul,
    add_zero]

theorem γ_qA (h : p.IsCoreFrame B s FA F₀) : FA.γ * B.o.qA.map (prH p) = F₀.γ.toRows₁ := by
  have e : FA.γ * B.o.qA.map (prH p) = FA.γ * B.o.qA.map (prH p) * (F₀.β * F₀.γ) := by rw [F₀.βγ, Matrix.mul_one]
  rw [e, ← Matrix.mul_assoc, Matrix.mul_assoc FA.γ, qA_β h, Matrix.mul_fromCols, FA.γβ, Matrix.mul_zero,
    ← Matrix.fromRows_toRows F₀.γ, Matrix.fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.toRows₁_fromRows]

theorem γ_iA (h : p.IsCoreFrame B s FA F₀) : F₀.γ * B.o.iA.map (prH p) = fromRows FA.γ (0 : Matrix Unit (Fin B.A.rank) k) := by
  have e1 : B.o.iA.map (prH p) * FA.β = F₀.β * (fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) : Matrix (n' ⊕ Unit) n' k) := by
    rw [← Matrix.fromCols_toCols F₀.β, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
    ext r a
    exact (h.1 r a).symm
  calc F₀.γ * B.o.iA.map (prH p) = F₀.γ * (B.o.iA.map (prH p) * FA.β) * FA.γ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, FA.βγ, Matrix.mul_one]
    _ = (F₀.γ * F₀.β) * (fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) : Matrix (n' ⊕ Unit) n' k) * FA.γ := by
        rw [e1]; simp only [Matrix.mul_assoc]
    _ = fromRows FA.γ 0 := by rw [F₀.γβ, Matrix.one_mul, Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]

theorem up_slice (h : p.IsCoreFrame B s FA F₀) (x : Matrix n n' k) :
    (B.o.resS S).symm (p.up FA FS x, 0) = p.up F₀ FS (fromCols x 0) := by
  have e : fromCols x (0 : Matrix n Unit k) * F₀.γ = x * F₀.γ.toRows₁ := by
    conv_lhs => rw [← Matrix.fromRows_toRows F₀.γ]
    rw [Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero]
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, OrthDec.pA, GlobalTheory.MixModel.rat, Place.up, Place.up, map_ι_mul_rat,
    Matrix.mul_assoc, γ_qA h, Matrix.mul_assoc FS.β (fromCols x 0) F₀.γ, e, Matrix.mul_assoc]

theorem res_up (h : p.IsCoreFrame B s FA F₀) (x : Matrix n (n' ⊕ Unit) k) :
    (B.o.resS S (p.up F₀ FS x)).1 = p.up FA FS x.toCols₁ := by
  have e : x * fromRows FA.γ (0 : Matrix Unit (Fin B.A.rank) k) = x.toCols₁ * FA.γ := by
    conv_lhs => rw [← Matrix.fromCols_toCols x]
    rw [Matrix.fromCols_mul_fromRows, Matrix.mul_zero, add_zero]
  show (p.up F₀ FS x) * B.o.jA = _
  rw [OrthDec.jA, GlobalTheory.MixModel.rat, Place.up, Place.up, map_ι_mul_rat, Matrix.mul_assoc, γ_iA h, Matrix.mul_assoc, e,
    Matrix.mul_assoc]

end Frames

section Tensor

variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def splitH : Matrix n (n' ⊕ Unit) k ≃ₜ Matrix n n' k × (n → k) where
  toFun x := (x.toCols₁, fun r => x r (Sum.inr ()))
  invFun q := fromCols q.1 (Matrix.of fun r (_ : Unit) => q.2 r)
  left_inv x := by
    ext r j
    rcases j with j | j <;> rfl
  right_inv q := rfl
  continuous_toFun := (continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inl j)).prodMk
    (continuous_pi fun r => continuous_id.matrix_elem r (Sum.inr ()))
  continuous_invFun := continuous_matrix fun i j => by
    rcases j with j | j
    · exact continuous_fst.matrix_elem i j
    · exact (continuous_apply i).comp continuous_snd

variable {n n'}

def tens (a : (n → k) → ℂ) (ha : a ∈ SB (n → k)) : SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun Ξ := GlobalTheory.LocFlat.CFac.comapH (splitH n n') (GlobalTheory.LocFlat.CFac.prodSB Ξ ⟨a, ha⟩)
  map_add' Ξ Ξ' := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, add_mul]
  map_smul' c Ξ := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, mul_assoc]

theorem tens_apply (a : (n → k) → ℂ) (ha : a ∈ SB (n → k)) (Ξ : SB (Matrix n n' k)) (x : Matrix n (n' ⊕ Unit) k) :
    (tens a ha Ξ).1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ()) := rfl

end Tensor

theorem symplO_zero_right'' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem exists_isModel_slice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO B.L S, ∃ T₁, p.IsModel ψ FA FS T₁ ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ())) → ∀ u, T₀ Ψ ((B.o.resS S).symm (u, v)) = T₁ Ξ u := by
  intro D k _ _ _ _ p ψ n n' _ _ _ _ ρ B S s FA F₀ FS h T₀ hT a ha v
  let T₁ : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ fun u => (B.o.resS S).symm (u, v)) ∘ₗ T₀ ∘ₗ tens a ha
  have hT₁ : ∀ Φ u, T₁ Φ u = T₀ (tens a ha Φ) ((B.o.resS S).symm (u, v)) := fun _ _ => rfl
  refine ⟨T₁, ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact GlobalTheory.BoxSlice.isThetaFunO_slice_left B.o (hT.theta (tens a ha Φ)) v
  · have h1 : ∀ t, (tens a ha Φ').1 t = (tens a ha Φ).1 (t + fromCols x 0) := by
      intro t
      rw [tens_apply, tens_apply, hΦ]
      congr 2
      ext i j; simp [Matrix.toCols₁, fromCols]
    have h2 := hT.trans (fromCols x 0) _ _ h1
    funext u
    rw [hT₁, h2, ← up_slice S FS h x]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resS S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resS, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · have hY : IsHalf (cA D p.e) ((B.o.resS S).symm (y, 0)) := by
      intro i j
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
      simp only [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_assoc, hy i l]
    have h1 : ∀ t, (tens a ha Φ').1 t =
        ψ (symplO B.V₀ S (p.up F₀ FS t) ((B.o.resS S).symm (y, 0))) * (tens a ha Φ).1 t := by
      intro t
      rw [tens_apply, tens_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, res_up S FS h,
        symplO_zero_right'', add_zero, mul_assoc]
    have h2 := hT.modul _ hY _ _ h1
    funext u
    rw [hT₁, h2]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resS S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resS, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · have e : Ψ = tens a ha Ξ := Subtype.ext (funext fun x => (hΨ x).trans (tens_apply a ha Ξ x).symm)
    rw [e, hT₁]

end GlobalTheory.SliceModel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLocalModelSliceTargetLine
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SliceModelT

variable {D : D7}

theorem resT_symm_left {T A B : HSp D} (d : OrthDec T A B) (S : HSp D) (u : WO S A) :
    (d.resT S).symm (u, 0) = GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank) u := by
  rw [OrthDec.resT_symm_apply, GlobalTheory.MixModel.sandwich_apply, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem isThetaFunO_sliceT_left {ψ : AddChar (AF D.host.F) ℂ} {T A B S : HSp D} (d : OrthDec T A B) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (v : WO S B) : IsThetaFunO ψ S A fun u => f ((d.resT S).symm (u, v)) where
  quasi γ u := by
    have e0 : (d.resT S).symm (ratW A S γ, 0) = ratW T S (d.iA * γ) := by
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    have e : ((ratW A S γ + u, v) : WO S A × WO S B) = (ratW A S γ, (0 : WO S B)) + (u, v) := by simp
    show f ((d.resT S).symm (ratW A S γ + u, v)) = ψ (-(symplOH S A (ratW A S γ) u)) * f ((d.resT S).symm (u, v))
    rw [e, map_add, e0, hf.quasi, ← e0, d.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.MixModel.symplOH_zero_left, add_zero]
  level := by
    obtain ⟨U, hU, hk⟩ := hf.level
    refine ⟨U.comap (GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)),
      hU.preimage (GlobalTheory.MixModel.continuous_sandwich _ _), fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (hk _ hu (GlobalTheory.MixModel.map_sandwich _ _ _ h0)) ((d.resT S).symm (w, v))
    rw [← resT_symm_left] at e1
    simp only [heisO] at e1 ⊢
    rw [← e1, ← map_add (d.resT S).symm, Prod.mk_add_mk, add_zero, d.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  cont := hf.cont.comp ((d.continuous_resT_symm S).comp (continuous_id.prodMk continuous_const))
  smooth m L hL h0 w := by
    have e : ∀ t, (d.resT S).symm (w + L t, v) =
        (d.resT S).symm (w, v) + ((GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)).comp L) t := by
      intro t
      rw [AddMonoidHom.comp_apply, ← resT_symm_left, ← map_add (d.resT S).symm, Prod.mk_add_mk, add_zero]
    simp only [e]
    exact hf.smooth m ((GlobalTheory.MixModel.sandwich d.jA (1 : Mx D S.rank S.rank)).comp L)
      ((GlobalTheory.MixModel.continuous_sandwich _ _).comp hL) (fun t => GlobalTheory.MixModel.map_sandwich _ _ _ (h0 t)) _

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def prH : D.host.E →+* k := p.π.comp (incA D)

theorem ι_mul (a : AE D) (x : k) : p.ι (p.π a * x) = a * p.ι x := by
  have h1 : p.π a * x = p.π (a * p.ι x) := by rw [map_mul, p.π_ι]
  rw [h1, p.ι_π, mul_left_comm, ← p.ι_π, p.π_ι]

theorem mul_map_ι {m l n : Type} [Fintype l] (N : Matrix m l (AE D)) (M : Matrix l n k) :
    N * M.map p.ι = (N.map p.π * M).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul]

variable {ρ : ℕ} (B : BesLev D ρ) (S : HSp D) {s : k} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {FA : Frame k B.A.rank n'} {F₀ : Frame k B.V₀.rank (n' ⊕ Unit)} (FS : Frame k S.rank n)

theorem beta_eq (hF : p.IsCoreFrame B s FA F₀) :
    F₀.β = fromCols (B.o.iA.map (prH p) * FA.β) (Matrix.of fun r (_ : Unit) => s * prH p (vecB B.o B.ζ r)) := by
  ext r (a | _)
  · exact hF.1 r a
  · exact hF.2 r

theorem col_eq : (Matrix.of fun r (_ : Unit) => s * prH p (vecB B.o B.ζ r)) =
    s • (B.o.iB.map (prH p) * Matrix.of fun j (_ : Unit) => prH p (B.ζ j)) := by
  ext r u
  simp [Matrix.mul_apply, vecB, Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem qA_beta (hF : p.IsCoreFrame B s FA F₀) : B.o.qA.map (prH p) * F₀.β = fromCols FA.β 0 := by
  rw [beta_eq p B hF, col_eq, Matrix.mul_fromCols, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Matrix.map_mul, ← Matrix.map_mul, B.o.qA_iA, B.o.qA_iB, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, smul_zero]

theorem up_fromRows (hF : p.IsCoreFrame B s FA F₀) (x : Matrix n' n k) :
    p.up FS F₀ (fromRows x 0) = (B.o.resT S).symm (p.up FS FA x, 0) := by
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Place.up, Place.up, OrthDec.jA, rat, mul_map_ι,
    beta_eq p B hF, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, Matrix.map_map]
  simp only [Matrix.mul_assoc]
  rfl

theorem resT_up_fst (hF : p.IsCoreFrame B s FA F₀) (x : Matrix (n' ⊕ Unit) n k) :
    (B.o.resT S (p.up FS F₀ x)).1 = p.up FS FA x.toRows₁ := by
  rw [OrthDec.resT_apply]
  dsimp only
  rw [Place.up, Place.up, OrthDec.pA, rat, mul_map_ι, Matrix.map_map]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  change (B.o.qA.map (prH p) * F₀.β) * x * FS.γ = _
  rw [qA_beta p B hF]
  conv_lhs => rw [← fromRows_toRows x]
  rw [fromCols_mul_fromRows, Matrix.zero_mul, add_zero]

theorem symplO_zero_right' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

def rowsH (n n' : Type) [Fintype n] [Fintype n'] : Matrix (n' ⊕ Unit) n k ≃ₜ Matrix n' n k × (n → k) where
  toFun x := (x.toRows₁, x (Sum.inr ()))
  invFun q := fromRows q.1 (Matrix.of fun _ => q.2)
  left_inv x := by
    ext (i | i) j <;> rfl
  right_inv q := by
    ext i j <;> rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ (continuous_apply _)
    exact continuous_pi fun i => continuous_apply (Sum.inl i)
  continuous_invFun := by
    refine continuous_pi fun i => ?_
    rcases i with i | i
    · exact (continuous_apply i).comp continuous_fst
    · exact continuous_snd

def tens (a : SB (n → k)) : SB (Matrix n' n k) →ₗ[ℂ] SB (Matrix (n' ⊕ Unit) n k) where
  toFun Ξ := GlobalTheory.LocFlat.CFac.comapH (rowsH n n') (GlobalTheory.LocFlat.CFac.prodSB Ξ a)
  map_add' Ξ Ξ' := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, add_mul]
  map_smul' c Ξ := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, mul_assoc]

theorem tens_apply (a : SB (n → k)) (Ξ : SB (Matrix n' n k)) (x : Matrix (n' ⊕ Unit) n k) :
    (tens a Ξ).1 x = Ξ.1 x.toRows₁ * a.1 (x (Sum.inr ())) := rfl

end GlobalTheory.SliceModelT

open GlobalTheory.SliceModelT in

theorem GlobalTheory.SliceModelT.main : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ FS F₀ T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO S B.L, ∃ T₁, p.IsModel ψ FS FA T₁ ∧ ∀ (Ξ : SB (Matrix n' n k)) (Ψ : SB (Matrix (n' ⊕ Unit) n k)), (∀ x, Ψ.1 x = Ξ.1 x.toRows₁ * a (x (Sum.inr ()))) → ∀ u, T₀ Ψ ((B.o.resT S).symm (u, v)) = T₁ Ξ u := by
  intro D k _ _ _ _ p ψ n n' _ _ _ _ ρ B S s FA F₀ FS hF T₀ hT a ha v
  let a' : SB (n → k) := ⟨a, ha⟩
  let T₁ : SB (Matrix n' n k) →ₗ[ℂ] (WO S B.A → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (fun u : WO S B.A => (B.o.resT S).symm (u, v))) ∘ₗ T₀ ∘ₗ tens a'
  have hT₁ : ∀ Ξ u, T₁ Ξ u = T₀ (tens a' Ξ) ((B.o.resT S).symm (u, v)) := fun _ _ => rfl
  refine ⟨T₁, ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact isThetaFunO_sliceT_left B.o (hT.theta _) v
  · have h1 := hT.trans (fromRows x 0) (tens a' Φ) (tens a' Φ') (fun t => by
      have e1 : (t + fromRows x (0 : Matrix Unit n k)).toRows₁ = t.toRows₁ + x := by
        ext i j; simp [Matrix.toRows₁, Matrix.fromRows_apply_inl]
      have e2 : (t + fromRows x (0 : Matrix Unit n k) : Matrix (n' ⊕ Unit) n k) (Sum.inr ()) = t (Sum.inr ()) := by
        funext j; simp [Matrix.fromRows_apply_inr]
      rw [tens_apply, tens_apply, hΦ, e1, e2])
    funext u
    rw [hT₁, h1, up_fromRows p B S FS hF]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resT S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · set Y : WO S B.V₀ := (B.o.resT S).symm (y, 0) with hYdef
    have hY : IsHalf (cA D p.e) Y := by
      intro i j
      rw [hYdef, OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [mul_left_comm, hy l j]
    have h1 := hT.modul Y hY (tens a' Φ) (tens a' Φ') (fun t => by
      rw [tens_apply, tens_apply, hΦ, B.o.symplO_resT, resT_up_fst p B S FS hF, hYdef, AddEquiv.apply_symm_apply,
        symplO_zero_right', add_zero, mul_assoc])
    funext u
    rw [hT₁, h1]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resT S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resT, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · have e : Ψ = tens a' Ξ := Subtype.ext (funext hΨ)
    rw [e, hT₁]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
section
noncomputable section
open scoped TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mt_mul_gaMat (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one_gaMat (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl

theorem Place.pi_idem (p : Place D k) : p.π p.e = 1 := by
  have h1 := p.ι_π 1
  rw [mul_one, map_one] at h1
  rw [← h1, p.π_ι]

theorem Place.pi_eq_of_toEAf (p : Place D k) {a b : AE D} (h : toEAf D a = toEAf D b) : p.π a = p.π b := by
  have hf : finPart D a = finPart D b :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E).injective h
  have key : p.e * a = p.e * b := GlobalTheory.SplitScalar.adele_ext
    (by rw [map_mul, map_mul, GlobalTheory.SplitScalar.infPart_splitIdem p.split, zero_mul, zero_mul])
    (by rw [map_mul, map_mul, hf])
  calc p.π a = p.π (p.e * a) := by rw [map_mul, p.pi_idem, one_mul]
    _ = p.π (p.e * b) := by rw [key]
    _ = p.π b := by rw [map_mul, p.pi_idem, one_mul]

theorem Place.map_pi_eq_of_toEAf (p : Place D k) {m n : ℕ} {a b : Matrix (Fin m) (Fin n) (AE D)}
    (h : a.map (toEAf D) = b.map (toEAf D)) : a.map p.π = b.map p.π := by
  ext i j
  exact p.pi_eq_of_toEAf (congrFun (congrFun h i) j)

theorem exists_toEAf_lift (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul b α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] b, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩

def liftM {m n : ℕ} (x : Matrix (Fin m) (Fin n) (EAf D)) : Matrix (Fin m) (Fin n) (AE D) :=
  x.map fun z => (exists_toEAf_lift z).choose

theorem liftM_map {m n : ℕ} (x : Matrix (Fin m) (Fin n) (EAf D)) : (liftM x).map (toEAf D) = x := by
  ext i j
  exact (exists_toEAf_lift (x i j)).choose_spec

def stdFrame (k : Type) [Field k] (N : ℕ) : Frame k N (Fin N) := ⟨1, 1, by simp, by simp⟩

theorem exists_GL_mul_of_mul_eq_one {n : ℕ} (M : GL (Fin n) k) (N Ni : Matrix (Fin n) (Fin n) k) (h : N * Ni = 1) :
    ∃ gk : GL (Fin n) k, gk.val = M.val * Ni := by
  have h' : Ni * N = 1 := (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 h
  exact ⟨M * ⟨Ni, N, h', h⟩, rfl⟩

theorem Place.exists_movedTo (p : Place D k) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (M : GL (Fin V.rank) k) (g₀ : GA D V) : ∃ g, SuppAt p.e V g ∧ MovedTo p V (g * g₀) β M.val := by
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Matrix (Fin V.rank) (Fin V.rank) (AE D), b₀.map (toEAf D) = β.val :=
    ⟨liftM β.val, liftM_map _⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Matrix (Fin V.rank) (Fin V.rank) (AE D), c₀.map (toEAf D) = (β⁻¹).val :=
    ⟨liftM (β⁻¹).val, liftM_map _⟩
  have hbc : b₀.map p.π * c₀.map p.π = 1 := by
    rw [← Matrix.map_mul]
    have h1 : (b₀ * c₀).map (toEAf D) = (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).map (toEAf D) := by
      rw [Matrix.map_mul, hb₀, hc₀, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul, mul_inv_cancel,
        Units.val_one]
    rw [p.map_pi_eq_of_toEAf h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hN : ((mt V g₀).map p.π * b₀.map p.π) * (c₀.map p.π * (mt V g₀⁻¹).map p.π) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (b₀.map p.π), hbc, Matrix.one_mul, ← Matrix.map_mul, ← mt_mul_gaMat,
      mul_inv_cancel, mt_one_gaMat, Matrix.map_one _ (map_zero _) (map_one _)]
  have hN' : (c₀.map p.π * (mt V g₀⁻¹).map p.π) * ((mt V g₀).map p.π * b₀.map p.π) = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq _ _ _ rfl).1 hN
  obtain ⟨gk, hgk⟩ := exists_GL_mul_of_mul_eq_one M _ _ hN
  obtain ⟨g, hg, -⟩ := ((GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p).1 V (Fin V.rank) (stdFrame k V.rank)).1 gk
  refine ⟨g, hg.1, fun b hb => ?_⟩
  have h2 : (mt V g).map p.π = gk.val := by
    rw [hg.2]
    change (1 : Matrix (Fin V.rank) (Fin V.rank) k) * gk.val * 1 = gk.val
    rw [Matrix.one_mul, Matrix.mul_one]
  have hbb : b.map p.π = b₀.map p.π := p.map_pi_eq_of_toEAf (by rw [hb, hb₀])
  rw [mt_mul_gaMat, Matrix.map_mul, Matrix.map_mul, h2, hbb, hgk, Matrix.mul_assoc (M.val * _), Matrix.mul_assoc M.val,
    hN', Matrix.mul_one]

theorem normalFrames_and_basePoint_exist : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k), p.xi ≠ 0 → (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n), s ≠ 0 → (∃ F : Frame k B.V₀.rank (n ⊕ Unit), p.IsCoreFrame B s FA F) ∧ ∃ F : Frame k B.V.rank (n ⊕ Fin (2 * ρ + 1)), p.IsBesFrame B s FA F) ∧ (∀ (n : Type) [Fintype n] [DecidableEq n] (ρ : ℕ) (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n), s ≠ 0 → hh ≠ 0 → ∃ F : Frame k J.W.rank (n ⊕ Fin (2 * ρ)), p.IsJacFrame J s hh F₀ F) ∧ ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (M : GL (Fin V.rank) k) (g₀ : GA D V), ∃ g, SuppAt p.e V g ∧ MovedTo p V (g * g₀) β M.val :=
  fun _ _ _ _ _ _ p _ =>
    ⟨fun _ _ _ _ B _ FA hs => ⟨p.exists_isCoreFrame hs B FA, p.exists_isBesFrame hs B FA⟩,
      fun _ _ _ _ J _ _ F₀ hs hh0 => p.exists_isJacFrame hs J hh0 F₀,
      fun V β M g₀ => p.exists_movedTo V β M g₀⟩

end GlobalTheory.LocMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagUnipotentHaarEqMapCoordinatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotentHaar_eq_map_coordinates : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (vN : VolN d) (vb : VolM D ρ V₀.rank) (vU : VolU D ρ) (e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d), (∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1)) → ∀ (lC : Measure (skewA D ρ)) (𝓒 : Set (skewA D ρ)), lC.IsAddHaarMeasure → SFinite lC → IsAddFundamentalDomain ((ratMx D ρ ρ).addSubgroupOf (skewA D ρ)) 𝓒 lC → lC 𝓒 = 1 → vN.ν = (lC.prod (vb.μ.prod vU.ν)).map e := by
  first | exact @GlobalTheory.HaarCoordsUnit.volN_eq_map_coords | exact GlobalTheory.HaarCoordsUnit.volN_eq_map_coords | (intros; apply GlobalTheory.HaarCoordsUnit.volN_eq_map_coords <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockVectorsLatticeVacuaOffFiniteSetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vectors_lattice_vacua_off_finite_set : ∀ D : D7, ForStep D fun c _ s s' p => ∀ φ, ∀ v ∉ c.S, VacFin c.ψ s.V s'.V v (p.pt φ) := by
  first | exact @GlobalTheory.ChainOnto.fock_vacFin_off | exact GlobalTheory.ChainOnto.fock_vacFin_off | (intros; apply GlobalTheory.ChainOnto.fock_vacFin_off <;> assumption)
end

