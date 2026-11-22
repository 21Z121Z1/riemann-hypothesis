import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0065
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0105
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesMultiplication
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FlatBFLoc.ModelModul
variable {D : D7}

theorem symplectic_pairing_ext_zero_inc_zero {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (t : WO V W)
    (y : WO V₀ W₀) : symplO V W t (dV.ext0 W (dW.inc0 V₀ y)) = symplO V₀ W₀ (dW.p0 ⬝ t ⬝ dV.j0) y := by
  unfold symplO
  congr 2
  have h1 : dW.pY ⬝ (dW.j0 ⬝ y) = 0 := by rw [← Matrix.mul_assoc, HypDec.pY_j0, Matrix.zero_mul]
  have h2 : dW.pX ⬝ (dW.j0 ⬝ y) = 0 := by rw [← Matrix.mul_assoc, HypDec.pX_j0, Matrix.zero_mul]
  have h3 : dW.p0 ⬝ (dW.j0 ⬝ y) = y := by rw [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
  rw [dV.hO_coordS, dW.hO_coordT]
  simp only [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_assoc, HypDec.p0_jX, HypDec.p0_jY, HypDec.p0_j0,
    Matrix.mul_zero, Matrix.mul_one, h1, h2, h3]
  simp [pairS, pairT]

theorem isHalf_mul {a b c d : ℕ} {e : AE D} (A : Mx D a b) {y : Mx D b c} (C : Mx D c d) (hy : IsHalf e y) :
    IsHalf e (A ⬝ y ⬝ C) := by
  have h : e • y = y := Matrix.ext fun i j => hy i j
  intro i j
  have h2 : e • (A ⬝ y ⬝ C) = A ⬝ y ⬝ C := by rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]
  exact congrFun (congrFun h2 i) j

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem mul_iota (b : AE D) (a : k) : b * p.ι a = p.ι (p.π b * a) := by
  have h1 : p.e * p.ι a = p.ι a := by rw [← p.ι_π, p.π_ι]
  have h2 := p.ι_π (b * p.ι a)
  rw [map_mul, p.π_ι, mul_left_comm, h1] at h2
  exact h2.symm

theorem rat_mul_iota {a b c : ℕ} (R : Matrix (Fin a) (Fin b) D.host.E) (A : Matrix (Fin b) (Fin c) k) :
    rat R ⬝ (A.map p.ι : Mx D b c) = ((R.map p.pr * A).map p.ι : Mx D a c) := by
  ext i j
  simp only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, mul_iota, Place.pr]

theorem iota_mul_rat {a b c : ℕ} (A : Matrix (Fin a) (Fin b) k) (R : Matrix (Fin b) (Fin c) D.host.E) :
    (A.map p.ι : Mx D a b) ⬝ rat R = ((A * R.map p.pr).map p.ι : Mx D a c) := by
  ext i j
  simp only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, Place.pr]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm, mul_iota, mul_comm]

theorem map_pr_mul {a b c : ℕ} (R : Matrix (Fin a) (Fin b) D.host.E) (R' : Matrix (Fin b) (Fin c) D.host.E) :
    (R * R').map p.pr = R.map p.pr * R'.map p.pr :=
  Matrix.map_mul (f := p.π.comp (incA D))

theorem q_zero_projection_identities {W W₀ : HSp D} {σ : ℕ} (d : HypDec W W₀ σ) :
    d.q0.map p.pr * d.i₀.map p.pr = 1 ∧ d.q0.map p.pr * d.e.map p.pr = 0 ∧ d.q0.map p.pr * d.e'.map p.pr = 0 := by
  have h1 : d.q0 * d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.p0_j0)
  have h2 : d.q0 * d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.p0_jX)
  have h3 : d.q0 * d.e' = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.p0_jY)
  have z : p.pr 0 = 0 := map_zero (p.π.comp (incA D))
  have o : p.pr 1 = 1 := map_one (p.π.comp (incA D))
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_pr_mul, h1, Matrix.map_one _ z o]
  · rw [← map_pr_mul, h2, Matrix.map_zero _ z]
  · rw [← map_pr_mul, h3, Matrix.map_zero _ z]

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem q_zero_jacobi_frame_projection {ρ : ℕ} (J : JacLev D ρ) (s hh : k) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c))
    (h : p.IsJacFrame J s hh G₀ FW) : J.d.q0.map p.pr * FW.β = fromCols G₀.β 0 := by
  obtain ⟨hc, h0, hX, hY⟩ := h
  obtain ⟨q1, q2, q3⟩ := q_zero_projection_identities p J.d
  have key : ∀ (E : Matrix (Fin J.W.rank) (Fin ρ) D.host.E), J.d.q0.map p.pr * E.map p.pr = 0 → ∀ (a : k) (i : Fin ρ)
      (j : Fin c), (∀ r, FW.β r (Sum.inr j) = a * p.pr (E r i)) → ∀ r, (J.d.q0.map p.pr * FW.β) r (Sum.inr j) = 0 := by
    intro E hE a i j hj r
    have := congrFun (congrFun hE r) i
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, hj]
    rw [← mul_zero a, ← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  ext r q
  rcases q with a | j
  · have : (J.d.q0.map p.pr * FW.β) r (Sum.inl a) = (J.d.q0.map p.pr * (J.d.i₀.map p.pr * G₀.β)) r a := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [h0]
    rw [this, ← Matrix.mul_assoc, q1, Matrix.one_mul, fromCols_apply_inl]
  · rw [fromCols_apply_inr, Matrix.zero_apply]
    by_cases hj : j.val < ρ
    · exact key _ q2 _ ⟨j.val, hj⟩ j (hX ⟨j.val, hj⟩ j rfl) r
    · have := j.2
      exact key _ q3 _ ⟨2 * ρ - 1 - j.val, by omega⟩ j (hY ⟨2 * ρ - 1 - j.val, by omega⟩ j (by simp only []; omega)) r

theorem bessel_normal_frame_core_frame_part {ρ : ℕ} (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (FV : Frame k B.V.rank (n' ⊕ Fin c)) (h₀ : p.IsCoreFrame B s FA F₀) (h : p.IsBesFrame B s FA FV) (j : Fin c)
    (hj : j.val = ρ) : B.d.i₀.map p.pr * F₀.β = FV.β.submatrix id (Sum.map id fun _ => j) := by
  obtain ⟨-, h0, -, hz, -⟩ := h
  ext r q
  rcases q with a | u
  · have : (B.d.i₀.map p.pr * F₀.β) r (Sum.inl a) = (B.d.i₀.map p.pr * (B.o.iA.map p.pr * FA.β)) r a := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [h₀.1]
    rw [this, ← Matrix.mul_assoc, ← map_pr_mul]
    exact (h0 r a).symm
  · cases u
    have h2 : p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r) = ∑ m, p.pr (B.d.i₀ r m) * p.pr (vecB B.o B.ζ m) := by
      simp only [Place.pr, Matrix.mulVec, dotProduct, map_sum, map_mul]
    simp only [Matrix.submatrix_apply, Sum.map_inr, id, hz j hj r, h2, Matrix.mul_apply, Matrix.map_apply, h₀.2,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem core_up {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (s hh : k) (FA : Frame k B.A.rank n')
    (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n)
    (FW : Frame k J.W.rank (n ⊕ Fin c)) (h₀ : p.IsCoreFrame B s FA F₀) (hB : p.IsBesFrame B s FA FV)
    (hJ : p.IsJacFrame J s hh G₀ FW) (j : Fin (c + 1)) (hj : j.val = ρ) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    J.d.p0 ⬝ (p.up FV FW t : WO B.V J.W) ⬝ B.d.j0 = p.up F₀ G₀ (t.submatrix Sum.inl (Sum.map id fun _ => j)) := by
  have h1 := q_zero_jacobi_frame_projection p J s hh G₀ FW hJ
  have h2 := bessel_normal_frame_core_frame_part p B s FA F₀ FV h₀ hB j hj
  have h3 : t * FV.γ * B.d.i₀.map p.pr = t.submatrix id (Sum.map id fun _ => j) * F₀.γ := by
    rw [← Matrix.mul_one (t * FV.γ * B.d.i₀.map p.pr), ← F₀.βγ, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ F₀.β, h2]
    congr 1
    have : t * FV.γ * FV.β = t := by rw [Matrix.mul_assoc, FV.γβ, Matrix.mul_one]
    ext r q
    conv_rhs => rw [← this]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  unfold Place.up HypDec.p0 HypDec.j0
  rw [rat_mul_iota, iota_mul_rat]
  congr 1
  rw [Matrix.mul_assoc FW.β, ← Matrix.mul_assoc _ FW.β, h1, Matrix.mul_assoc, h3]
  refine (Matrix.mul_assoc _ _ _).symm.trans ?_
  congr 1
  ext r q
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem submatrix_affPt (ρ : ℕ) (j : Fin (c + 1)) (hj : j.val = ρ) (x : Matrix n (n' ⊕ Unit) k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} → k) :
    (affPt (ρ + 1) x.toCols₁ e + GlobalTheory.LocFlat.colAt n' c (ρ + 1) fun r => x r (Sum.inr ())).submatrix Sum.inl
      (Sum.map id fun _ => j) = x := by
  ext r q
  rcases q with a | u
  · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, Free]
  · cases u
    simp [affPt, basePt, GlobalTheory.LocFlat.colAt, Free, hj]

theorem continuous_hO_up {S T : HSp D} (FS : Frame k S.rank n') (FT : Frame k T.rank n) (y : WO S T) :
    Continuous fun t => p.π (hO S T (p.up FS FT t) y) := by
  have hx : ∀ i j, Continuous fun t => p.up FS FT t i j := fun i j =>
    p.cont_ι.comp (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j)
  refine p.cont_π.comp ?_
  exact continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ =>
      continuous_finset_sum _ fun _ _ => continuous_const.mul (hx _ _)

theorem model_modul : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ (y : WO B.V₀ J.W₀), IsHalf (cA D p.e) y → ∀ (Ψ Ψ' : SB (Matrix n (n' ⊕ Unit) k)), (∀ t, Ψ'.1 t = ψ (symplO B.V₀ J.W₀ (p.up F₀ G₀ t) y) * Ψ.1 t) → L₀ Ψ' = heisO ψ B.V₀ J.W₀ y (L₀ Ψ) := by
  intro D _ hLaws _ k _ _ _ _ _ _ p ν hν ψ ψk hψk ρ B J st s _ n n' _ _ _ _ c FA F₀ FV G₀ FW h₀ hB hJ Tm hTm L₀ hL₀ y hy
    Ψ Ψ' hΨ'
  have hψc : Continuous ψk := ((GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ st.weil.std).2.1 ψk hψk).1
  have hc : c = 2 * ρ := hJ.1
  obtain ⟨Φ, hΦSB, hΦ⟩ := ((GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k ψk ν hψc hν n n' c (ρ + 1) (by omega)).1 (by omega)).2 Ψ.1 Ψ.2
  have hy' : IsHalf (cA D p.e) (B.d.ext0 J.W (J.d.inc0 B.V₀ y)) := isHalf_mul J.d.j0 B.d.p0 hy
  have hχ : IsLocallyConstant fun t => ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.inc0 B.V₀ y))) := by
    have h := (GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψk hψc).comp_continuous
      (continuous_hO_up p FV FW (B.d.ext0 J.W (J.d.inc0 B.V₀ y)))
    have h4 := (GlobalTheory.T.heisenberg_frame_half_inverse D k p _ _ B.V J.W FV FW ψ ψk hψk).2.2.2.1
    have h5 : (fun t => ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.inc0 B.V₀ y)))) = _ :=
      funext fun t => h4 t _ hy'
    rw [h5]
    exact h
  let Φ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := ⟨Φ, hΦSB⟩
  let Φ₂ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
    ⟨fun t => ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.inc0 B.V₀ y))) * Φ t,
      hχ.mul hΦSB.1, hΦSB.2.mul_left⟩
  have h1 := hTm.modul _ hy' Φ₁ Φ₂ fun t => rfl
  have hMx : GlobalTheory.FinPl.MxAt (fun _ => True) y := fun i j =>
    ⟨congrFun (congrFun (GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj p.split) hy) i) j,
      Ideal.mem_iInf.2 fun w => (w.2 trivial).elim⟩
  have h2 := ((hLaws ψ fun _ => True).1 ρ B J st).Heisenberg₂.core (Tm Φ₁) (hTm.theta Φ₁) y hMx
  have h3 := hL₀ Φ₁ Ψ hΦ.symm
  have h4 : Ψ'.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ₂.1 := by
    funext x
    rw [hΨ' x, ← hΦ]
    unfold GlobalTheory.LocFlat.flCol GlobalTheory.RootEx.opE
    rw [← integral_const_mul]
    congr 1
    funext e
    have hj : ρ < c + 1 := by omega
    simp only [Φ₂]
    rw [symplectic_pairing_ext_zero_inc_zero, core_up p B J s _ FA F₀ FV G₀ FW h₀ hB hJ ⟨ρ, hj⟩ rfl, submatrix_affPt ρ ⟨ρ, hj⟩ rfl, mul_assoc]
  rw [← hL₀ Φ₂ Ψ' h4, h1, h2, h3]

end GlobalTheory.FlatBFLoc.ModelModul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesTranslations
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatTrans

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem ι_sandwich (a c : AE D) (m : k) : p.ι (p.π a * m * p.π c) = a * p.ι m * c := by
  rw [GlobalTheory.LocChar.ι_mul, GlobalTheory.LocChar.ι_mul, p.ι_π, p.ι_π]
  have h := GlobalTheory.LocChar.e_mul_ι p m
  linear_combination (a * c * p.e + a * c) * h

theorem mul_map_ι_mul {a b l m : Type} [Fintype a] [Fintype b] (A : Matrix m a (AE D)) (M : Matrix a b k)
    (C : Matrix b l (AE D)) : A * M.map p.ι * C = (A.map p.π * M * C.map p.π).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_sum, ι_sandwich]

theorem map_incA_map {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) : (M.map (incA D)).map p.π = M.map p.pr := by
  ext; rfl

theorem ι_mem_idAt : ∃ v, ∀ y : k, p.ι y ∈ GlobalTheory.FinPl.idAt D (· = v) := by
  obtain ⟨-, he, v, ε, hε, hsum⟩ := p.split
  refine ⟨v, fun y => GlobalTheory.FinPl.Model.mem_idAt_iff.2 ?_⟩
  have hε' := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 hε
  subst hε'
  rw [← hsum]
  have h1 := GlobalTheory.LocChar.e_mul_ι p y
  have h2 : cA D p.e * p.e = 0 := by rw [mul_comm]; exact he
  linear_combination (1 - cA D p.e) * h1 + p.ι y * h2

theorem sb_translate {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] {Φ : X → ℂ}
    (hΦ : Φ ∈ SB X) (t : X) : (fun z => Φ (z + t)) ∈ SB X :=
  ⟨hΦ.1.comp_continuous (continuous_add_const t), hΦ.2.comp_homeomorph (Homeomorph.addRight t)⟩

section Local
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def bigPt (c ρ : ℕ) (x : Matrix n (n' ⊕ Unit) k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks x.toCols₁ (Matrix.of fun r i => if i.val = ρ then x r (Sum.inr ()) else 0) 0 0

theorem flCol_translate [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (c ρ : ℕ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x t : Matrix n (n' ⊕ Unit) k) :
    GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) (fun z => Φ (z + bigPt c ρ x)) t = GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ (t + x) := by
  unfold GlobalTheory.LocFlat.flCol GlobalTheory.RootEx.opE
  congr 1
  funext e
  have h1 : affPt (ρ + 1) t.toCols₁ e + GlobalTheory.LocFlat.colAt n' c (ρ + 1) (fun r => t r (Sum.inr ())) + bigPt c ρ x =
      affPt (ρ + 1) (t + x).toCols₁ e + GlobalTheory.LocFlat.colAt n' c (ρ + 1) (fun r => (t + x) r (Sum.inr ())) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt, add_right_comm]
    · by_cases h : j.val = ρ <;> simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt, h, add_assoc]
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt]
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt]
  have h2 : ch (affPt (ρ + 1) t.toCols₁ e) = ch (affPt (ρ + 1) (t + x).toCols₁ e) := by
    simp [ch, affPt, basePt]
  simp only [h1, h2]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq n] [DecidableEq n'] in

theorem mul_bigPt_mul {a b : Type} {c ρ : ℕ} (j₀ : Fin (c + 1)) (hj : j₀.val = ρ) (β : Matrix a (n ⊕ Fin c) k) (β₀ : Matrix a n k)
    (γ : Matrix (n' ⊕ Fin (c + 1)) b k) (γ₀ : Matrix (n' ⊕ Unit) b k) (hβ : ∀ r i, β r (Sum.inl i) = β₀ r i)
    (hγ : ∀ i s, γ (Sum.inl i) s = γ₀ (Sum.inl i) s) (hγ' : ∀ s, γ (Sum.inr j₀) s = γ₀ (Sum.inr ()) s)
    (x : Matrix n (n' ⊕ Unit) k) : β * bigPt c ρ x * γ = β₀ * x * γ₀ := by
  ext r s
  have hj' : ∀ j : Fin (c + 1), j.val = ρ ↔ j = j₀ := fun j => by rw [← hj, Fin.val_inj]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, bigPt, hβ, hγ, hj', hγ', Finset.sum_ite_irrel]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem rows_of_inverse {N N₀ c : ℕ} (j₀ : Fin (c + 1)) (F : Frame k N (n' ⊕ Fin (c + 1))) (F₀ : Frame k N₀ (n' ⊕ Unit))
    (q : Matrix (Fin N₀) (Fin N) k) (h1 : ∀ r i, (q * F.β) r (Sum.inl i) = F₀.β r (Sum.inl i))
    (h2 : ∀ r, (q * F.β) r (Sum.inr j₀) = F₀.β r (Sum.inr ())) (h3 : ∀ r j, j ≠ j₀ → (q * F.β) r (Sum.inr j) = 0) :
    (∀ i s, F.γ (Sum.inl i) s = (F₀.γ * q) (Sum.inl i) s) ∧ ∀ s, F.γ (Sum.inr j₀) s = (F₀.γ * q) (Sum.inr ()) s := by
  let σ : n' ⊕ Unit → n' ⊕ Fin (c + 1) := Sum.map id fun _ => j₀
  have hq : F₀.β * F.γ.submatrix σ id = q := by
    conv_rhs => rw [← Matrix.mul_one q, ← F.βγ, ← Matrix.mul_assoc]
    ext r s
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type,
      Finset.sum_eq_single j₀ (fun j _ hj => by rw [h3 r j hj, zero_mul]) (by simp), h2]
    simp [h1, σ]
  have hγ : F₀.γ * q = F.γ.submatrix σ id := by rw [← hq, ← Matrix.mul_assoc, F₀.γβ, Matrix.one_mul]
  rw [hγ]
  exact ⟨fun _ _ => rfl, fun _ => rfl⟩

end Local

theorem proj_laws {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    d.p0.map p.π * d.i₀.map p.pr = 1 ∧ d.p0.map p.π * d.e.map p.pr = 0 ∧ d.p0.map p.π * d.e'.map p.pr = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_incA_map, ← Matrix.map_mul]
    exact (congrArg (·.map p.π) d.p0_j0).trans (Matrix.map_one _ (map_zero _) (map_one _))
  · rw [← map_incA_map, ← Matrix.map_mul]
    exact (congrArg (·.map p.π) d.p0_jX).trans (Matrix.map_zero _ (map_zero _))
  · rw [← map_incA_map, ← Matrix.map_mul]
    exact (congrArg (·.map p.π) d.p0_jY).trans (Matrix.map_zero _ (map_zero _))

def prHom : D.host.E →+* k := p.π.comp (incA D)

theorem pr_eq : p.pr = prHom p := rfl

theorem up_bigPt {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (s hh : k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {c : ℕ} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c))
    (hC : p.IsCoreFrame B s FA F₀) (hB : p.IsBesFrame B s FA FV) (hJ : p.IsJacFrame J s hh G₀ FW)
    (x : Matrix n (n' ⊕ Unit) k) :
    p.up FV FW (bigPt c ρ x) = B.d.ext0 J.W (J.d.inc0 B.V₀ (p.up F₀ G₀ x)) := by
  obtain ⟨hc, hinl, hlt, heq, hgt⟩ := hB
  obtain ⟨q1, q2, q3⟩ := proj_laws p B.d
  let j₀ : Fin (c + 1) := ⟨ρ, by omega⟩
  have col : ∀ (r : Fin B.V₀.rank) (j : n' ⊕ Fin (c + 1)) (a : k) (y : Fin B.V.rank → k), (∀ r', FV.β r' j = a * y r') →
      (B.d.p0.map p.π * FV.β) r j = a * (B.d.p0.map p.π *ᵥ y) r := fun r j a y h => by
    simp only [Matrix.mul_apply, h, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
  obtain ⟨g1, g2⟩ := rows_of_inverse j₀ FV F₀ (B.d.p0.map p.π)
    (fun r i => by
      rw [hC.1, ← Matrix.one_mul (B.o.iA.map p.pr * FA.β), ← q1, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [hinl, pr_eq, Matrix.map_mul, Matrix.mul_assoc])
    (fun r => by
      rw [col r _ s (B.d.i₀.map p.pr *ᵥ fun i => p.pr (vecB B.o B.ζ i)) fun r' => by
        rw [heq j₀ rfl, pr_eq, RingHom.map_mulVec]; rfl, Matrix.mulVec_mulVec, q1, Matrix.one_mulVec, hC.2])
    (fun r j hj => by
      have hj' : j.val ≠ ρ := fun h => hj (Fin.ext h)
      rcases lt_or_gt_of_ne hj' with h | h
      · rw [col r _ _ _ (hlt ⟨j.val, h⟩ j rfl)]
        exact mul_eq_zero_of_right _ (congrFun (congrFun q2 r) ⟨j.val, h⟩)
      · have := j.2
        rw [col r _ _ _ (hgt ⟨2 * ρ - j.val, by omega⟩ j (by simp only; omega))]
        exact mul_eq_zero_of_right _ (congrFun (congrFun q3 r) ⟨2 * ρ - j.val, by omega⟩))
  rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Place.up, Place.up,
    mul_bigPt_mul j₀ rfl FW.β _ FV.γ _ hJ.2.1 g1 g2, ← map_incA_map]
  refine Eq.trans ?_ (mul_map_ι_mul p J.d.j0 _ B.d.p0).symm
  simp only [Matrix.mul_assoc]
  rfl

theorem factor_trans : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ (x : Matrix n (n' ⊕ Unit) k) (Ψ Ψ' : SB (Matrix n (n' ⊕ Unit) k)), (∀ t, Ψ'.1 t = Ψ.1 (t + x)) → L₀ Ψ' = heisO ψ B.V₀ J.W₀ (p.up F₀ G₀ x) (L₀ Ψ) := by
  intro D _ hFLs _ k _ _ _ _ _ _ p ν hν ψ ψk hpc ρ B J st s _ n n' _ _ _ _ c FA F₀ FV G₀ FW hC hB hJ Tm hTm L₀ hL₀ x Ψ Ψ' hΨ
  have hψc : Continuous ψk := ((GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ st.weil.std).2.1 ψk hpc).1
  have hc : c = 2 * ρ := hJ.1
  obtain ⟨Φ, hΦ, hΦΨ⟩ := ((GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k ψk ν hψc hν n n' c (ρ + 1) (by omega)).1 (by omega)).2 Ψ.1 Ψ.2
  have h1 : flatBF st (Tm ⟨Φ, hΦ⟩) = L₀ Ψ := hL₀ _ _ hΦΨ.symm
  have h2 : flatBF st (Tm ⟨_, sb_translate hΦ (bigPt c ρ x)⟩) = L₀ Ψ' := hL₀ _ _ (by
    funext t
    rw [hΨ, ← hΦΨ]
    exact (flCol_translate ψk ν c ρ Φ x t).symm)
  have h3 := hTm.trans (bigPt c ρ x) ⟨Φ, hΦ⟩ ⟨_, sb_translate hΦ (bigPt c ρ x)⟩ fun _ => rfl
  obtain ⟨v, hv⟩ := ι_mem_idAt p
  rw [← h2, h3, up_bigPt p B J s _ FA F₀ FV G₀ FW hC hB hJ, ← h1]
  exact ((hFLs ψ (· = v)).1 ρ B J st).Heisenberg₂.core _ (hTm.theta _) _ fun i j => hv _

end GlobalTheory.FlatTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelCentralTermsViaGramMatrices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.CentralGram

variable {D : D7}

theorem trace_incA_eq (x : D.host.E) : Algebra.trace (AF D.host.F) (AE D) (incA D x) =
    algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E x) := by
  show Algebra.trace (AF D.host.F) (AE D) ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

def qG {ρ : ℕ} (A c : Mx D ρ ρ) : AF D.host.F :=
  algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) (A ⬝ c).trace

theorem qG_add_right {ρ : ℕ} (A c c' : Mx D ρ ρ) : qG A (c + c') = qG A c + qG A c' := by
  simp only [qG, Matrix.mul_add, Matrix.trace_add, map_add, mul_add]

theorem qG_sub_left {ρ : ℕ} (A A' c : Mx D ρ ρ) : qG (A - A') c = qG A c - qG A' c := by
  simp only [qG, Matrix.sub_mul, Matrix.trace_sub, map_sub, mul_sub]

theorem trace_rat {ρ : ℕ} (M : Matrix (Fin ρ) (Fin ρ) D.host.E) : (rat M : Mx D ρ ρ).trace = incA D M.trace := by
  simp only [Matrix.trace, Matrix.diag, rat, Matrix.map_apply, map_sum]

theorem qG_rat {ρ : ℕ} (M C : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    qG (rat M) (rat C) = algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E (M * C).trace) := by
  rw [qG, ← rat_mul, trace_rat, trace_incA_eq, map_mul]

theorem map_cA_rat {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E) : (rat N).map (cA D) = rat (N.map star) := by
  funext i j; exact GlobalTheory.DualPairCheck.cA_incA _

def gramE (T : HSp D) {ρ : ℕ} (X : Matrix (Fin T.rank) (Fin ρ) D.host.E) : Matrix (Fin ρ) (Fin ρ) D.host.E :=
  (-D.host.xi0) • (Xᴴ * (T.gram * X))ᵀ

theorem gramSkew_rat (T : HSp D) {ρ : ℕ} (X : Matrix (Fin T.rank) (Fin ρ) D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T (rat X) = rat (gramE T X) := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, ← rat_conjTranspose, gA, ← rat_mul, ← rat_mul, ← map_neg (incA D), gramE, rat_smul]
  rfl

theorem gramE_skew (T : HSp D) {ρ : ℕ} (X : Matrix (Fin T.rank) (Fin ρ) D.host.E) :
    ((gramE T X).map star)ᴴ = -((gramE T X).map star) := by
  have hK : (Xᴴ * (T.gram * X))ᴴ = Xᴴ * (T.gram * X) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, gram_conjTranspose, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  funext i j
  have h := congrFun (congrFun hK i) j
  rw [Matrix.conjTranspose_apply] at h
  simp only [gramE, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.neg_apply, Matrix.smul_apply,
    Matrix.transpose_apply, smul_eq_mul, star_star, star_mul', star_neg, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, h]
  ring

theorem central : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.CentralTerms D := by
  intro D
  have h1 := GlobalTheory.T.mixed_model_central_terms_gram_identities D
  have hq : ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (c : skewA D ρ) (x : Mx D T.rank ρ),
      d.qS T c x = -qG ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D)) c.1 :=
    fun S S₀ T ρ d c x => (h1.1 S S₀ T ρ d).2 c x
  refine ⟨fun S S₀ T ρ d => ⟨(h1.1 S S₀ T ρ d).1, (h1.1 S S₀ T ρ d).2, fun ψ hψ => ⟨?_, ?_, ?_⟩⟩, h1.2⟩
  · intro x c c'
    rw [hq, hq, hq, AddSubgroup.coe_add, qG_add_right, neg_add, AddChar.map_add_eq_mul]
  · intro x hx c hc
    obtain ⟨X, rfl⟩ := mem_ratMx.1 hx
    obtain ⟨C, hC⟩ := mem_ratMx.1 hc
    rw [hq, gramSkew_rat, map_cA_rat, ← hC, qG_rat, ← map_neg]
    exact hψ.1.2.2.1 _
  · intro x hx x' hx'
    obtain ⟨X, rfl⟩ := mem_ratMx.1 hx
    obtain ⟨X', rfl⟩ := mem_ratMx.1 hx'
    constructor
    · intro h
      have hM := GlobalTheory.T.skewHermitian_tracePairing_standardCharacter_perfect D ψ hψ ρ ((gramE T X).map star - (gramE T X').map star)
        (by rw [Matrix.conjTranspose_sub, gramE_skew, gramE_skew, neg_sub, neg_sub_neg]) (fun c => by
          rw [rat_sub, ← map_cA_rat, ← map_cA_rat, ← gramSkew_rat, ← gramSkew_rat]
          change ψ (qG _ c.1) = 1
          have eA : qG ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T (rat X)).map (cA D)) c.1 = -d.qS T c (rat X) := by
            rw [hq S S₀ T ρ d, neg_neg]
          have eA' : qG ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T (rat X')).map (cA D)) c.1 = -d.qS T c (rat X') := by
            rw [hq S S₀ T ρ d, neg_neg]
          rw [qG_sub_left, eA, eA', sub_eq_add_neg, neg_neg, AddChar.map_add_eq_mul, ← h c, ← AddChar.map_add_eq_mul,
            neg_add_cancel, AddChar.map_zero_eq_one])
      rw [sub_eq_zero] at hM
      rw [gramSkew_rat, gramSkew_rat, Matrix.map_injective star_injective hM]
    · intro h c
      rw [hq, hq, h]

end GlobalTheory.CentralGram
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PoincareSeriesCompactSupportThetaLawStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareSeries_compactSupport_thetaLaw : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (h : WO A T → ℂ), Continuous h → HasCompactSupport h → (∀ u, {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | h (ratW T A γ + u) ≠ 0}.Finite) ∧ Continuous (fun u => ∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) u) * h (ratW T A γ + u)) ∧ ∀ (γ₀ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), (∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) (ratW T A γ₀ + u)) * h (ratW T A γ + (ratW T A γ₀ + u))) = ψ (-(symplOH A T (ratW T A γ₀) u)) * ∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) u) * h (ratW T A γ + u) := by
  first | exact @GlobalTheory.PoincareLaw.poincare_law | exact GlobalTheory.PoincareLaw.poincare_law | (intros; apply GlobalTheory.PoincareLaw.poincare_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceBasisGramIntegralInvertiblStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLatticeAtPlace_basis_gram_integral_invertible : ∀ (D : D7) (S : HSp D) (v : Pl D) (ε : AE D) (Λ : AddSubgroup (Fin S.rank → AE D)) (β β' : Matrix (Fin S.rank) (Fin S.rank) (AE D)), ε * ε = ε → cA D ε = ε → ε ∈ intAt D (· = v) → (∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) → IsSDAt S v Λ → (∀ i j, β i j ∈ idAt D (· = v)) → (∀ i j, β' i j ∈ idAt D (· = v)) → β * β' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → β' * β = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) → (∀ y : Fin S.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) → (y ∈ Λ ↔ ∀ i, (β' *ᵥ y) i ∈ intAt D (· = v))) → (∀ i j, (adj β * (gA S * β)) i j ∈ intAt D (· = v)) ∧ (∀ i j, cA D ((adj β * (gA S * β)) i j) = (adj β * (gA S * β)) j i) ∧ ∃ H' : Matrix (Fin S.rank) (Fin S.rank) (AE D), (∀ i j, H' i j ∈ intAt D (· = v)) ∧ adj β * (gA S * β) * H' = ε • (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
  first | exact @GlobalTheory.IwaPlace.GramBasis.gram_basis | exact GlobalTheory.IwaPlace.GramBasis.gram_basis | (intros; apply GlobalTheory.IwaPlace.GramBasis.gram_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SizeInequalitiesNoLevelPrimeColumnNormParametersStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizeInequalitiesNoLevelPrime_columnNormParameters : ∀ (D : D7) (L : SizeData₂ D) (CY : ℝ), HtRowsS L CY → ∀ (u : D.what₂.Word), SizeRowsS CY (numDatumOfParameters D L) (codeRec L u) := by
  first | exact @GlobalTheory.CoreHt.SizeRowsRec.sizeRowsS_numRec | exact GlobalTheory.CoreHt.SizeRowsRec.sizeRowsS_numRec | (intros; apply GlobalTheory.CoreHt.SizeRowsRec.sizeRowsS_numRec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLocalComponentsOneMulInvStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.LocOm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLocalComponents_one_mul_inv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (V : HSp D) (Z : Type) [Fintype Z] [DecidableEq Z] (F : Frame k V.rank Z), p.IsLoc F 1 1 ∧ (∀ (g g' : GA D V) (gk gk' : GL Z k), p.IsLoc F g gk → p.IsLoc F g' gk' → p.IsLoc F (g * g') (gk * gk')) ∧ ∀ (g : GA D V) (gk : GL Z k), p.IsLoc F g gk → p.IsLoc F g⁻¹ gk⁻¹ := by
  first | exact @GlobalTheory.LocOm.isLoc_one_mul_inv | exact GlobalTheory.LocOm.isLoc_one_mul_inv | (intros; apply GlobalTheory.LocOm.isLoc_one_mul_inv <;> assumption)
end

