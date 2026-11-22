import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingFormsLat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0023
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0020
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0035
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0118
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0121
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero
import Formalism.GL3MeanSquares.HookFormulaTorsion.Bundle0004
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaMovedCosetIndicatorVacuumShape
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0119
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFormsOfToH
section
noncomputable section

namespace GlobalTheory.PeriodOnStep

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.PeriodClassSum
open scoped Matrix ComplexOrder

theorem wForm_sum {C ι κ : Type} [Fintype C] [Fintype ι] [Fintype κ] (w : C → ℕ) (G : Matrix ι ι ℂ) (u : κ → C → ι → ℂ)
    (a b : κ → ℂ) : star a ⬝ᵥ (Matrix.of fun i j => wForm w G (u i) (u j)) *ᵥ b = wForm w G (∑ i, a i • u i) (∑ i, b i • u i) := by
  rw [dotProduct]
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
  simp only [wForm, Finset.sum_apply, Pi.smul_apply, star_sum, star_smul, sum_dotProduct, smul_dotProduct,
    Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
    Pi.star_apply]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => by ring

section Metric

variable {K : Type} [Field K] [NumberField K] [StarRing K]

omit [NumberField K] in

theorem map_pair {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] (b : Basis ι K V) (p : V →ₗ⋆[K] V →ₗ[K] K)
    (φ : K →+* ℂ) (x y : V) (hx : ∀ i, b.repr x i ∈ cmMax K) :
    φ (p x y) = star (fun i => φ (b.repr x i)) ⬝ᵥ (Matrix.of fun i j => p (b i) (b j)).map φ *ᵥ fun i => φ (b.repr y i) := by
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_mul, dotProduct,
    Matrix.mulVec, Matrix.map_apply, Matrix.of_apply, Finset.mul_sum, RingHom.id_apply, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply, hx i φ, starRingEnd_apply]
  ring

variable (S : CSD K) (v : InfinitePlace K)

def coAt (f : S.Cl → S.V) : S.Cl → S.ιV → ℂ := fun c i => v.embedding (S.bV.repr (f c) i)

theorem coAt_sum (x : S.Forms) :
    coAt S v (x : S.Cl → S.V) = ∑ i, v.embedding (S.basis.repr x i) • coAt S v (S.basis i : S.Cl → S.V) := by
  funext c k
  conv_lhs => rw [← S.basis.sum_repr x]
  simp only [coAt, AddSubmonoidClass.coe_finset_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, map_sum,
    map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul, smul_eq_mul, map_mul]

theorem coAt_indep : LinearIndependent ℂ fun i => fun p : S.Cl × S.ιV => coAt S v (S.basis i : S.Cl → S.V) p.1 p.2 := by
  letI : Algebra K ℂ := v.embedding.toAlgebra
  let f : S.Forms →ₗ[K] (S.Cl × S.ιV → K) := LinearMap.pi fun p =>
    S.bV.coord p.2 ∘ₗ LinearMap.proj p.1 ∘ₗ S.Forms.subtype
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro φ hφ
    apply Subtype.ext
    funext c
    exact S.bV.forall_coord_eq_zero_iff.1 fun k => congrFun hφ (c, k)
  exact (linearIndependent_algebraMap_comp_iff (S := ℂ)).2 (S.basis.linearIndependent.map' f hf)

theorem H_map (hb : S.HasRatBasis) : S.H.map v.embedding = Matrix.of fun i j =>
    wForm S.wt (S.gramV.map v.embedding) (coAt S v (S.basis i : S.Cl → S.V)) (coAt S v (S.basis j : S.Cl → S.V)) := by
  ext i j
  simp only [Matrix.map_apply, CSD.H, Matrix.of_apply, CSD.csum, wForm, map_sum, map_mul, map_inv₀, map_natCast]
  exact Finset.sum_congr rfl fun c _ => congrArg _ (map_pair S.bV S.pair v.embedding _ _ (S.basis_rat hb i c))

theorem H_posDef (hb : S.HasRatBasis) (hG : (S.gramV.map v.embedding).PosDef) : (S.H.map v.embedding).PosDef := by
  rw [H_map S v hb]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun a ha => ?_
  · ext i j
    rw [Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.of_apply]
    exact wForm_conj _ hG.1 _ _
  · rw [wForm_sum]
    refine lt_of_le_of_ne (wForm_nonneg _ hG.posSemidef _) fun h0 => ha ?_
    have h1 := wForm_eq_zero _ S.wt_pos hG h0.symm
    funext i
    refine Fintype.linearIndependent_iff.1 (coAt_indep S v) a ?_ i
    funext p
    simpa using congrFun (congrFun h1 p.1) p.2

theorem normAt_sq (hb : S.HasRatBasis) (hG : (S.gramV.map v.embedding).PosDef) (x : S.Forms) :
    ((Formalism.HermitianLatticesTheory.normAt S.basis (stdFrame S.H) v x ^ 2 : ℝ) : ℂ) =
      wForm S.wt (S.gramV.map v.embedding) (coAt S v (x : S.Cl → S.V)) (coAt S v (x : S.Cl → S.V)) := by
  have hm := (frameOfSpec _ _ (H_posDef S v hb hG)).2
  have h1 := wForm_sum S.wt (S.gramV.map v.embedding) (fun i => coAt S v (S.basis i : S.Cl → S.V))
    (Formalism.HermitianLatticesTheory.vecAt S.basis v x) (Formalism.HermitianLatticesTheory.vecAt S.basis v x)
  rw [← H_map S v hb, ← hm, metOf, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec] at h1
  rw [coAt_sum S v x]
  refine Eq.trans ?_ h1
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.ofReal_pow, ← Complex.conj_mul']
  rfl

variable (T : GSD K) (h : T.Ok) (hr : ∀ (g : T.G) i j, T.bV.repr (T.ρ g (T.bV j)) i ∈ cmMax K)

include hr in

theorem isFormsOf_toH (hG : ∀ v : InfinitePlace K, (T.gramV.map v.embedding).PosDef) (N : Submodule (𝓞 K) T.EqFun) :
    IsFormsOf T h N (T.toH h N) (LinearEquiv.refl _ _) := by
  refine ⟨fun _ => Iff.rfl, fun v (x : T.EqFun) => ?_⟩
  exact (normAt_sq (T.toCSD h) v (FormsDescent.hasRatBasis_of_act _ fun c γ => hr γ.1) (hG v) (T.res h x)).trans
    (ipAt_eq T h v x x).symm

include h hr in

theorem pairAt_rho (g : T.G) (x : T.V) : T.pairAt v (T.ρ g x) (T.ρ g x) = T.pairAt v x x := by
  let u : T.ιV → Unit → T.ιV → ℂ := fun k _ i => v.embedding (T.bV.repr (T.ρ g (T.bV k)) i)
  have h1 := wForm_sum (fun _ => 1) (T.gramV.map v.embedding) u (fun i => v.embedding (T.bV.repr x i))
    (fun i => v.embedding (T.bV.repr x i))
  have e1 : (Matrix.of fun i j => wForm (fun _ => 1) (T.gramV.map v.embedding) (u i) (u j)) = T.gramV.map v.embedding := by
    ext i j
    simp only [Matrix.of_apply, wForm, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, inv_one, one_mul]
    refine (map_pair T.bV T.pair v.embedding _ _ fun k => hr g k i).symm.trans ?_
    rw [h.inv]
    rfl
  have e2 : (∑ i, v.embedding (T.bV.repr x i) • u i) = fun _ i => v.embedding (T.bV.repr (T.ρ g x) i) := by
    funext c k
    conv_rhs => rw [← T.bV.sum_repr x]
    simp only [u, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul,
      smul_eq_mul, map_mul]
  rw [e1, e2] at h1
  rw [pairAt_eq, pairAt_eq, h1]
  simp only [wForm, Finset.univ_unique, Finset.sum_singleton, Nat.cast_one, inv_one, one_mul]

include hr in

theorem ipAt_sec (s : T.Sec) (φ : T.EqFun) : T.ipAt h v φ φ = letI := h.fintypeCl
    ∑ c, ((Nat.card (MulAction.stabilizer T.G (s.rep c)) : ℕ) : ℂ)⁻¹ *
      T.pairAt v ((φ : T.D → T.V) (s.rep c)) ((φ : T.D → T.V) (s.rep c)) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := T.outSec.exists_smul s c
  rw [T.wt_eq, ← hg, T.card_stab_smul, φ.2, pairAt_rho v T h hr]

end Metric

end GlobalTheory.PeriodOnStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentMeasureNormLeOneIffLatticeIntegral
section
open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate

noncomputable section
namespace GlobalTheory.MomN.Bridge

variable {g : ℕ}

theorem im_hf_int (S : Setup g) (hOk : S.Ok) (x y : Fin g → ℂ) (hx : x ∈ S.La) (hy : y ∈ S.La) :
    ∃ z : ℤ, (hf S.Hm x y).im = z := by
  obtain ⟨hdp, -, -, -, -, -, hbeta, -⟩ := hOk
  obtain ⟨u, v, huv⟩ := hbeta x hx y hy
  have h := congrArg Complex.im huv
  simp [beta, w0, rtd, Complex.mul_im] at h
  have hd : (0 : ℝ) < Real.sqrt S.d := Real.sqrt_pos.2 (by exact_mod_cast hdp.pos)
  refine ⟨v, ?_⟩
  field_simp at h
  nlinarith [h]

theorem hf_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (s : ℕ) (x t : Fin g → ℂ) :
    hf Hm ((s : ℂ) • x) t = hf Hm x ((s : ℂ) • t) := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hf_zero_right (Hm : Matrix (Fin g) (Fin g) ℂ) (x : Fin g → ℂ) : hf Hm x 0 = 0 := by
  simp [hf]

theorem opW_zero (d : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (G : (Fin g → ℂ) → ℂ) : opW d Hm 0 G = G := by
  funext z
  simp [opW, opU, beta, hf]

variable {q : ℕ} [Fact q.Prime]

theorem lamA_eq (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z) (x : ℂ) (hx : x ∈ Qbar) :
    lamA lam x = ι x := by
  unfold lamA
  rw [dif_pos hx, ← hι ⟨x, hx⟩]

theorem natCast_mem_Qbar (s : ℕ) : (s : ℂ) ∈ Qbar := (algebraicClosure ℚ ℂ).natCast_mem s

theorem lamA_nat (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z) (s : ℕ) :
    lamA lam (s : ℂ) = (s : ℂ_[q]) := by
  rw [lamA_eq ι lam hι _ (natCast_mem_Qbar s), map_natCast]

end GlobalTheory.MomN.Bridge

namespace GlobalTheory.MomN.Bridge
variable {g : ℕ} {q : ℕ} [Fact q.Prime]

theorem jet_trivialTorsion_eq_latticeMomentIntegral (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z)
    (δ₀ : ℂ) (Ω : ℂ_[q]) (S : Setup g) (hOk : S.Ok) {r : ℕ} (b : Fin r → Fin g → ℂ) (hbLa : ∀ i, b i ∈ S.La)
    (t : Fin g → ℂ) (ht : S.PrimeTo q t) (G : (Fin g → ℂ) → ℂ) (μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q])
    (hM : MomentProperty lam Ω δ₀ S b (fun _ : Fin 1 => t) μ G)
    (k : ℕ) (ys : Fin k → Fin g → ℂ) (hys : ∀ j, ys j ∈ S.La) (f : C(Fin r → ℤ_[q], ℂ_[q]))
    (hf' : ∀ a, f a = ∏ j, pairD lam Ω S.d S.Hm b (ys j) a) :
    ι (iteratedFDeriv ℂ k G 0 fun j => δ₀⁻¹ • ys j) = μ f := by
  obtain ⟨s, hs0, -, hst⟩ := ht
  have hid : IsIdem lam S.d 0 (s : ℂ) := by
    refine ⟨⟨s, 0, by simp⟩, ?_, ?_⟩
    · rw [lamA_nat ι lam hι]
      simp only [CharP.cast_eq_zero, neg_zero, zpow_zero]
      rw [← Nat.cast_pred hs0]
      exact IsUltrametricDist.norm_natCast_le_one ℂ_[q] _
    · rw [map_natCast, lamA_nat ι lam hι]
      simpa using IsUltrametricDist.norm_natCast_le_one ℂ_[q] s
  have hint : ∀ (l : Fin 1) (i : Fin r), ∃ z : ℤ, (hf S.Hm ((s : ℂ) • b i) t).im = z := by
    intro _ i
    rw [hf_smul_left]
    exact im_hf_int S hOk _ _ (hbLa i) hst
  let y0 : Fin r → Fin (q ^ 0) := fun _ => ⟨0, by simp⟩
  have hlift : liftY q 0 (s : ℂ) b y0 = 0 := by simp [liftY, y0]
  have hdir : ∀ j, S.AlgDir (ys j) := by
    intro j
    refine ⟨1, fun _ => 1, fun _ => ys j, fun _ => (algebraicClosure ℚ ℂ).one_mem, fun _ => hys j, by simp⟩
  have hf2 : ∀ a, f a = lamA lam (kap S.Hm (vecA 0 b a) (liftY q 0 (s : ℂ) b y0)) *
      ∏ j, pairD lam Ω S.d S.Hm b (ys j) a := by
    intro a
    rw [hlift, hf' a]
    have : kap S.Hm (vecA (q := q) 0 b a) 0 = ((1 : ℕ) : ℂ) := by simp [kap, hf_zero_right]
    rw [this, lamA_nat ι lam hι]; simp
  obtain ⟨hQ, heq⟩ := hM 0 0 (s : ℂ) hid le_rfl hint y0 k ys hdir f hf2
  rw [hlift, opW_zero] at hQ heq
  rw [← heq, lamA_eq ι lam hι _ hQ]
  rfl

end GlobalTheory.MomN.Bridge

namespace GlobalTheory.MomN.Bridge
variable {g : ℕ} {q : ℕ} [Fact q.Prime]

theorem pairD_dual (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z) (Ω : ℂ_[q])
    (S : Setup g) {r : ℕ} (b : Fin r → Fin g → ℂ) (s' : ℕ) (c : Fin r → Fin g → ℂ)
    (hcb : ∀ i j, beta S.d S.Hm (c j) (b i) = if i = j then (s' : ℂ) else 0) (j : Fin r) (a : Fin r → ℤ_[q]) :
    pairD lam Ω S.d S.Hm b (c j) a = Ω⁻¹ * ((s' : ℂ_[q]) * zc (a j)) := by
  unfold pairD
  congr 1
  have : ∀ i, zc (a i) * lamA lam (beta S.d S.Hm (c j) (b i)) = if i = j then (s' : ℂ_[q]) * zc (a j) else 0 := by
    intro i
    rw [hcb]
    split_ifs with h
    · subst h; rw [lamA_nat ι lam hι]; ring
    · rw [show (0 : ℂ) = ((0 : ℕ) : ℂ) by simp, lamA_nat ι lam hι]; simp
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_ite_eq']
  simp

theorem isMom_dual (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (hι : ∀ z : Qbar, ι (z : ℂ) = lam z)
    (δ₀ : ℂ) (hδ : δ₀ ≠ 0) (Ω : ℂ_[q]) (hΩ : Ω ≠ 0) (S : Setup g) (hOk : S.Ok) {r : ℕ} (b : Fin r → Fin g → ℂ)
    (hbLa : ∀ i, b i ∈ S.La) (t : Fin g → ℂ) (ht : S.PrimeTo q t) (G : (Fin g → ℂ) → ℂ)
    (μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]) (hM : MomentProperty lam Ω δ₀ S b (fun _ : Fin 1 => t) μ G)
    (s' : ℕ) (hs' : s' ≠ 0) (c : Fin r → Fin g → ℂ) (hcLa : ∀ j, c j ∈ S.La)
    (hcb : ∀ i j, beta S.d S.Hm (c j) (b i) = if i = j then (s' : ℂ) else 0) :
    IsMom ι (fun j => (ι.symm (Ω / ι δ₀) / (s' : ℂ)) • c j) G μ := by
  intro k j f hf
  have hs'q : (s' : ℂ_[q]) ≠ 0 := Nat.cast_ne_zero.2 hs'
  have hιδ : ι δ₀ ≠ 0 := by simpa using hδ
  let f' : C(Fin r → ℤ_[q], ℂ_[q]) := ((Ω⁻¹ * s') ^ k) • f
  have hf' : ∀ a, f' a = ∏ l, pairD lam Ω S.d S.Hm b (c (j l)) a := by
    intro a
    simp only [f', ContinuousMap.smul_apply, smul_eq_mul, hf a, pairD_dual ι lam hι Ω S b s' c hcb,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
    rw [mul_assoc]; rfl
  have hA := jet_trivialTorsion_eq_latticeMomentIntegral ι lam hι δ₀ Ω S hOk b hbLa t ht G μ hM k (fun l => c (j l)) (fun l => hcLa _) f' hf'
  have e1 : (iteratedFDeriv ℂ k G 0 fun l => δ₀⁻¹ • c (j l)) = δ₀⁻¹ ^ k • iteratedFDeriv ℂ k G 0 fun l => c (j l) := by
    rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have e2 : (iteratedFDeriv ℂ k G 0 fun l => (ι.symm (Ω / ι δ₀) / (s' : ℂ)) • c (j l)) =
      (ι.symm (Ω / ι δ₀) / (s' : ℂ)) ^ k • iteratedFDeriv ℂ k G 0 fun l => c (j l) := by
    rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [e1, smul_eq_mul, map_mul, map_pow, map_inv₀] at hA
  simp only [f', ContinuousLinearMap.map_smul, smul_eq_mul] at hA
  rw [e2, smul_eq_mul, map_mul, map_pow, map_div₀, RingEquiv.apply_symm_apply, map_natCast]
  set J := ι (iteratedFDeriv ℂ k G 0 fun l => c (j l))
  have hJ : J = (ι δ₀) ^ k * ((Ω⁻¹ * s') ^ k * μ f) := by
    rw [← hA, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hιδ, one_pow, one_mul]
  rw [hJ, ← mul_assoc, ← mul_assoc, ← mul_pow, ← mul_pow]
  have h1 : Ω / ι δ₀ / (s' : ℂ_[q]) * ι δ₀ * (Ω⁻¹ * s') = 1 := by field_simp
  rw [h1, one_pow, one_mul]

end GlobalTheory.MomN.Bridge

namespace GlobalTheory.MomN.Bridge
variable {q : ℕ} [Fact q.Prime]

theorem exists_zc_inv (s : ℕ) (hs : Nat.Coprime s q) : ∃ u : ℤ_[q], zc u = ((s : ℂ_[q]))⁻¹ := by
  have hn : ‖(s : ℤ_[q])‖ = 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_natCast, Padic.norm_natCast_eq_one_iff]; exact hs.symm
  refine ⟨(s : ℤ_[q]).inv, ?_⟩
  have hm : (s : ℤ_[q]) * (s : ℤ_[q]).inv = 1 := PadicInt.mul_inv hn
  have h2 : zc (s : ℤ_[q]) * zc (s : ℤ_[q]).inv = 1 := by
    simp only [zc]
    rw [← map_mul, ← PadicInt.coe_mul, hm, PadicInt.coe_one, map_one]
  rw [show zc (s : ℤ_[q]) = (s : ℂ_[q]) by simp [zc]] at h2
  exact eq_inv_of_mul_eq_one_right h2

end GlobalTheory.MomN.Bridge

namespace GlobalTheory.MomN

open Bridge in

theorem norm_le_one_iff_latInt : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (lam : Qbar →+* ℂ_[q]) (δ₀ : ℂ) (Ω : ℂ_[q])
    (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (t : Fin g → ℂ) (G : (Fin g → ℂ) → ℂ)
    (μ : C(Fin r → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]), (∀ z : Qbar, ι (z : ℂ) = lam z) → δ₀ ≠ 0 → ‖Ω‖ = 1 → S.Ok →
    GlobalTheory.MomOne.Split S.d q → S.NNBasis q b → S.PrimeTo q t → ContDiff ℂ ⊤ G →
    MomentProperty lam Ω δ₀ S b (fun _ : Fin 1 => t) μ G → (‖μ‖ ≤ 1 ↔ LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup G) := by
  intro q _ ι lam δ₀ Ω g S r b t G μ hι hδ hΩ hOk hsplit hb ht _ hM
  have hΩ0 : Ω ≠ 0 := by rintro rfl; simp at hΩ
  obtain ⟨s', c, hs'q, hcLa, hcb, hsp⟩ := GlobalTheory.T.exists_dualBasis_of_unimodular_lattice_at_prime q g S r b hOk hb
  have hs'0 : s' ≠ 0 := by
    rintro rfl
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.coprime_zero_left q |>.1 hs'q)
  have hmom := isMom_dual ι lam hι δ₀ hδ Ω hΩ0 S hOk b hb.1 t ht G μ hM s' hs'0 c hcLa hcb
  obtain ⟨hdp, hd16, -, -, -, -, hbeta, -⟩ := hOk
  constructor
  · intro hμ
    have hM' : MomInt ι (fun j => ι.symm (Ω / ι δ₀) • ((s' : ℂ)⁻¹ • c j)) G := by
      refine ⟨μ, hμ, ?_⟩
      have e : (fun j => ι.symm (Ω / ι δ₀) • ((s' : ℂ)⁻¹ • c j)) =
          fun j => (ι.symm (Ω / ι δ₀) / (s' : ℂ)) • c j := by
        funext j; simp only [smul_smul, div_eq_mul_inv]
      rw [e]; exact hmom
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_of_span_imagQuadratic q ι (Fin g → ℂ) S.d (Ω / ι δ₀) S.La.toAddSubgroup (Fin r) (fun j => (s' : ℂ)⁻¹ • c j) G
      hdp hd16 hsplit ?_ hM'
    intro x hx
    rw [Submodule.mem_toAddSubgroup] at hx
    refine ⟨1, Nat.coprime_one_left q, fun i => beta S.d S.Hm x (b i), fun i => ?_, ?_⟩
    · obtain ⟨u, v, huv⟩ := hbeta x hx (b i) (hb.1 i)
      exact ⟨u, v, huv⟩
    · have hs'C : (s' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hs'0
      rw [Nat.cast_one, one_smul]
      calc x = (s' : ℂ)⁻¹ • ((s' : ℂ) • x) := by rw [smul_smul, inv_mul_cancel₀ hs'C, one_smul]
        _ = ∑ i, beta S.d S.Hm x (b i) • (s' : ℂ)⁻¹ • c i := by
          rw [hsp x hx, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, smul_smul, mul_comm]
  · intro hL
    have h1 := hL (Fin r) c (fun j => by simpa using hcLa j)
    obtain ⟨u, hu⟩ := exists_zc_inv s' hs'q
    have h2 := GlobalTheory.MomN.momInt_push q ι (Fin g → ℂ) (Fin r) (Fin r) (fun i => ι.symm (Ω / ι δ₀) • c i)
      (fun i => (ι.symm (Ω / ι δ₀) / (s' : ℂ)) • c i) (fun i j => if i = j then (s' : ℂ)⁻¹ else 0)
      (fun i j => if i = j then u else 0) G ?_ ?_ h1
    · obtain ⟨μ', hμ', hmom'⟩ := h2
      have he := GlobalTheory.MomN.measure_eq_of_moments q (Fin r) μ μ'
        (fun k j f hf => by rw [← hmom k j f hf, ← hmom' k j f hf])
      rw [he]; exact hμ'
    · intro i j
      split_ifs
      · rw [map_inv₀, map_natCast, ← hu]; rfl
      · simp [GlobalTheory.MomOne.zc]
    · intro i
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
      simp only [if_true]
      rw [smul_smul, div_eq_mul_inv, mul_comm]

end GlobalTheory.MomN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaCharHalfPeriodEqZeroIffStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChar_half_period_eq_zero_iff_odd_add_odd_add : ∀ τ : UpperHalfPlane, ThetaConstantWeber.JacobiProduct τ → ∀ (m n : ℤ) (a b : Fin 2),
    JacobiThetaHalfCharacteristic.IsEvenChar a b →
    (JacobiThetaHalfCharacteristic.thetaChar a b (((m : ℂ) + (n : ℂ) * (τ : ℂ)) / 2) (τ : ℂ) = 0 ↔
      Odd (m + ((b : ℕ) : ℤ)) ∧ Odd (n + ((a : ℕ) : ℤ))) := by
  first | exact @GlobalTheory.Glob.ThetaParity.thetaChar_half_period_eq_zero_iff | exact GlobalTheory.Glob.ThetaParity.thetaChar_half_period_eq_zero_iff | (intros; apply GlobalTheory.Glob.ThetaParity.thetaChar_half_period_eq_zero_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaMovedCosetIndicatorVacuumShapeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_movedCosetIndicator_vacuum_shape : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c : ℕ), X.Ok → A.LaHyp a b S → A.AA ≠ ⊥ → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → ∃ n : ℕ, n ≠ 0 ∧ n ∣ (halfBO S (per A N N') c).toAddSubgroup.relIndex (per A N N').toAddSubgroup ∧ ∀ x ∈ divLat cA (homAt S N N'), ∀ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') → ∀ R : Finset (HomE X.E a b), IsReps (per A N N').toAddSubgroup (halfBO S (per A N N') c).toAddSubgroup R → A.thInd S N N' c x = fun z => (n : ℂ)⁻¹ * Wx A (-t) (fun z => ∑ y ∈ R, Wx A y (A.e a b N N') z) z := by
  first | exact @GlobalTheory.MomT.ThShape.thInd_shape | exact GlobalTheory.MomT.ThShape.thInd_shape | (intros; apply GlobalTheory.MomT.ThShape.thInd_shape <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThinChoiceOfZeroDensityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thin_choice_of_zero_density : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → GlobalTheory.Mem.An.ZeroCount → Formalism.ZeroFreeDirichlet.ZFRDirichlet → ThinChoice := by
  first | exact @GlobalTheory.EX.thinChoice_of_explicit | exact GlobalTheory.EX.thinChoice_of_explicit | (intros; apply GlobalTheory.EX.thinChoice_of_explicit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwGoodOneSetDiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.EX.DQ NumberField IsDedekindDomain

namespace GlobalTheory.EX.DQ

set_option maxHeartbeats 2000000 in

theorem twGoodOne_setDiv (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    (N0 : D.ntw.Tw → ℕ) (S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b))
    (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k : ℕ) (p : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)
    (H : TwGoodOne D ⟨twEOf O.xd, N0, S⟩ i b Q k p) :
    TwGoodOne (setDiv D N h) ⟨twEOf (O.tr N h).xd, N0, S⟩ i b Q k p := by
  unfold TwGoodOne at H ⊢
  have e1 : AvRec (setDiv D N h) = AvRec D := rfl
  have e2 : twEps (setDiv D N h) i = twEps D i := rfl
  rw [e1, e2]
  unfold IntegralHeckeForms.GoodTw at H ⊢
  obtain ⟨h1, ⟨eB, h2, h3, h4⟩, h5, h6, h7, h8⟩ := H
  exact ⟨h1, ⟨eB, h2, h3, h4⟩, fun j hj c => ⟨(h5 j hj c).1, (h5 j hj c).2⟩, h6, h7, h8⟩

theorem qd_setDiv : ∀ (D : D7) (O : Obj D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ),
    QD D O → QD (setDiv D N h) (O.tr N h) := by
  rintro D O N h ⟨h1, ⟨hc, N0, S, hS⟩, h3⟩
  refine ⟨h1, ⟨hc, N0, S, fun w hw => ⟨(hS w hw).1, fun a ha => ?_⟩⟩, h3⟩
  exact twGoodOne_setDiv D O N h N0 S _ _ _ _ _ ((hS w hw).2 a ha)

end GlobalTheory.EX.DQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryGroupNegFormCompatibleStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_neg_form_compatible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J J' : Matrix (Fin M) (Fin M) E), J' = -J → ∃ φ : HA (AF F) σ J ≃ₜ* HA (AF F) σ J', (∀ h, HA.mat (AF F) σ J' (φ h) = HA.mat (AF F) σ J h) ∧ (∀ h, h ∈ HFinIn (AF F) σ J ↔ φ h ∈ HFinIn (AF F) σ J') ∧ ∀ (L : Set (Fin M → E)) h, h ∈ StabFin.SFin σ J L ↔ φ h ∈ StabFin.SFin σ J' L := by
  first | exact @GlobalTheory.unitary_neg_same | exact GlobalTheory.unitary_neg_same | (intros; apply GlobalTheory.unitary_neg_same <;> assumption)
end

