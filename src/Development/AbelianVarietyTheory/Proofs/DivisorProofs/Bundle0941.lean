import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0050
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PtCoeffSingleSubst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralIdelesEulerProduct
import Formalism.PairingDivisors.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorNegHermitianSpaceConjMonomial
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj

namespace GlobalTheory.FockConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem inv_neg_mat {k : Type} [Fintype k] [DecidableEq k] {R : Type} [CommRing R] (A : Matrix k k R) :
    (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · have e : ((-1 : Rˣ) • A) = -A := by simp
    rw [← e, Matrix.inv_smul' (A := A) (k := (-1 : Rˣ)) h]
    simp
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      apply h
      have : IsUnit ((-1 : R) ^ Fintype.card k) := (isUnit_neg_one (α := R)).pow _
      exact (IsUnit.mul_iff.1 hu).2
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem symplOH_negSp (S T : HSp D) (x y : WO S T) :
    symplOH (negSp S) T x y = -symplOH S T x y := by
  have h : hO (negSp S) T x y = -hO S T x y := by
    unfold hO
    rw [negSp_gram, inv_neg_mat]
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  unfold symplOH symplO
  rw [h, mul_neg, map_neg, mul_neg]

theorem star_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (a : AF D.host.F) :
    star (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ a]
  simp [Complex.star_def]

theorem heisO_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) (w₀ : WO S T)
    (g : WO S T → ℂ) :
    heisO ψ (negSp S) T w₀ (fun w => star (g w)) = fun w => star (heisO ψ S T w₀ g w) := by
  funext w
  unfold heisO
  rw [star_mul, symplOH_negSp, ← star_psi hψ]
  ring

theorem lineAt_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (y : Matrix (Fin m) (Fin n) ℂ) :
    lineAt θ τ (-y) = -(lineAt θ τ y) := by
  have h := GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ y
  refine GlobalTheory.RealLineAt.lineAt_unique D θ hθ m n τ (-y) _ _ (GlobalTheory.OrientedHeis.isLineAt_lineAt hθ τ (-y)) ?_
  refine ⟨h.1.neg, fun t => ?_, fun t τ' => ?_⟩
  · have h2 := h.2.1 t
    ext i j
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.map_apply, Matrix.zero_apply] at this
    simp only [Matrix.map_apply, Matrix.zero_apply, AddMonoidHom.neg_apply, Matrix.neg_apply, RingHom.map_neg, this,
      neg_zero]
  · have h3 := h.2.2 t τ'
    have e : compAt θ τ' ((-(lineAt θ τ y)) t) = -compAt θ τ' (lineAt θ τ y t) := by
      ext i j
      simp only [compAt, Matrix.map_apply, AddMonoidHom.neg_apply, Matrix.neg_apply, RingHom.map_neg]
    rw [e, h3]
    split_ifs <;> simp

end GlobalTheory.FockConj

namespace GlobalTheory.FockConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem dRho_neg {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (hs : Mx D m n → (Mx D m n → ℂ) → (Mx D m n → ℂ))
    (τ : D.what₂.Tau) (y : Matrix (Fin m) (Fin n) ℂ) (h : Mx D m n → ℂ) :
    Formalism.IndefR.Datum.dRho hs θ τ (-y) h = -Formalism.IndefR.Datum.dRho hs θ τ y h := by
  funext x
  have e : (fun t : ℝ => hs (lineAt θ τ (-y) t) h x) = fun t => (fun s : ℝ => hs (lineAt θ τ y s) h x) (-t) := by
    funext t
    rw [lineAt_neg hθ, AddMonoidHom.neg_apply, ← map_neg]
  simp only [Formalism.IndefR.Datum.dRho, Pi.neg_apply]
  rw [e]
  exact (deriv_comp_neg (f := fun s : ℝ => hs (lineAt θ τ y s) h x) (x := 0)).trans (by rw [neg_zero])

theorem dRho_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (θ : InfFam D) (S T : HSp D)
    (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ (negSp S) T) θ τ z (fun w => star (g w)) = fun w => star (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g w) := by
  funext x
  simp only [Formalism.IndefR.Datum.dRho]
  have e : (fun t : ℝ => heisO ψ (negSp S) T (lineAt θ τ z t) (fun w => star (g w)) x) =
      fun t => star (heisO ψ S T (lineAt θ τ z t) g x) := by
    funext t
    rw [heisO_negSp_star hψ]
  rw [e, deriv.star]

theorem cplxO_neg {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ)
    (z : Matrix (Fin m) (Fin n) ℂ) : cplxO (-sS) sT z = -cplxO sS sT z := by
  unfold cplxO
  rw [Matrix.mul_neg, smul_neg]

theorem aPlus_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (τ : D.what₂.Tau) (sS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (u : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    aPlus (heisO ψ (negSp S) T) θ τ (cplxO (-sS) sT) u (fun w => star (g w)) =
      fun w => star (aPlus (heisO ψ S T) θ τ (cplxO sS sT) u g w) := by
  funext w
  simp only [aPlus, crea, cplxO_neg, dRho_neg hθ, dRho_negSp_star hψ]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply,
    smul_eq_mul, star_mul, star_sub, Complex.star_def, Complex.conj_I, map_inv₀, Complex.conj_ofReal]
  ring

theorem foldr_negSp_star {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) {θ : InfFam D} (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (L : List (FVar D T.rank S.rank)) (g : WO S T → ℂ) :
    L.foldr (fun i h => aPlusAll (heisO ψ (negSp S) T) θ (fun τ => cplxO (-sS τ) (sT τ)) BS BT i h)
        (fun w => star (g w)) =
      fun w => star (L.foldr (fun i h => aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i h) g w) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    exact aPlus_negSp_star hψ hθ S T a.1 (sS a.1) (sT a.1) _ _

end GlobalTheory.FockConj

namespace GlobalTheory.FockConj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorO_negSp_monomial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO (negSp S) T → ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (k : FVar D T.rank S.rank →₀ ℕ) (x : WO S T), pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT f (MvPolynomial.monomial k 1) x = starRingEnd ℂ (pureTensorO ψ θ S T sS sT BS BT (fun w => starRingEnd ℂ (f w)) (MvPolynomial.monomial k 1) x) := by
  intro D ψ θ S T sS sT BS BT f hψ hθ k x
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have h1 : pureTensorO ψ θ (negSp S) T (fun τ => -sS τ) sT BS BT f (MvPolynomial.monomial k 1) =
      opPow (aPlusAll (heisO ψ (negSp S) T) θ (fun τ => cplxO (-sS τ) (sT τ)) BS BT) k f := by
    have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
      (fun k => opPow (aPlusAll (heisO ψ (negSp S) T) θ (fun τ => cplxO (-sS τ) (sT τ)) BS BT) k f) k
    rwa [MvPolynomial.coe_basisMonomials] at this
  have h2 : pureTensorO ψ θ S T sS sT BS BT (fun w => starRingEnd ℂ (f w)) (MvPolynomial.monomial k 1) =
      opPow (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) k (fun w => starRingEnd ℂ (f w)) := by
    have := (MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ).constr_basis ℂ
      (fun k => opPow (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) k
        (fun w => starRingEnd ℂ (f w))) k
    rwa [MvPolynomial.coe_basisMonomials] at this
  rw [h1, h2, opPow, opPow]
  have hf : f = fun w => star (starRingEnd ℂ (f w)) := by
    funext w
    simp
  conv_lhs => rw [hf]
  rw [foldr_negSp_star hn hθ S T sS sT BS BT]
  rfl

end GlobalTheory.FockConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDetPowDepthLeOfIntegralLogHom
section
set_option autoImplicit false

noncomputable section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory.DepthMono

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def linSub {d d' : ℕ} (M : Matrix (Fin d') (Fin d) C) : Fin d' → MvPowerSeries (Fin d) C :=
  fun b => ∑ a, M b a • (X a : MvPowerSeries (Fin d) C)

theorem constantCoeff_linSub {d d' : ℕ} (M : Matrix (Fin d') (Fin d) C) (b : Fin d') :
    constantCoeff (linSub M b) = 0 := by
  simp [linSub]

theorem subst_expOf_hom {d d' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {M : Matrix (Fin d') (Fin d) C} (hφ : IsIntHom G G' φ M)
    (c : Fin d') : subst (expOf G) (φ c) = subst (linSub M) (expOf G' c) := by
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero (isExp_expOf G).1
  have hE' : HasSubst (expOf G') := hasSubst_of_constantCoeff_zero (isExp_expOf G').1
  have hφs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ.1
  have hL : HasSubst (linSub M) := hasSubst_of_constantCoeff_zero (constantCoeff_linSub M)
  have hlg' : HasSubst G'.lg := hasSubst_of_constantCoeff_zero G'.lg_const
  set ψ : Fin d' → MvPowerSeries (Fin d) C := fun c => subst (expOf G) (φ c) with hψ
  set ρ : Fin d' → MvPowerSeries (Fin d) C := fun c => subst (linSub M) (expOf G' c) with hρ
  have hψ0 : ∀ c, constantCoeff (ψ c) = 0 := fun c =>
    constantCoeff_subst_eq_zero hE (isExp_expOf G).1 (hφ.1 c)
  have hρ0 : ∀ c, constantCoeff (ρ c) = 0 := fun c =>
    constantCoeff_subst_eq_zero hL (constantCoeff_linSub M) ((isExp_expOf G').1 c)
  have hψs : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  have hρs : HasSubst ρ := hasSubst_of_constantCoeff_zero hρ0
  have key : ∀ b, subst ψ (G'.lg b) = subst ρ (G'.lg b) := by
    intro b
    have h1 : subst ψ (G'.lg b) = subst (expOf G) (subst φ (G'.lg b)) :=
      (subst_comp_subst_apply hφs hE (G'.lg b)).symm
    have h2 : subst ρ (G'.lg b) = subst (linSub M) (subst (expOf G') (G'.lg b)) :=
      (subst_comp_subst_apply hE' hL (G'.lg b)).symm
    rw [h1, h2, hφ.2.2, (isExp_expOf G').2, subst_sum_smul hE, subst_X hL]
    simp only [(isExp_expOf G).2, linSub]
  have inj : ∀ c, ψ c = subst (fun b => subst ψ (G'.lg b)) (expOf G' c) ∧
      ρ c = subst (fun b => subst ρ (G'.lg b)) (expOf G' c) := by
    intro c
    constructor
    · rw [← subst_comp_subst_apply hlg' hψs, subst_lg_expOf, subst_X hψs]
    · rw [← subst_comp_subst_apply hlg' hρs, subst_lg_expOf, subst_X hρs]
  show ψ c = ρ c
  rw [(inj c).1, (inj c).2, funext key]

theorem subst_exp_hom {τ : Type} {d d' : ℕ} {G : LogFGL v d} {G' : LogFGL v d'}
    {φ : Fin d' → MvPowerSeries (Fin d) C} {M : Matrix (Fin d') (Fin d) C} (hφ : IsIntHom G G' φ M)
    {L : Fin d → MvPowerSeries τ C} (hL0 : ∀ e, constantCoeff (L e) = 0) (c : Fin d') :
    subst (fun e => (subst L (expOf G e) : MvPowerSeries τ C)) (φ c) =
      (subst (fun b => ∑ a, M b a • L a) (expOf G' c) : MvPowerSeries τ C) := by
  have hE : HasSubst (expOf G) := hasSubst_of_constantCoeff_zero (isExp_expOf G).1
  have hM : HasSubst (linSub M) := hasSubst_of_constantCoeff_zero (constantCoeff_linSub M)
  have hL : HasSubst L := hasSubst_of_constantCoeff_zero hL0
  rw [← subst_comp_subst_apply hE hL, subst_expOf_hom hφ, subst_comp_subst_apply hM hL]
  congr 1
  funext b
  rw [linSub, subst_sum_smul hL]
  simp only [subst_X hL]

theorem detDepth_le_of_isIntHom : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)),
    ∀ (i d d' k : ℕ) (G : LogFGL v d) (G' : LogFGL v d') (φ : Fin d' → MvPowerSeries (Fin d) C)
      (M : Matrix (Fin d') (Fin d) C), IsIntHom G G' φ M → ∀ u : Fin i → Fin d → C,
      detDepth G u k ≤ detDepth G' (fun a => M.mulVec (u a)) k := by
  intro C _ _ v i d d' k G G' φ M hφ u
  have hX : ∀ b : Fin i, HasSubst
      (fun e : Fin d => (X ⟨b, e⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) := fun b =>
    hasSubst_of_constantCoeff_zero fun e => by simp
  let Φ : (Σ _ : Fin i, Fin d') → MvPowerSeries (Σ _ : Fin i, Fin d) C := fun x =>
    subst (fun e : Fin d => (X ⟨x.1, e⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (φ x.2)
  have hΦ : HasSubst Φ := hasSubst_of_constantCoeff_zero fun x =>
    constantCoeff_subst_eq_zero (hX x.1) (fun e => by simp) (hφ.1 x.2)
  have hΦi : ∀ x, MvIsInt v (Φ x) := fun x =>
    ptIntSer_subst (v := v) (hX x.1) (fun e => ptIntSer_X _) (hφ.2.1 x.2)
  have hL0 : ∀ (b : Fin i) (e : Fin d), constantCoeff
      (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) = 0 := fun b e => by simp
  have hA : HasSubst (expAlong (fun _ : Fin i => G) (fun _ => u)) :=
    hasSubst_of_constantCoeff_zero fun x =>
      constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (hL0 x.1)) (hL0 x.1)
        ((isExp_expOf G).1 x.2)
  have hcol : (fun x => subst (expAlong (fun _ : Fin i => G) (fun _ => u)) (Φ x)) =
      expAlong (fun _ : Fin i => G') (fun _ a => M.mulVec (u a)) := by
    funext x
    simp only [Φ]
    rw [subst_comp_subst_apply (hX x.1) hA]
    simp only [subst_X hA, expAlong]
    rw [subst_exp_hom hφ (hL0 x.1)]
    congr 1
    funext b
    simp only [Matrix.mulVec, dotProduct, Finset.smul_sum, Finset.sum_smul, smul_smul]
    exact Finset.sum_comm
  refine le_iInf fun f => iInf_le_of_le ⟨subst Φ f.1, ptIntSer_subst (v := v) hΦ hΦi f.2⟩ (le_of_eq ?_)
  simp only
  rw [subst_comp_subst_apply hΦ hA, hcol]

end GlobalTheory.DepthMono
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameSeriesExpSumOfActionLinearLogUnit
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dAct)

theorem frame_cc_ev {C : Type} [CommRing C] {d m n : ℕ} (a : Fin m → Pt C n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) {f : PS C m d} (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 := by
  have h0 : ∀ p : Fin m × Fin d, constantCoeff ((fun p : Fin m × Fin d => a p.1 p.2) p) = 0 := fun p => ha p.1 p.2
  unfold ev
  exact constantCoeff_subst_eq_zero (a := fun p : Fin m × Fin d => a p.1 p.2)
    (hasSubst_of_constantCoeff_zero h0) h0 hf

theorem frame_subst_ev {C : Type} [CommRing C] {d m n : ℕ} {σ : Type} (a : Fin m → Pt C n d)
    (ha : ∀ j i, constantCoeff (a j i) = 0) {t : Fin n × Fin d → MvPowerSeries σ C} (ht : HasSubst t)
    (f : PS C m d) :
    subst t (ev a f) = subst (fun p : Fin m × Fin d => subst t (a p.1 p.2)) f := by
  have h0 : ∀ p : Fin m × Fin d, constantCoeff ((fun p : Fin m × Fin d => a p.1 p.2) p) = 0 := fun p => ha p.1 p.2
  unfold ev
  exact subst_comp_subst_apply (a := fun p : Fin m × Fin d => a p.1 p.2) (hasSubst_of_constantCoeff_zero h0) ht f

theorem frame_cc_pt {C : Type} [CommRing C] {d n : ℕ} (b : Fin n) (j : Fin 1) (i : Fin d) :
    constantCoeff ((![pt C d b] : Fin 1 → Pt C n d) j i) = 0 := by
  simp [pt]

theorem frame_subst_ev_pt {C : Type} [CommRing C] {d n : ℕ} {σ : Type} (b : Fin n)
    {t : Fin n × Fin d → MvPowerSeries σ C} (ht : HasSubst t) (f : PS C 1 d) :
    subst t (ev ![pt C d b] f) = subst (fun p : Fin 1 × Fin d => t (b, p.2)) f := by
  rw [frame_subst_ev _ (frame_cc_pt b) ht]
  congr 1
  funext p
  simp only [Matrix.cons_val_fin_one, pt]
  exact subst_X ht _

theorem frame_exp_zero {C : Type} [CommRing C] [Algebra ℚ C] {σ : Type} :
    PowerSeries.subst (0 : MvPowerSeries σ C) (PowerSeries.exp C) = 1 := by
  classical
  unfold PowerSeries.subst
  have e : (fun _ : Unit => (0 : MvPowerSeries σ C)) = 0 := rfl
  rw [e, MvPowerSeries.subst_zero_eq_C_constantCoeff]
  ext x
  by_cases hx : x = 0
  · subst hx
    rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_C, if_pos rfl, MvPowerSeries.coeff_zero_eq_constantCoeff,
      map_one]
    exact PowerSeries.constantCoeff_exp (A := C)
  · rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_C, if_neg hx, MvPowerSeries.coeff_one, if_neg hx, map_zero]

theorem frameSt_of (hAct : ActSt) (hUnit : UnitSt) : FrameSt := by
  intro C _ _ v d R _ _ O _ _ B hB h hh w0 n
  have hc : constantCoeff h = 0 := GlobalTheory.GaugeBaseChange.const_of_axis hh.ax0
  have hact : ∀ i, constantCoeff (B.actK C w0 i) = 0 := fun i => by
    unfold FB.actK
    rw [constantCoeff_map, B.A.const, map_zero]
  have hpair : ∀ j i, constantCoeff
      ((![pt C d 0, comp1 (B.actK C w0) (pt C d 0)] : Fin 2 → Pt C 1 d) j i) = 0 := by
    intro j i
    fin_cases j
    · simp [pt]
    · exact frame_cc_ev _ (frame_cc_pt 0) (hact i)
  have hcL : constantCoeff (B.hL C h w0) = 0 := frame_cc_ev _ hpair hc
  have hS : constantCoeff (∑ b : Fin n, ev (n := n) ![pt C d b] (B.hL C h w0)) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => frame_cc_ev _ (frame_cc_pt b) hcL
  obtain ⟨-, -, -, hadd, hone, -⟩ := hUnit C v (Fin n × Fin d)
  refine ⟨hone _ hS, fun k => ?_, fun σ _ y hy => ?_⟩
  · unfold frameSer FB.expS
    induction k with
    | zero => rw [Nat.cast_zero, zero_smul, pow_zero, frame_exp_zero]
    | succ k ih =>
      rw [Nat.cast_succ, add_smul, one_smul, hadd _ _ _ hS, ih, pow_succ]
      rw [smul_eq_C_mul, map_mul, hS, mul_zero]
  · have ht : HasSubst (fun q : Fin n × Fin d => expPt (fglOf hB) (y q.1) q.2) :=
      hasSubst_of_constantCoeff_zero fun q => cc_expPt _ (hy q.1) q.2
    have key : subst (fun q : Fin n × Fin d => expPt (fglOf hB) (y q.1) q.2)
        (∑ b : Fin n, ev (n := n) ![pt C d b] (B.hL C h w0)) =
        ∑ j, pairSer (fglOf hB) h (y j) (mv (dAct C B w0) (y j)) := by
      rw [← coe_substAlgHom ht, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hs : HasSubst (fun p : Fin 1 × Fin d => expPt (fglOf hB) (y b) p.2) :=
        hasSubst_of_constantCoeff_zero fun q => cc_expPt _ (hy b) q.2
      rw [coe_substAlgHom, frame_subst_ev_pt b ht]
      unfold FB.hL pairSer
      rw [frame_subst_ev _ hpair hs, (hAct C v d R O B hB σ w0).1 (y b) (hy b)]
      congr 1
      funext ⟨j, i⟩
      fin_cases j
      · exact subst_X hs _
      · exact frame_subst_ev_pt 0 hs _
    rw [← key]
    unfold frameSer FB.expS PowerSeries.subst
    exact subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => hS) ht _

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalIdealFrobeniusPowers
section
open MeasureTheory Matrix GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace GlobalTheory.SmGL.CuspSpan

theorem blk_two_apply {α β n : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (c : α ⊕ β ≃ n) (s : α ⊕ β) : GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two c) (c s) = s.isRight := by
  rcases s with p | q
  · rw [← GlobalTheory.SmGL.two_false, GlobalTheory.SmGL.blk_apply]; rfl
  · rw [← GlobalTheory.SmGL.two_true, GlobalTheory.SmGL.blk_apply]; rfl

theorem mem_span_unip (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hπ : GlobalTheory.SmGL.IsCuspidal π) (a b : ℕ)
    (e : Fin N ≃ Fin a ⊕ Fin b) (ha : 0 < a) (hb : 0 < b)
    (u : (Fin a → Fin b → k) → GL (Fin N) k)
    (hu : ∀ X, (u X : Matrix (Fin N) (Fin N) k) =
      Matrix.reindex e.symm e.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)) (w : V) :
    w ∈ Submodule.span ℂ {x | ∃ (Y : Fin a → Fin b → k) (y : V), x = π (u Y) y - y} := by
  have h : a + b = N := by
    have := Fintype.card_congr e
    simpa using this.symm
  have H := ((GlobalTheory.SmGL.CuspMax.isCuspidal_iff_maximal k N V π).1 hπ).2 a b h ha hb
  have H' : Subsingleton (Jacquet π (unipRad k (GlobalTheory.SmGL.two e.symm))) := by
    refine GlobalTheory.SmGL.CuspMax.subsingleton_jacquet_of_perm π (e.trans (stdSum h)) (fun i j hij => ?_) H
    have h1 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two (stdSum h)) ((e.trans (stdSum h)) i) = (e i).isRight :=
      fun i => blk_two_apply (stdSum h) (e i)
    have h2 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two e.symm) i = (e i).isRight := fun i => by
      have := blk_two_apply e.symm (e i)
      rwa [Equiv.symm_apply_apply] at this
    rw [h1, h1] at hij
    rw [h2, h2]
    exact hij
  have htop : twKer π (unipRad k (GlobalTheory.SmGL.two e.symm)) 1 = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 H'
  have hw : w ∈ twKer π (unipRad k (GlobalTheory.SmGL.two e.symm)) 1 := htop ▸ Submodule.mem_top
  refine (Submodule.span_le.2 ?_) hw
  rintro _ ⟨n, v, rfl⟩
  refine Submodule.subset_span ⟨fun p q => (n : GL (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q)),
    v, ?_⟩
  have hn : (n : GL (Fin N) k) = u (fun p q => (n : GL (Fin N) k) (e.symm (Sum.inl p)) (e.symm (Sum.inr q))) := by
    have hent := GlobalTheory.SmGL.CuspMax.mem_unipRad_iff_entries.1 n.2
    have h2 : ∀ i, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.two e.symm) i = (e i).isRight := fun i => by
      have := blk_two_apply e.symm (e i)
      rwa [Equiv.symm_apply_apply] at this
    ext i j
    rw [hu, Matrix.reindex_apply, Matrix.submatrix_apply]
    simp only [Equiv.symm_symm]
    obtain ⟨s, rfl⟩ := e.symm.surjective i
    obtain ⟨t, rfl⟩ := e.symm.surjective j
    simp only [Equiv.apply_symm_apply]
    rcases s with p | p <;> rcases t with q | q
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₁₁]
      simp [Matrix.one_apply]
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₂₁]
      simp [Matrix.one_apply]
    · rw [hent _ _ (by rw [h2, h2]; simp), Matrix.fromBlocks_apply₂₂]
      simp [Matrix.one_apply]
  rw [← hn]
  simp

end GlobalTheory.SmGL.CuspSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFirstColumnSpaceRankSignatureSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem sig_X'_eq_sig_Y (D : D7) (τ : D.host.E →+* ℂ) : D.sp.X'.sig τ = (D.sp.Y D.R.m).sig τ := by
  have hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a) := D.sp.cm.cmUnram.2.1 τ
  have hw : (Matrix.of fun i j => (D.sp.Y D.R.m).hT (D.sp.eYm (D.sp.X'.frame i)) (D.sp.eYm (D.sp.X'.frame j))) =
      D.sp.X'.gram := by
    exact Matrix.ext fun i j => D.sp.eYm_isom _ _
  have hs := D.sp.X'_sig τ
  rw [← hw] at hs
  have k := sig_family (D.sp.Y D.R.m) τ hτ _ hs (D.sp.Y_sig D.R.m τ)
  have h3 := sig_sum _ D.sp.X'_sig τ
  have h4 := sig_sum _ (D.sp.Y_sig D.R.m) τ
  have hYr : (D.sp.Y D.R.m).rank = D.sp.X'.rank := by
    rw [D.sp.Y_rank D.R.m le_rfl, D.sp.X'_rank]; rfl
  rw [hYr] at k h4
  exact Prod.ext (by omega) (by omega)

theorem colY_isV : ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ j, j ≤ D.R.m → (columnBlock L j).IsV (rankV D 0 j) ((D.R.m - j) / 2) := by
  intro D T L μ0 hL j hj
  have hr : rankV D 0 j = D.R.rankY j := by
    simp only [rankV, zero_mul, add_zero]; rfl
  rw [hr]
  rcases hj.eq_or_lt with rfl | hlt
  · rw [colY_m]
    refine ⟨D.sp.X'_rank, D.sp.X'_sig, fun τ => ?_,
      GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX⟩
    exact (sig_X'_eq_sig_Y D τ).trans (D.Y_sigval _ le_rfl τ)
  · rw [colY_lt L hlt]
    have e : min j D.R.m = j := min_eq_left hj
    refine ⟨?_, D.sp.Y_sig _, fun τ => ?_,
      GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY j hlt)⟩
    · exact (D.sp.Y_rank _ (min_le_right _ _)).trans (by rw [e])
    · exact (D.Y_sigval _ (min_le_right _ _) τ).trans (by rw [e]; rfl)

end GlobalTheory.ChiGrid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumIntegralIdelesEulerProductStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_integralIdeles_eulerProduct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (Pq : HeightOneSpectrum (OF E) → HeightOneSpectrum (𝓞 E)) (S L : ℂ), UnramFin E → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ → (∀ q ∈ Q, Over (Pq q) q) → 1 < S.re → HasProd (eulerFactor χ S) L → open Classical in HasSum (fun z : {z : (Af E)ˣ ⧸ hatOUnits (condQ 𝔣 Q) // ∃ y : (Af E)ˣ, (QuotientGroup.mk y : (Af E)ˣ ⧸ hatOUnits (condQ 𝔣 Q)) = z ∧ (y : Af E) ∈ hatO (condQ 𝔣 Q)} => (finPart χ z.1.out : ℂ) * ((modF z.1.out : ℝ) : ℂ) ^ S) (L * ∏ q ∈ Q.filter (fun q => UnrAt χ (Pq q)), ((1 - (val χ (Pq q) : ℂ) * (Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) * (1 - (val χ (Pq q) : ℂ)⁻¹ * (Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) + ((Ideal.absNorm q.asIdeal : ℂ) - 1) * ((Ideal.absNorm q.asIdeal : ℂ) ^ (-S)) ^ 2)) := by
  first | exact @GlobalTheory.CMVal.Euler.hasSum_euler | exact GlobalTheory.CMVal.Euler.hasSum_euler | (intros; apply GlobalTheory.CMVal.Euler.hasSum_euler <;> assumption)
end

