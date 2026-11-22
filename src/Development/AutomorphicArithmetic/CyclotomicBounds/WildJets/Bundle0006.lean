import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactPairRealAverageFockEqJetOperator
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaStepDistributionEquivariantRational
import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0004

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.RealRow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.KJInf Formalism.L2.Ker MvPolynomial in
private theorem jet_smul_subst {ι : Type} [Fintype ι] {a b : ℕ} (c : ℂ) (ℓ : FP ι a b →ₗ[ℂ] ℂ)
    (g : ι → Matrix (Fin a) (Fin a) ℂ) (h : ι → Matrix (Fin b) (Fin b) ℂ) (n : ι → ℕ) (P : PY ι a) :
    jetMap (fun m => c * ℓ (mvZ g h (monomial m 1))) n P =
      (c * ∏ τ, (g τ).det ^ n τ) • lft h (jetMap (fun m => ℓ (monomial m 1)) n (lft g P)) := by
  have h1 : ∀ (J : (DVar ι a b →₀ ℕ) → ℂ) Q, jetLin (fun m => c * J m) Q = c • jetLin J Q := fun J Q => by
    refine LinearMap.congr_fun (f := jetLin (fun m => c * J m)) (g := c • jetLin J) ((basisMonomials _ ℂ).ext fun m => ?_) Q
    rw [coe_basisMonomials]
    simp only [LinearMap.smul_apply, GlobalTheory.KerT.RatLaw.jetLin_monomial, smul_monomial, smul_eq_mul]
  have h2 : ∀ (J : (DVar ι a b →₀ ℕ) → ℂ), jetMap (fun m => c * J m) n P = c • jetMap J n P := fun J => by
    simp only [jetMap, LinearMap.comp_apply, h1]
  have h3 : GlobalTheory.KerT.RatLaw.tabFn (fun m => ℓ (monomial m 1)) = ℓ := by
    refine (basisMonomials _ ℂ).ext fun m => ?_
    rw [coe_basisMonomials]
    exact GlobalTheory.KerT.RatLaw.tabFn_monomial _ m
  rw [h2, GlobalTheory.KerT.RatLaw.jetMap_subst (J := fun m => ℓ (monomial m 1)) g h (fun m => by rw [h3]; rfl), smul_smul]
  rfl

open GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.RowHoweAvg GlobalTheory.FockReal GlobalTheory.DefStep MvPolynomial in
theorem UpperTheory.WildA.realRow :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil} {U₀ : Set T} (N : Std G U₀) {μ₀ : T}, L.Is μ₀ → ∀ (i : ℕ), i + 1 ≤ D.R.m →
      ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D (G.chrS (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) τ (a τ)) → (∀ τ, HasInfExp D (G.chrT (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) τ (b τ)) →
      ∀ (e₁ e₂ : D.what₂.Tau → ℤ), (∀ τ, (e₁ τ : ℚ) = a τ + GlobalTheory.FockReal.sgnP (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) * (G.pS (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).rank / 2) →
        (∀ τ, (e₂ τ : ℚ) = -(b τ + GlobalTheory.FockReal.sgnP (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) * (G.pT (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).rank / 2)) →
      ∀ (ℓ : PolF D (G.pT (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).rank (G.pS (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).rank →ₗ[ℂ] ℂ) (k : GA D (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small)), k ∈ GinfC (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) →
      ∀ k' : GA D (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big), k' ∈ GinfC (G.V ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) →
        Formalism.L2.Ker.jetOp (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) (fun m => GlobalTheory.FockReal.realChar W (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) e₁ e₂ k k' *
                  ℓ (GlobalTheory.FockReal.realSubst W N.frC (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T) k k' (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T))) 1))) (nuEnd G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) =
          GlobalTheory.DefStep.realAct W.θ N.fr ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big k'⁻¹ ∘ₗ
            Formalism.L2.Ker.jetOp (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small) (wt G ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).big) (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T))) 1)) (nuEnd G (GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)) ∘ₗ
            GlobalTheory.DefStep.realAct W.θ N.fr ((GlobalTheory.ChiGrid.Pair.chi i D.R.m : GlobalTheory.ChiGrid.Pair T)).small k := by
  intro D T L sc G W U N μ0 hL i hi a b ha hb e₁ e₂ he₁ he₂ ℓ k hk k' hk'
  have hi' : i < D.R.m := hi
  have hp : DefPair D.R.m (.chi i D.R.m : Pair T) := ⟨hi', rfl⟩
  have hn := DefPair.nodes hp
  have hX := GlobalTheory.SeeSaw.ontoUni_inB D W.θ (G.V (.grid i D.R.m)) (N.frC _) W.θ_is (GlobalTheory.RealType.frC_on N hn.1)
  have hY := GlobalTheory.SeeSaw.ontoUni_inB D W.θ (G.V (.grid (i + 1) D.R.m)) (N.frC _) W.θ_is (GlobalTheory.RealType.frC_on N hn.2)
  have hJ := (wtOK_of_defPair G _ hp).2
  have hm := fun τ => exps_match G hL hi' τ (ha τ) (hb τ) (he₁ τ) (he₂ τ)
  let f : D.what₂.Tau × Fin (G.V (.grid (i + 1) D.R.m)).rank × Fin (G.V (.grid i D.R.m)).rank →
      D.what₂.Tau × Fin (G.V (.grid i D.R.m)).rank × Fin (G.V (.grid (i + 1) D.R.m)).rank := fun k => (k.1, k.2.2, k.2.1)
  let ℓ' : FP D.what₂.Tau (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank →ₗ[ℂ] ℂ := ℓ ∘ₗ (rename f).toLinearMap
  have hJ' : (fun m => ℓ (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1)) =
      fun m => ℓ' (monomial m 1) := by
    funext m
    simp only [ℓ', LinearMap.comp_apply, AlgHom.toLinearMap_apply, rename_monomial]
    rfl
  have hinv : ∀ τ, (inB W.θ _ (N.frC (.grid i D.R.m)) k τ)⁻¹ = inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹ τ := fun τ =>
    GlobalTheory.KJAvg.ontoUni_inv hX ⟨k, hk⟩ τ
  have e : ∀ P, realSubst W N.frC (.chi i D.R.m) k k' (rename f P) =
      rename f (mvZ (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹) (inB W.θ _ (N.frC (.grid (i + 1) D.R.m)) k') P) := fun P => by
    rw [← funext hinv, ← substF_rename]
    have e1 := fun τ => (map_conj_of_unitary (hX.uni ⟨k, hk⟩ τ)).1
    have e2 := fun τ => (map_conj_of_unitary (hY.uni ⟨k', hk'⟩ τ)).2
    exact congrArg₂ (fun x y => GlobalTheory.CompactHowe.substF x y (rename f P)) (funext e1) (funext e2)
  have hJ2 : (fun m => realChar W (.chi i D.R.m) e₁ e₂ k k' *
      ℓ (realSubst W N.frC (.chi i D.R.m) k k' (MvPolynomial.monomial (m.mapDomain (fvar G (.chi i D.R.m : Pair T))) 1))) =
      fun m => realChar W (.chi i D.R.m) e₁ e₂ k k' * ℓ' (mvZ (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹)
        (inB W.θ _ (N.frC (.grid (i + 1) D.R.m)) k') (monomial m 1)) := by
    funext m
    have := e (monomial m 1)
    rw [rename_monomial] at this
    exact congrArg (fun x => realChar W (.chi i D.R.m) e₁ e₂ k k' * ℓ x) this
  have hne : ∀ τ, (inB W.θ _ (N.frC (.grid i D.R.m)) k τ).det ≠ 0 := fun τ =>
    (Matrix.UnitaryGroup.det_isUnit ⟨_, hX.uni ⟨k, hk⟩ τ⟩).ne_zero
  have hsc : realChar W (.chi i D.R.m) e₁ e₂ k k' *
      ∏ τ, (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹ τ).det ^ nuEnd G (.chi i D.R.m : Pair T) τ =
      (∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid (i + 1) D.R.m)) k')).det ^ (wt G (.grid (i + 1) D.R.m) τ).detShift) *
      ∏ τ, (compAt W.θ τ (Formalism.L2.Theta.mt (G.V (.grid i D.R.m)) k⁻¹)).det ^ (wt G (.grid i D.R.m) τ).detShift := by
    simp only [realChar, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have h1 := hne τ
    rw [← det_inB W.θ N (.grid i D.R.m) k⁻¹, ← hinv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', ← zpow_natCast,
      ← (hm τ).2, ← (hm τ).1, zpow_add₀ (inv_ne_zero h1), _root_.inv_zpow _ (e₁ τ), mul_assoc, det_inB]
    rw [det_inB] at h1
    exact congrArg₂ (· * ·) rfl (mul_inv_cancel_left₀ (zpow_ne_zero _ h1) _)
  have key : ∀ v : VV ℂ (wt G (.grid i D.R.m)),
      Formalism.L2.Ker.jetOp (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m))
        (fun m => realChar W (.chi i D.R.m) e₁ e₂ k k' * ℓ' (mvZ (inB W.θ _ (N.frC (.grid i D.R.m)) k⁻¹)
        (inB W.θ _ (N.frC (.grid (i + 1) D.R.m)) k') (monomial m 1))) (nuEnd G (.chi i D.R.m : Pair T)) v =
      realAct W.θ N.fr (.grid (i + 1) D.R.m) k'⁻¹ (Formalism.L2.Ker.jetOp (wt G (.grid i D.R.m)) (wt G (.grid (i + 1) D.R.m))
        (fun m => ℓ' (monomial m 1)) (nuEnd G (.chi i D.R.m : Pair T)) (realAct W.θ N.fr (.grid i D.R.m) k v)) := fun v => by
    have hk1 := realAct_inv_coe W.θ N (.grid i D.R.m) k⁻¹ v
    rw [inv_inv] at hk1
    refine Subtype.ext ?_
    rw [realAct_inv_coe, jetOp_coe hJ, jetOp_coe hJ, hk1, jet_smul_subst, map_smul, map_smul, smul_smul, hsc]
  rw [hJ', hJ2]
  exact LinearMap.ext key
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.WtBdWtOf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
open GlobalTheory.SignedHC

private theorem wtBd_wtOf (n : ℕ) (E : Finset ℚ) (B : ℝ) (hB : 0 ≤ B) (hE : ∀ x ∈ E, |(x : ℝ)| ≤ B)
    (a a' : Fin n) (h : a ≤ a') : (((wtOf n E).w a - (wtOf n E).w a' : ℤ) : ℝ) ≤ 2 * B := by
  by_cases hc : E.card = n ∧ InCoset (((n : ℚ) - 1) / 2) E
  · have e1 := wtOf_cast hc.1 hc.2 a
    have e2 := wtOf_cast hc.1 hc.2 a'
    have b1 := abs_le.1 (hE _ (descEnum_mem E hc.1 a))
    have b2 := abs_le.1 (hE _ (descEnum_mem E hc.1 a'))
    unfold highestWeight at e1 e2
    have e1' := congrArg (fun q : ℚ => (q : ℝ)) e1
    have e2' := congrArg (fun q : ℚ => (q : ℝ)) e2
    have h' : ((a : ℕ) : ℝ) ≤ ((a' : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at e1' e2' ⊢
    linarith [b1.1, b1.2, b2.1, b2.2]
  · rw [wtOf, dif_neg hc]
    simp only [Pi.zero_apply, sub_self, Int.cast_zero]
    linarith

private theorem wtBd_natW {n : ℕ} (lam : DomWeight n) (C : ℝ)
    (h : ∀ a a' : Fin n, a ≤ a' → ((lam.w a - lam.w a' : ℤ) : ℝ) ≤ C) (a : Fin n) :
    ((lam.natW a : ℕ) : ℝ) ≤ C := by
  have hn : 0 < n := a.pos
  have hle : a ≤ (⟨n - 1, by omega⟩ : Fin n) := by
    have := a.2
    show a.1 ≤ n - 1
    omega
  have h1 := h a _ hle
  have h2 := lam.anti hle
  have h3 : ((lam.natW a : ℕ) : ℤ) = lam.w a - lam.w ⟨n - 1, by omega⟩ := by
    unfold DomWeight.natW DomWeight.detShift
    rw [dif_pos hn]
    exact Int.toNat_of_nonneg (by linarith)
  rw [← h3] at h1
  exact_mod_cast h1

private theorem wtBd_dual {n : ℕ} (lam : DomWeight n) (C : ℝ)
    (h : ∀ a a' : Fin n, a ≤ a' → ((lam.w a - lam.w a' : ℤ) : ℝ) ≤ C) (a a' : Fin n) (haa : a ≤ a') :
    ((lam.dual.w a - lam.dual.w a' : ℤ) : ℝ) ≤ C := by
  have h1 := h a'.rev a.rev (Fin.rev_le_rev.2 haa)
  have e : lam.dual.w a - lam.dual.w a' = lam.w a'.rev - lam.w a.rev := by
    show -lam.w a.rev - -lam.w a'.rev = _
    ring
  rw [e]; exact h1

end

theorem UpperTheory.WildA.wtBd :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → sc.cGap = 1 → ∀ p : GlobalTheory.ChiGrid.Pair T, DefPair D.R.m p →
      ∀ τ a, (((wt G p.big τ).natW a : ℕ) : ℝ) ≤ 12 * large₂.sc.b := by
  intro D T L sc G large₂ hS hH hc p hp τ
  obtain ⟨-, -, -, -, -, -, -, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS
  have key : ∀ X : Node, DefNode D.R.m X → ∀ a, (((wt G X τ).natW a : ℕ) : ℝ) ≤ 12 * large₂.sc.b := by
    intro X hX
    have hb := UpperTheory.WildA.parBd D large₂ hS hH X hX τ
    rw [← hc] at hb
    have hl : ∀ a a', a ≤ a' → (((listedWt G X τ).w a - (listedWt G X τ).w a' : ℤ) : ℝ) ≤ 12 * large₂.sc.b := by
      intro a a' h
      have := wtBd_wtOf (G.V X).rank _ (6 * large₂.sc.b) (by linarith) hb a a' h
      unfold listedWt
      linarith
    cases X with
    | core i => exact hX.elim
    | top j => exact wtBd_natW _ _ hl
    | grid i j => exact wtBd_natW _ _ (wtBd_dual _ _ hl)
  exact key p.big hp.nodes.2
end

