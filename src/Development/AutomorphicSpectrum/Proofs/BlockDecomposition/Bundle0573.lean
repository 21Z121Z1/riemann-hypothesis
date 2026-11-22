import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0237
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0046
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0031
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0015
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0037

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPos
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.FrobJm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem piTensor_rep_isIrreducible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL k) :
    (piTensor fun a => (x a).rep).IsIrreducible := by
  have hKex : ∀ N : ℕ, ∃ K : Subgroup (GL (Fin N) k),
      IsOpen (K : Set (GL (Fin N) k)) ∧ IsCompact (K : Set (GL (Fin N) k)) := by
    intro N
    have hT2 : T2Space k := inferInstance
    let O : Subring k := (ValuativeRel.valuation k).integer
    have hOo : IsOpen (O : Set k) := (ValuativeRel.valuation k).isOpen_integer
    have hOc : IsCompact (O : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall (K := k) 1
    let K : Subgroup (GL (Fin N) k) :=
      { carrier := {g | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ O) ∧
            ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ O}
        mul_mem' := by
          rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
          refine ⟨fun i j => ?_, fun i j => ?_⟩
          · rw [Units.val_mul, Matrix.mul_apply]
            exact sum_mem fun l _ => mul_mem (ha1 i l) (hb1 l j)
          · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
            exact sum_mem fun l _ => mul_mem (hb2 i l) (ha2 l j)
        one_mem' := by
          refine ⟨fun i j => ?_, fun i j => ?_⟩
          · rw [Units.val_one, Matrix.one_apply]
            split_ifs
            exacts [one_mem _, zero_mem _]
          · rw [inv_one, Units.val_one, Matrix.one_apply]
            split_ifs
            exacts [one_mem _, zero_mem _]
        inv_mem' := by
          rintro a ⟨ha1, ha2⟩
          exact ⟨ha2, by rw [inv_inv]; exact ha1⟩ }
    have hKset : (K : Set (GL (Fin N) k)) =
        (⋂ i, ⋂ j, (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k)) ∩
          ⋂ i, ⋂ j, (fun g : GL (Fin N) k => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      exact Iff.rfl
    refine ⟨K, ?_, ?_⟩
    · rw [hKset]
      refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_)
        (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_)
      · exact Units.continuous_val.matrix_elem i j
      · exact Units.continuous_coe_inv.matrix_elem i j
    · rw [Units.isEmbedding_embedProduct.isInducing.isCompact_iff]
      let S : Set (Matrix (Fin N) (Fin N) k) := {A | ∀ i j, A i j ∈ O}
      have hS : IsCompact S := by
        have h := isCompact_univ_pi (fun _ : Fin N => isCompact_univ_pi (fun _ : Fin N => hOc))
        have hSe : S = Set.univ.pi (fun _ : Fin N => Set.univ.pi fun _ : Fin N => (O : Set k)) := by
          ext A
          show (∀ i j, A i j ∈ O) ↔ ∀ i ∈ (Set.univ : Set (Fin N)), ∀ j ∈ (Set.univ : Set (Fin N)), A i j ∈ (O : Set k)
          constructor
          · intro hA i _ j _
            exact hA i j
          · intro hA i j
            exact hA i (Set.mem_univ i) j (Set.mem_univ j)
        rw [hSe]
        exact h
      have hsub : Units.embedProduct (Matrix (Fin N) (Fin N) k) '' (K : Set (GL (Fin N) k)) =
          (S ×ˢ (MulOpposite.op '' S)) ∩
            {p | p.1 * MulOpposite.unop p.2 = 1 ∧ MulOpposite.unop p.2 * p.1 = 1} := by
        ext p
        constructor
        · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
          exact ⟨⟨hg1, (g⁻¹ : GL (Fin N) k).val, hg2, rfl⟩, g.mul_inv, g.inv_mul⟩
        · rintro ⟨⟨hA, B, hB, hBp⟩, h1, h2⟩
          refine ⟨⟨p.1, MulOpposite.unop p.2, h1, h2⟩, ⟨hA, ?_⟩, rfl⟩
          show ∀ i j, (MulOpposite.unop p.2) i j ∈ O
          rw [← hBp]
          exact hB
      rw [hsub]
      refine (hS.prod (hS.image MulOpposite.continuous_op)).inter_right ?_
      exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd))
        continuous_const).inter
        (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)
  refine GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) ?_
  intro a φ hφ
  obtain ⟨K, hKo, hKc⟩ := hKex (x a).1
  exact GlobalTheory.SchurAdm.schur_admissible _ K hKo hKc _ _ (x a).2.rep.irr
    (hA k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem eval_map (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (g : GL n k) (v : V) :
    (f (τ g v)).1.1 1 = (f v).1.1 g := by
  have hf : f (τ g v) = parInd e ρ g (f v) := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun (f.isIntertwining' g) v
  rw [hf, parInd_apply, one_mul]

theorem eval_unipRad (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} (φ : IndSp e ρ)
    (u : unipRad k e) : φ.1.1 (u : GL n k) = φ.1.1 1 := by
  have hp : (u : GL n k) ∈ parab k e := unipRad_le_parab k e u.2
  have hl : leviProj k e ⟨u, hp⟩ = 1 := (coe_mem_unipRad k (e := e) ⟨(u : GL n k), hp⟩).1 u.2
  have hφ := parInd_law e ρ φ ⟨u, hp⟩ 1
  rw [hl] at hφ
  simpa using hφ

def evalOne (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) : V →ₗ[ℂ] W where
  toFun v := (f v).1.1 1
  map_add' v w := by simp
  map_smul' c v := by simp

theorem twKer_le_ker_evalOne (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V}
    {ρ : Representation ℂ (Levi k m) W} (f : τ.IntertwiningMap (parInd e ρ)) :
    twKer τ (unipRad k e) 1 ≤ LinearMap.ker (evalOne e f) := by
  unfold GlobalTheory.PRep.twKer
  rw [Submodule.span_le]
  rintro w ⟨u, v, rfl⟩
  have hu : evalOne e f (τ (u : GL n k) v) = evalOne e f v := by
    show (f (τ (u : GL n k) v)).1.1 1 = (f v).1.1 1
    rw [eval_map, eval_unipRad e (f v) u]
  simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, hu, MonoidHom.one_apply,
    Units.val_one, one_smul, sub_self]

def frobMap (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) : (jac e τ).IntertwiningMap ρ where
  toLinearMap := (twKer τ (unipRad k e) 1).liftQ (evalOne e f) (twKer_le_ker_evalOne e f)
  isIntertwining' g := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have h := parInd_law e ρ (f v) ⟨_, leviEmb_mem_parab k e g⟩ 1
    rw [mul_one] at h
    simp only [leviProj_leviEmb] at h
    have h2 : evalOne e f (τ (leviEmb k e g) v) =
        (deltaHalf k m g : ℂ) • ρ g (evalOne e f v) := (eval_map e f _ v).trans h
    show (twKer τ (unipRad k e) 1).liftQ (evalOne e f) (twKer_le_ker_evalOne e f)
        (jac e τ g (Submodule.Quotient.mk v)) = ρ g (evalOne e f v)
    rw [jac_mk, map_smul]
    change (((deltaHalf k m g)⁻¹ : ℂˣ) : ℂ) • evalOne e f (τ (leviEmb k e g) v) = _
    rw [h2, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

theorem frobMap_mk (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (v : V) :
    frobMap e f (Submodule.Quotient.mk v) = (f v).1.1 1 := rfl

theorem frobMap_ne_zero (e : (Σ a, m a) ≃ n) {τ : Representation ℂ (GL n k) V} {ρ : Representation ℂ (Levi k m) W}
    (f : τ.IntertwiningMap (parInd e ρ)) (hf : ∃ v, f v ≠ 0) : ∃ y, frobMap e f y ≠ 0 := by
  obtain ⟨v, hv⟩ := hf
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  apply hv
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have h1 := frobMap_mk e f (τ g v)
  rw [hcon, eval_map] at h1
  simpa using h1.symm

theorem surjective_of_ne_zero {G : Type} [Group G] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hσ : σ.IsIrreducible) (f : ρ.IntertwiningMap σ) (hf : ∃ y, f y ≠ 0) : Function.Surjective f := by
  haveI := hσ
  rcases Representation.IsIrreducible.surjective_or_eq_zero f with hs | hz
  · exact hs
  · obtain ⟨y, hy⟩ := hf
    exact (hy (by simp [hz])).elim

theorem one_le_jm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ →
    ∀ f : τ.IntertwiningMap (prodIrr x hd), (∃ v, f v ≠ 0) → 1 ≤ jm x hd τ := by
  intro k _ _ _ _ hA h N x hd V _ _ τ _ f hf
  let f' : τ.IntertwiningMap (parInd (stdBlocks (fun a => (x a).1) hd) (piTensor fun a => (x a).rep)) := f
  obtain ⟨y, hy⟩ := frobMap_ne_zero _ f' hf
  have hs := surjective_of_ne_zero (piTensor_rep_isIrreducible hA x) (frobMap _ f') ⟨y, hy⟩
  have hq := jhMult_ne_zero_iff.2 (IsSubquotient.of_surjective _ hs)
  exact Order.one_le_iff_ne_zero.2 hq

end GlobalTheory.CompanionTheory.FrobJm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFourierContinuationDecay
section
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HalfWeight

lemma one_add_abs_le_two_mul_exp_sq (x : ℝ) : 1 + |x| ≤ 2 * Real.exp (x ^ 2) := by
  have h1 : x ^ 2 + 1 ≤ Real.exp (x ^ 2) := Real.add_one_le_exp _
  have h2 : |x| ≤ 1 + x ^ 2 := by
    nlinarith [sq_abs x, sq_nonneg (|x| - 1), abs_nonneg x]
  nlinarith [sq_nonneg x]

lemma norm_half_add_le (s : ℂ) (a D L B : ℝ) (hL : L ≤ s.re) (hB : s.re ≤ B)
    (hD : |L| + |B| + |a| ≤ D) :
    ‖s / 2 + (a : ℂ)‖ ≤ 2 * (D + 1) * Real.exp (s.im ^ 2) := by
  have hre : |s.re| ≤ |L| + |B| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le L, abs_nonneg B]
    · linarith [le_abs_self B, abs_nonneg L]
  have hs : ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
  have h1 : ‖s / 2 + (a : ℂ)‖ ≤ ‖s‖ / 2 + |a| := by
    refine (norm_add_le _ _).trans ?_
    simp [Complex.norm_real]
  have hD0 : 0 ≤ D := by
    linarith [abs_nonneg L, abs_nonneg B, abs_nonneg a]
  have him := abs_nonneg s.im
  have h2 : ‖s / 2 + (a : ℂ)‖ ≤ (D + 1) * (1 + |s.im|) := by
    have h4 : 0 ≤ D * |s.im| := mul_nonneg hD0 him
    have h5 : (D + 1) * (1 + |s.im|) = D + 1 + D * |s.im| + |s.im| := by ring
    rw [h5]
    linarith [abs_nonneg L, abs_nonneg B, abs_nonneg a]
  have h3 := one_add_abs_le_two_mul_exp_sq s.im
  calc ‖s / 2 + (a : ℂ)‖ ≤ (D + 1) * (1 + |s.im|) := h2
    _ ≤ (D + 1) * (2 * Real.exp (s.im ^ 2)) := by
        exact mul_le_mul_of_nonneg_left h3 (by linarith)
    _ = 2 * (D + 1) * Real.exp (s.im ^ 2) := by ring

lemma mul_exp_le_of_abs_le {c E y : ℝ} (hy : 0 ≤ y) (hc : |c| ≤ E) :
    c * Real.exp (c * y) ≤ E * Real.exp (E * y) := by
  have hE : 0 ≤ E := (abs_nonneg c).trans hc
  have h1 : c ≤ E := (le_abs_self c).trans hc
  have h2 : Real.exp (c * y) ≤ Real.exp (E * y) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h1 hy)
  calc c * Real.exp (c * y) ≤ E * Real.exp (c * y) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ E * Real.exp (E * y) := mul_le_mul_of_nonneg_left h2 hE

lemma step_bound {n₁ n₂ p₁ p₂ c₁ c₂ D y x : ℝ} (m : ℕ) (hD : 0 ≤ D) (hy : 0 ≤ y) (hx : 0 < x)
    (hn₁0 : 0 ≤ n₁) (hn₂0 : 0 ≤ n₂) (hp₁0 : 0 ≤ p₁) (hp₂0 : 0 ≤ p₂)
    (hn₁ : n₁ ≤ 2 * (D + 1) * Real.exp y) (hn₂ : n₂ ≤ 2 * (D + 1) * Real.exp y)
    (hp₁ : p₁ ≤ c₁ * Real.exp (c₁ * y) / x ^ m) (hp₂ : p₂ ≤ c₂ * Real.exp (c₂ * y) / x ^ m) :
    (n₁ * p₁ + n₂ * p₂) / (2 * Real.pi * x) ≤
      (4 * (D + 1) * (|c₁| + |c₂|) + (|c₁| + |c₂|) + 1) *
        Real.exp ((4 * (D + 1) * (|c₁| + |c₂|) + (|c₁| + |c₂|) + 1) * y) / x ^ (m + 1) := by
  set E := |c₁| + |c₂| with hEdef
  have hE : 0 ≤ E := by positivity
  have ht : 0 < x ^ m := pow_pos hx m
  have hexpE := Real.exp_pos (E * y)
  have hexpy := Real.exp_pos y
  set Q := E * Real.exp (E * y) / x ^ m with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hq₁ : p₁ ≤ Q := hp₁.trans (div_le_div_of_nonneg_right
    (mul_exp_le_of_abs_le hy (by rw [hEdef]; linarith [abs_nonneg c₂])) ht.le)
  have hq₂ : p₂ ≤ Q := hp₂.trans (div_le_div_of_nonneg_right
    (mul_exp_le_of_abs_le hy (by rw [hEdef]; linarith [abs_nonneg c₁])) ht.le)
  set P := 2 * (D + 1) * Real.exp y with hP
  have hP0 : 0 ≤ P := by positivity
  have hsum : n₁ * p₁ + n₂ * p₂ ≤ 2 * (P * Q) := by
    have := mul_le_mul hn₁ hq₁ hp₁0 hP0
    have := mul_le_mul hn₂ hq₂ hp₂0 hP0
    linarith
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hden : x ≤ 2 * Real.pi * x := by nlinarith
  have h1 : (n₁ * p₁ + n₂ * p₂) / (2 * Real.pi * x) ≤ 2 * (P * Q) / x := by
    calc (n₁ * p₁ + n₂ * p₂) / (2 * Real.pi * x) ≤ (n₁ * p₁ + n₂ * p₂) / x :=
          div_le_div_of_nonneg_left (by positivity) hx hden
      _ ≤ 2 * (P * Q) / x := div_le_div_of_nonneg_right hsum hx.le
  have h2 : 2 * (P * Q) / x =
      (4 * (D + 1) * E * Real.exp ((E + 1) * y)) / x ^ (m + 1) := by
    have hsplit : Real.exp ((E + 1) * y) = Real.exp (E * y) * Real.exp y := by
      rw [← Real.exp_add]
      ring_nf
    rw [hP, hQ, pow_succ, hsplit]
    field_simp
    <;> ring
  rw [h2] at h1
  refine h1.trans (div_le_div_of_nonneg_right ?_ (pow_pos hx _).le)
  set C := 4 * (D + 1) * E + E + 1 with hC
  have hc1 : 4 * (D + 1) * E ≤ C := by rw [hC]; linarith
  have hc2 : E + 1 ≤ C := by
    have : 0 ≤ 4 * (D + 1) * E := by positivity
    rw [hC]; linarith
  have hexp : Real.exp ((E + 1) * y) ≤ Real.exp (C * y) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc2 hy)
  exact mul_le_mul hc1 hexp (Real.exp_pos _).le (by linarith)

theorem kernel_fourier_continuation_decay : W0 → W1 → W2 := by
  intro h0 h1 m
  induction m with
  | zero =>
    intro a b
    refine ⟨fun s ξ => Phi (s / 2 + a) (s / 2 + b) ξ, ?_, ?_, ?_, ?_⟩
    · intro ξ
      simpa using (h0 a b).1 ξ
    · intro s hs
      have hs' : s ∈ HP (1 - a - b) := by simpa using hs
      exact ((h0 a b).2.1 s hs').2.measurable
    · intro s _ ξ _
      rfl
    · intro δ B hδ
      obtain ⟨C, hC⟩ := (h0 a b).2.2 δ B hδ
      refine ⟨C, fun s ξ _ hl hu => ?_⟩
      simpa using hC s ξ (by simpa using hl) hu
  | succ m ih =>
    intro a b
    obtain ⟨P₁, d₁, m₁, e₁, b₁⟩ := ih (a + 1) b
    obtain ⟨P₂, d₂, m₂, e₂, b₂⟩ := ih a (b + 1)
    have hr₁ : 1 - (a + 1) - b - (m : ℝ) = 1 - a - b - ((m + 1 : ℕ) : ℝ) := by
      push_cast; ring
    have hr₂ : 1 - a - (b + 1) - (m : ℝ) = 1 - a - b - ((m + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [hr₁] at d₁ m₁
    rw [hr₂] at d₂ m₂
    refine ⟨fun s ξ => ((s / 2 + a) * P₁ s ξ - (s / 2 + b) * P₂ s ξ) / (2 * (Real.pi : ℂ) * ξ),
      ?_, ?_, ?_, ?_⟩
    · intro ξ
      have hlin : ∀ c : ℝ, DifferentiableOn ℂ (fun s : ℂ => s / 2 + (c : ℂ))
          (HP (1 - a - b - ((m + 1 : ℕ) : ℝ))) := fun c =>
        ((differentiable_id.div_const 2).add_const _).differentiableOn
      exact (((hlin a).mul (d₁ ξ)).sub ((hlin b).mul (d₂ ξ))).div_const _
    · intro s hs
      have hcast : Measurable fun ξ : ℝ => (2 * (Real.pi : ℂ) * (ξ : ℂ)) :=
        measurable_const.mul Complex.measurable_ofReal
      exact (((m₁ s hs).const_mul _).sub ((m₂ s hs).const_mul _)).div hcast
    · intro s hs ξ hξ
      have hs₁ : s ∈ HP (1 - (a + 1) - b) := by
        have : 1 - a - b < s.re := hs
        show 1 - (a + 1) - b < s.re
        linarith
      have hs₂ : s ∈ HP (1 - a - (b + 1)) := by
        have : 1 - a - b < s.re := hs
        show 1 - a - (b + 1) < s.re
        linarith
      have hre : 1 < (s / 2 + (a : ℂ) + (s / 2 + (b : ℂ))).re := by
        have : 1 - a - b < s.re := hs
        simp
        linarith
      have hW := (h1 _ _ hre).1 ξ
      have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have ha : s / 2 + ((a + 1 : ℝ) : ℂ) = s / 2 + (a : ℂ) + 1 := by push_cast; ring
      have hb : s / 2 + ((b + 1 : ℝ) : ℂ) = s / 2 + (b : ℂ) + 1 := by push_cast; ring
      show ((s / 2 + a) * P₁ s ξ - (s / 2 + b) * P₂ s ξ) / (2 * (Real.pi : ℂ) * ξ) = _
      rw [e₁ s hs₁ ξ hξ, e₂ s hs₂ ξ hξ, ha, hb, ← hW]
      field_simp
    · intro δ B hδ
      obtain ⟨c₁, hc₁⟩ := b₁ δ B hδ
      obtain ⟨c₂, hc₂⟩ := b₂ δ B hδ
      set L := 1 - a - b - ((m + 1 : ℕ) : ℝ) + δ with hL
      set D := |L| + |B| + |a| + |b| with hDdef
      have hD : 0 ≤ D := by positivity
      refine ⟨4 * (D + 1) * (|c₁| + |c₂|) + (|c₁| + |c₂|) + 1, fun s ξ hξ hl hu => ?_⟩
      have hx : 0 < |ξ| := abs_pos.mpr hξ
      have hl₁ : 1 - (a + 1) - b - (m : ℝ) + δ ≤ s.re := by rw [hr₁]; exact hl
      have hl₂ : 1 - a - (b + 1) - (m : ℝ) + δ ≤ s.re := by rw [hr₂]; exact hl
      have hna := norm_half_add_le s a D L B hl hu
        (by rw [hDdef]; linarith [abs_nonneg b])
      have hnb := norm_half_add_le s b D L B hl hu
        (by rw [hDdef]; linarith [abs_nonneg a])
      have key := step_bound (x := |ξ|) (y := s.im ^ 2) m hD (sq_nonneg _) hx
        (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hna hnb
        (hc₁ s ξ hξ hl₁ hu) (hc₂ s ξ hξ hl₂ hu)
      refine le_trans ?_ key
      have hden : ‖2 * (Real.pi : ℂ) * (ξ : ℂ)‖ = 2 * Real.pi * |ξ| := by
        simp [Complex.norm_real, abs_of_pos Real.pi_pos]
      show ‖((s / 2 + a) * P₁ s ξ - (s / 2 + b) * P₂ s ξ) / (2 * (Real.pi : ℂ) * ξ)‖ ≤ _
      rw [norm_div, hden]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_mul]

end GlobalTheory.CompanionTheory.HalfWeight
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeGramIntegralAlmostAll
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.Grams

theorem sub_gramH_mem_latH : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n d : ℕ) (b : Module.Basis (Fin d) F E) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c), ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite, ∀ X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)), hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.latH σ b v n := by
  intro F E _ _ _ _ _ σ hCM M J hJ n d b T hT
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hb : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ k, inclR (F := F) (Fv F v) (b k) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun k => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (b k)
  have hJ' : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ i j, inclR (F := F) (Fv F v) (J i j) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (J i j)
  have hT' : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ a c, inclR (F := F) (Fv F v) (T a c) ∈ Formalism.L2.SG.LocVol.OEv (E := E) v :=
    Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun c => Formalism.L2.SG.Pf.NcS.IntWittPf.ev_oev (T a c)
  have htr : ∀ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) in Filter.cofinite,
      ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_int (Algebra.trace F E (b k))
  filter_upwards [Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_int (F := F) (1 / 2), hb, hJ', hT', htr,
    Formalism.L2.SG.Pf.NcS.KfOrbPf.ev_crd_oev (E := E) b] with v hh hbv hJv hTv htrv hc X hX
  have hrepr : ∀ z : Fv F v ⊗[F] E,
      z = ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k • ((1 : Fv F v) ⊗ₜ[F] b k) := by
    intro z
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply]
  have hx : ∀ a i, X a i ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a i
    rw [hrepr (X a i)]
    refine Subring.sum_mem _ fun k _ => ?_
    exact Formalism.L2.SG.Pf.NcS.IntWittPf.oev_smul' v (hX a i k) (hbv k)
  have hG : ∀ a c, hR (Fv F v) σ J (X a) (X c) ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a c
    show ∑ i, ∑ j, sigR (Fv F v) σ (X a i) * JR (Fv F v) J i j * X c j ∈
      Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    exact mul_mem (mul_mem (Formalism.L2.SG.Pf.NcS.IntWittPf.oev_sigR v σ (hx a i)) (hJv i j)) (hx c j)
  have hS : ∀ a c, ((hermOf (Fv F v) σ T hT - GlobalTheory.CompanionTheory.SiegelND.Coef.gramH hCM hJ (Fv F v) X :
      HermR (Fv F v) σ n) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a c ∈
      Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v := by
    intro a c
    exact sub_mem (hTv a c) (hG a c)
  have htrace : ∀ z ∈ Formalism.L2.SG.Pf.NcS.IntWittPf.oevRing (E := E) v,
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) z ∈ v.adicCompletionIntegers F := by
    intro z hz
    rw [hrepr z, map_sum]
    refine sum_mem fun k _ => ?_
    rw [map_smul, GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.trace_one_tmul_len, smul_eq_mul]
    exact mul_mem (hc _ hz k) (htrv k)
  exact ⟨fun i => mul_mem hh (htrace _ (hS i i)), fun i j _ k => hc _ (hS i j) k⟩

end GlobalTheory.CompanionTheory.SiegelND.Coef.Grams
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviNormalizesUnipotentTerStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_normalizes_unipotent_ter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ m ∈ leviMin σ J X Y, ∀ u ∈ unipMin σ J X, m⁻¹ * u * m ∈ unipMin σ J X := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.UnipNormal.leviMin_normalises_unipMin | exact GlobalTheory.CompanionTheory.ParCocompact.UnipNormal.leviMin_normalises_unipMin | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.UnipNormal.leviMin_normalises_unipMin <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviParabolicIntersectionClosedStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_parabolic_intersection_closed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ L : Subgroup (GAd σ J), (L : Set (GAd σ J)) = leviMin σ J X Y ∩ minParOne σ J X ∧ IsClosed (L : Set (GAd σ J)) := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup | exact GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.exists_leviOne_subgroup <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorVectorEq
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.ClozelPurity

theorem EopV_val (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (τ : E →+* ℂ) (i j : Fin a) (φ : π.V) : (EopV π τ i j φ).1 = Eop τ i j φ.1 := by
  simp [EopV, Eop, lieS_apply, CuspSub.op_val, act]

end GlobalTheory.CompanionTheory.ClozelPurity

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationUniqueStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal NNReal Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_gram_fibration_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], GlobalTheory.CompanionTheory.SW.IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → GlobalTheory.CompanionTheory.SW.IsGramFib R σ J n μ ν m → ∀ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), IsUnit g.det → ∃ κ : ℝ≥0, κ ≠ 0 ∧ ∀ S S' : HermR R σ n, (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR R σ) g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g → m S' = κ • (m S).map (fun X => GlobalTheory.CompanionTheory.SW.rmul R X g) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibSch.fib_scale | exact GlobalTheory.CompanionTheory.SW.FibSch.fib_scale | (intros; apply GlobalTheory.CompanionTheory.SW.FibSch.fib_scale <;> assumption)
end

