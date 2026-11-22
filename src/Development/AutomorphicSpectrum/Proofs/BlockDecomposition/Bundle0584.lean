import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0237
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0049
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0014

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulQuotientInvMkEqMkIffMulEquiv
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.IdeleQuot

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {K : Type} [Field K] [NumberField K]

theorem finitePart_apply (s : GroundTheory.Global.IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    ((GlobalTheory.EllipticCM.finitePart (K := K) s : (FiniteAdeleRing (𝓞 K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K) v =
      (GroundTheory.Global.IdeleGroup.finiteProj v s : v.adicCompletion K) := by
  rw [GroundTheory.Global.IdeleGroup.coe_finiteProj]
  rfl

theorem finitePart_inv (s : GroundTheory.Global.IdeleGroup K) :
    GlobalTheory.EllipticCM.finitePart (K := K) s⁻¹ = (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ :=
  map_inv (Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) s

theorem ord_vw_finitePart (s : GroundTheory.Global.IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    GlobalTheory.Idele.ord_vw (GlobalTheory.EllipticCM.finitePart (K := K) s) v =
      GroundTheory.Global.IdeleGroup.ord v s :=
  rfl

theorem coe_smul_eq_finitePart_smul (s : GroundTheory.Global.IdeleGroup K)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      GlobalTheory.EllipticCM.finitePart (K := K) s • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
  GlobalTheory.Idele.eq_of_count_eq (Units.ne_zero _) (GlobalTheory.Idele.smul_ne_zero _ 𝔞.ne_zero) fun v => by
    rw [GroundTheory.Global.IdeleGroup.count_smul, GlobalTheory.Idele.count_smul _ 𝔞.ne_zero, ord_vw_finitePart]

theorem smulQuotient_inv_mk_eq_mk_iff_mulEquiv :
    ∀ {K : Type} [Field K] [NumberField K] (s : GroundTheory.Global.IdeleGroup K)
      (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x y : K),
      GroundTheory.Global.IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk x) =
          Submodule.Quotient.mk y ↔
        GlobalTheory.Idele.mulEquiv (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ 𝔞.ne_zero rfl
          (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  intro K _ _ s 𝔞 x y
  rw [GroundTheory.Global.IdeleGroup.smulQuotient_mk_eq_mk_iff, GlobalTheory.Idele.mulEquiv_mk_eq_mk_iff]
  refine forall_congr' fun v => ?_
  rw [← finitePart_inv, finitePart_apply s⁻¹ v, coe_smul_eq_finitePart_smul]
  rfl

end GlobalTheory.CompanionTheory.IdeleQuot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SocleOfMultiplicityOne
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SocleJm

section General

variable {G V W U : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem jhMult_le_of_injective {σ : Representation ℂ G U} {ρ₁ : Representation ℂ G V}
    {ρ : Representation ℂ G W} (hσ : σ.IsIrreducible) (ι : ρ₁.IntertwiningMap ρ)
    (hι : Function.Injective ι) : jhMult σ ρ₁ ≤ jhMult σ ρ := by
  let R : Subrepresentation ρ := ι.range
  let p : ρ.IntertwiningMap (subQuot ⊤ R) :=
    ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation ρ).toSubmodule LinearMap.id
      (fun _ => trivial), fun _ => rfl⟩
  have hp : ∀ v, p v = 0 ↔ v ∈ R.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
  rw [jhMult_exact ι p hσ hι (fun x => ?_) (fun u => (hp _).2 ⟨u, rfl⟩) (fun v hv => (hp v).1 hv)]
  · exact le_self_add
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨v.1, rfl⟩

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V W U X : Type} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]

theorem jhMult_jac_exact (e : (Σ a, m a) ≃ n) {σ : Representation ℂ (Levi k m) X}
    (hσ : σ.IsIrreducible) {π : Representation ℂ (GL n k) V} {π₁ : Representation ℂ (GL n k) W}
    {π₂ : Representation ℂ (GL n k) U} (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂)
    (hπ : IsSmooth π) (hι : Function.Injective ι) (hp : Function.Surjective p)
    (he : Function.Exact ι p) :
    jhMult σ (jac e π) = jhMult σ (jac e π₁) + jhMult σ (jac e π₂) := by
  refine jhMult_exact (jacMap e ι) (jacMap e p) hσ
    (GlobalTheory.JacInj.jacMap_injective k _ _ _ e W V π₁ π ι hπ hι) (fun x => ?_) (fun x => ?_)
    (fun x hx => ?_)
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨v, rfl⟩ := hp u
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (p (ι u)) = 0
    rw [he.apply_apply_eq_zero]
    rfl
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer π₂ (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := GlobalTheory.SmGL.Exponents.Additive.exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := (he (v - v')).1 (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')

theorem one_le_jhMult_jac (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) {τ : Representation ℂ (GL n k) V} (f : τ.IntertwiningMap (parInd e ρ))
    (hf : ∃ v, f v ≠ 0) : 1 ≤ jhMult ρ (jac e τ) := by
  obtain ⟨v, hv⟩ := hf
  obtain ⟨x, hx⟩ : ∃ x, (f v).1.1 x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv (Subtype.ext (Subtype.ext (funext h)))
  let φ := GlobalTheory.SmGL.Model.evalOne e f
  have h1 : φ (Submodule.Quotient.mk (τ x v)) ≠ 0 := by
    have : φ (Submodule.Quotient.mk (τ x v)) = (f v).1.1 x := by
      show (f (τ x v)).1.1 1 = _
      rw [f.isIntertwining, parInd_apply, one_mul]
    rwa [this]
  have h2 : Function.Surjective φ := by
    intro w
    rcases eq_bot_or_eq_top φ.range with e' | e'
    · have h3 : φ (Submodule.Quotient.mk (τ x v)) ∈ φ.range :=
        (Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨_, rfl⟩
      rw [e'] at h3
      exact absurd h3 h1
    · have h3 : w ∈ φ.range := e' ▸ trivial
      exact (Representation.IntertwiningMap.mem_range _ _ _ _).1 h3
  exact ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (.of_surjective φ h2))

theorem isIrreducible_piTensor (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL k) :
    (piTensor fun a => (x a).rep).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) fun a φ hφ =>
    GlobalTheory.SchurAdm.schur_admissible (GL (Fin (x a).1) k) (KO k (Fin (x a).1)) GlobalTheory.SplitFlip.isOpen_KO
      GlobalTheory.SplitFlip.isCompact_KO _ (x a).rep (x a).2.rep.irr
      (hA k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

theorem exists_isSocle_of_forall_isAtom (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) {π : Representation ℂ (GL n k) V} (hs : IsSmooth π) [Nontrivial V]
    (hfl : HasFiniteLength π)
    (hone : ∀ T : Subrepresentation π, IsAtom T → 1 ≤ jhMult ρ (jac e T.toRepresentation))
    (hjm : jhMult ρ (jac e π) ≤ 1) : ∃ τ : IrrRep (GL n k), IsSocle τ.ρ π := by
  obtain ⟨hGT, hLT⟩ := (hasFiniteLength_iff_wellFounded _).1 hfl
  haveI : IsAtomic (Subrepresentation π) := isAtomic_of_orderBot_wellFounded_lt wellFounded_lt
  have hnt : (⊤ : Subrepresentation π) ≠ ⊥ := fun hb => by
    obtain ⟨u, hu⟩ := exists_ne (0 : V)
    have h1 : u ∈ (⊥ : Subrepresentation π) := hb ▸ trivial
    exact hu h1
  obtain ⟨S, hS, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Subrepresentation π)).resolve_left hnt
  let ι : S.toRepresentation.IntertwiningMap π := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  have huniq : ∀ T : Subrepresentation π, IsAtom T → T = S := by
    intro T hT
    by_contra hne
    have hdis : T ⊓ S = ⊥ := (hT.disjoint_of_ne hS hne).eq_bot
    let p : π.IntertwiningMap (subQuot ⊤ S) :=
      ⟨Submodule.mkQ _ ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation π).toSubmodule
        LinearMap.id (fun _ => trivial), fun _ => rfl⟩
    have hp0 : ∀ v, p v = 0 ↔ v ∈ S.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hps : Function.Surjective p := fun y => by
      obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨v.1, rfl⟩
    have hQ : IsSmooth (subQuot ⊤ S) := (IsSubquotient.of_surjective p hps).isSmooth hs
    have hex : Function.Exact ι p := fun v =>
      ⟨fun h0 => ⟨⟨v, (hp0 v).1 h0⟩, rfl⟩, fun ⟨u, hu⟩ => (hp0 v).2 (hu ▸ u.2)⟩
    have hadd := jhMult_jac_exact e hρ ι p hs Subtype.val_injective hps hex
    let ιT : T.toRepresentation.IntertwiningMap π := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
    have hinj : Function.Injective (p.comp ιT) := by
      refine (injective_iff_map_eq_zero _).2 fun u hu => ?_
      have h1 : (u : V) ∈ S.toSubmodule := (hp0 _).1 hu
      have h2 : (u : V) ∈ (T ⊓ S) := ⟨u.2, h1⟩
      rw [hdis] at h2
      exact Subtype.ext h2
    have h1 : 1 ≤ jhMult ρ (jac e (subQuot ⊤ S)) :=
      (hone T hT).trans (jhMult_le_of_injective hρ (jacMap e (p.comp ιT))
        (GlobalTheory.JacInj.jacMap_injective k _ _ _ e _ _ _ _ _ hQ hinj))
    have h2 : (2 : ℕ∞) ≤ jhMult ρ (jac e π) := by
      rw [hadd]
      exact (by norm_num : (2 : ℕ∞) = 1 + 1).le.trans (add_le_add (hone S hS) h1)
    exact absurd (h2.trans hjm) (by norm_num)
  have hirr := GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom S hS
  refine ⟨⟨S.toSubmodule, S.toRepresentation,
    (IsSubquotient.of_injective ι Subtype.val_injective).isSmooth hs, hirr⟩, hirr, ι,
    Subtype.val_injective, fun T hT => ?_⟩
  rw [huniq T hT]
  refine SetLike.ext fun v => ⟨fun hv => (Representation.IntertwiningMap.mem_range _ _ _ _).2
    ⟨⟨v, hv⟩, rfl⟩, fun hv => ?_⟩
  obtain ⟨u, rfl⟩ := (Representation.IntertwiningMap.mem_range _ _ _ _).1 hv
  exact u.2

theorem nontrivial_indSp (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) (hsρ : IsSmooth ρ) : Nontrivial (IndSp e ρ) := by
  haveI : Nontrivial X := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hρ
  obtain ⟨u, hu⟩ := exists_ne (0 : X)
  obtain ⟨f, hf, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one e ρ hsρ u
  exact ⟨f, 0, fun h => hu (by rw [← hf, h]; rfl)⟩

theorem one_le_jhMult_jac_atom (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) (T : Subrepresentation (parInd e ρ)) (hT : IsAtom T) :
    1 ≤ jhMult ρ (jac e T.toRepresentation) := by
  let ιT : T.toRepresentation.IntertwiningMap (parInd e ρ) := ⟨T.toSubmodule.subtype, fun _ => rfl⟩
  refine one_le_jhMult_jac e hρ ιT ?_
  by_contra hc
  push_neg at hc
  exact hT.1 (Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv =>
    (Submodule.mem_bot ℂ).2 (hc ⟨v, hv⟩)))

theorem exists_isSocle_of_jm_le_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ}
    (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), jm x hd (prodIrr x hd) ≤ 1 →
    ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr x hd) := by
  intro k _ _ _ _ hA h N x hd hjm
  have hρ := isIrreducible_piTensor hA x
  have hsρ : IsSmooth (piTensor fun a => (x a).rep) := isSmooth_piTensor fun a => (x a).2.rep.smooth
  haveI := nontrivial_indSp (stdBlocks (fun a => (x a).1) hd) hρ hsρ
  exact exists_isSocle_of_forall_isAtom (stdBlocks (fun a => (x a).1) hd) hρ
    (isSmooth_parInd _ _)
    (GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ))
    (one_le_jhMult_jac_atom _ hρ) hjm

end GlobalTheory.CompanionTheory.SocleJm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareEuler
section
open Ad3 Ad3.S LSeries
open scoped LSeries.notation ArithmeticFunction.Moebius

namespace GlobalTheory.CompanionTheory.SquareEuler

lemma term_coeff_eq (h1 : N1) {M : ℕ} (c : DirichletCharacter ℂ M) (n : ℤ) (s : ℂ) (d : ℕ) :
    c (d : ZMod M) * RR n d * (d : ℂ) ^ (-(s + 1)) =
      LSeries.term (↗c * ((↗μ : ℕ → ℂ) ⍟ (fun e => (NN n e : ℂ)))) s d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [RR]
  · rw [LSeries.term_of_ne_zero hd.ne', h1 n d hd, LSeries.convolution_def]
    simp only [Pi.mul_apply]
    rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => ((μ a : ℤ) : ℂ) * (NN n b : ℂ))]
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hp : (d : ℂ) ^ (-(s + 1)) = ((d : ℂ) ^ s)⁻¹ * (d : ℂ)⁻¹ := by
      rw [show -(s + 1) = -s + -1 by ring, Complex.cpow_add _ _ hd0, Complex.cpow_neg_one,
        Complex.cpow_neg]
    rw [hp]
    have hds : (d : ℂ) ^ s ≠ 0 := by simp [hd0]
    field_simp

theorem euler_coeff : N1 → N2 → A2 := by
  intro h1 h2 M _ c n s hs
  set N : ℕ → ℂ := fun e => (NN n e : ℂ)
  have hNle : ∀ d : ℕ, d ≠ 0 → ‖N d‖ ≤ d := fun d _ => by
    simp only [N, Complex.norm_natCast]; exact_mod_cast (h2 n).2.1 d
  have hNs : LSeriesSummable N s := by
    refine LSeriesSummable_of_le_const_mul_rpow (x := 2) hs ⟨1, fun d hd => ?_⟩
    have : (d : ℝ) ^ ((2 : ℝ) - 1) = d := by norm_num
    rw [this, one_mul]
    exact hNle d hd
  have hμs : LSeriesSummable (↗μ : ℕ → ℂ) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr (by linarith)
  have hconv : LSeriesSummable ((↗μ : ℕ → ℂ) ⍟ N) s := hμs.convolution hNs
  have hT := DirichletCharacter.LSeriesSummable_mul c hconv
  refine ⟨?_, ?_⟩
  · exact hT.norm.congr fun d => by rw [term_coeff_eq h1 c n s d]
  · have hD : Dn c n s = L (↗c * ((↗μ : ℕ → ℂ) ⍟ N)) s := tsum_congr (term_coeff_eq h1 c n s)
    have hL : DirichletCharacter.LFunction (c ^ 2) (2 * s) = L ↗(c ^ 2) (2 * s) :=
      DirichletCharacter.LFunction_eq_LSeries _ (by rw [Complex.mul_re]; norm_num; linarith)
    rw [hD, hL, mul_comm]
    refine hasProd_moebius_conv_of_norm_le c (N := N) (by simp [N, (h2 n).1]) ?_ hNle hs
    intro a b hab
    simp only [N, (h2 n).2.2.1 a b hab, Nat.cast_mul]

end GlobalTheory.CompanionTheory.SquareEuler
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumRangeGaussLe
section
open Ad3 Ad3.S
open UpperHalfPlane hiding I
open Complex MeasureTheory Filter Topology
open scoped Real

noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaBound

lemma sum_range_gauss_le {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ i ∈ Finset.range N, Real.exp (-a * ((i : ℝ) + 1) ^ 2) ≤ √(π / a) / 2 := by
  have hanti : AntitoneOn (fun t : ℝ => Real.exp (-a * t ^ 2))
      (Set.Icc (0 : ℝ) ((0 : ℝ) + ((N : ℕ) : ℝ))) := by
    intro s hs t ht hst
    apply Real.exp_le_exp.mpr
    have h0 : 0 ≤ s := hs.1
    have h2 : s ^ 2 ≤ t ^ 2 := by nlinarith
    nlinarith
  have h1 := hanti.sum_le_integral
  have h2 : ∫ x in (0 : ℝ)..(0 : ℝ) + (N : ℝ), Real.exp (-a * x ^ 2) ≤
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-a * x ^ 2) := by
    rw [intervalIntegral.integral_of_le (by simp)]
    refine setIntegral_mono_set (integrable_exp_neg_mul_sq ha).integrableOn ?_
      Set.Ioc_subset_Ioi_self.eventuallyLE
    exact Eventually.of_forall fun x => (Real.exp_pos _).le
  rw [integral_gaussian_Ioi] at h2
  refine le_trans (le_of_eq ?_) (h1.trans h2)
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

lemma summable_gauss {a : ℝ} (ha : 0 < a) :
    Summable fun i : ℕ => Real.exp (-a * ((i : ℝ) + 1) ^ 2) :=
  summable_of_sum_range_le (fun _ => (Real.exp_pos _).le) (sum_range_gauss_le ha)

lemma tsum_gauss_le {a : ℝ} (ha : 0 < a) :
    ∑' i : ℕ, Real.exp (-a * ((i : ℝ) + 1) ^ 2) ≤ √(π / a) / 2 :=
  Real.tsum_le_of_sum_range_le (fun _ => (Real.exp_pos _).le) (sum_range_gauss_le ha)

def dom (ν : ℕ) (y : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else y ^ (-(ν : ℝ) / 2) * Real.exp (-(π * y) * (n : ℝ) ^ 2)

lemma dom_add_one (ν : ℕ) (y : ℝ) (i : ℕ) :
    dom ν y ((i : ℤ) + 1) = y ^ (-(ν : ℝ) / 2) * Real.exp (-(π * y) * ((i : ℝ) + 1) ^ 2) := by
  have h : ((i : ℤ) + 1) ≠ 0 := by omega
  simp [dom, h]

lemma dom_neg_add_one (ν : ℕ) (y : ℝ) (i : ℕ) :
    dom ν y (-((i : ℤ) + 1)) = y ^ (-(ν : ℝ) / 2) * Real.exp (-(π * y) * ((i : ℝ) + 1) ^ 2) := by
  have h : -((i : ℤ) + 1) ≠ 0 := by omega
  rw [dom, if_neg h]
  push_cast
  rw [neg_sq]

lemma summable_dom_and_tsum_le (ν : ℕ) {y : ℝ} (hy : 0 < y) :
    Summable (dom ν y) ∧ ∑' n, dom ν y n ≤ y ^ (-((ν : ℝ) + 1) / 2) := by
  have ha : 0 < π * y := mul_pos Real.pi_pos hy
  have hc0 : 0 ≤ y ^ (-(ν : ℝ) / 2) := Real.rpow_nonneg hy.le _
  have HS := ((summable_gauss ha).hasSum).mul_left (y ^ (-(ν : ℝ) / 2))
  have h1 : HasSum (fun i : ℕ => dom ν y ((i : ℤ) + 1))
      (y ^ (-(ν : ℝ) / 2) * ∑' i : ℕ, Real.exp (-(π * y) * ((i : ℝ) + 1) ^ 2)) := by
    simp only [dom_add_one]; exact HS
  have h2 : HasSum (fun i : ℕ => dom ν y (-((i : ℤ) + 1)))
      (y ^ (-(ν : ℝ) / 2) * ∑' i : ℕ, Real.exp (-(π * y) * ((i : ℝ) + 1) ^ 2)) := by
    simp only [dom_neg_add_one]; exact HS
  have H := HasSum.of_add_one_of_neg_add_one h1 h2
  refine ⟨H.summable, ?_⟩
  rw [H.tsum_eq]
  have h0 : dom ν y 0 = 0 := by simp [dom]
  rw [h0, add_zero]
  have hT := tsum_gauss_le ha
  have hq : √(π / (π * y)) = y ^ (-(1 : ℝ) / 2) := by
    have : π / (π * y) = y⁻¹ := by
      field_simp
    rw [this, Real.sqrt_eq_rpow, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le]
    norm_num
  rw [hq] at hT
  have hsplit : y ^ (-((ν : ℝ) + 1) / 2) = y ^ (-(ν : ℝ) / 2) * y ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_add hy]; congr 1; ring
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hT hc0]

lemma norm_ee_sq (n : ℤ) (z : ℂ) :
    ‖ee ((n : ℂ) ^ 2 * z)‖ = Real.exp (-(2 * π * (n : ℝ) ^ 2 * z.im)) := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (n : ℝ) ^ 2 := ⟨_, rfl⟩
  have h : ((n : ℂ) ^ 2) = (r : ℂ) := by rw [hr]; push_cast; rfl
  rw [ee, Complex.norm_exp, h, ← hr]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma pow_mul_exp_le {ν : ℕ} (hν : ν ≤ 1) {y : ℝ} (hy : 0 < y) {m : ℝ} (hm : 0 ≤ m) (hm2 : 1 ≤ m ^ 2) :
    m ^ ν * Real.exp (-(2 * π * m ^ 2 * y)) ≤
      y ^ (-(ν : ℝ) / 2) * Real.exp (-(π * y) * m ^ 2) := by
  have hpi := Real.pi_pos
  have hA : 0 ≤ π * y * m ^ 2 := by positivity
  have hsplit : Real.exp (-(2 * π * m ^ 2 * y)) =
      Real.exp (-(π * y) * m ^ 2) * Real.exp (-(π * y) * m ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  interval_cases ν
  · simp only [pow_zero, Nat.cast_zero, neg_zero, zero_div, Real.rpow_zero, one_mul]
    rw [Real.exp_le_one_iff]
    nlinarith
  · simp only [pow_one, Nat.cast_one]
    set s := √y with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hy
    have hs2 : s ^ 2 = y := Real.sq_sqrt hy.le
    have hr : y ^ (-(1 : ℝ) / 2) = s⁻¹ := by
      rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_neg hy.le]; norm_num
    have hE := Real.add_one_le_exp (π * y * m ^ 2)
    have hEpos := Real.exp_pos (π * y * m ^ 2)
    have hu : m * s ≤ Real.exp (π * y * m ^ 2) := by
      have h3 : (m * s) ^ 2 = y * m ^ 2 := by rw [mul_pow, hs2]; ring
      have h4 : 1 ≤ π := by linarith [Real.pi_gt_three]
      have h5 : 0 ≤ y * m ^ 2 := by positivity
      nlinarith [sq_nonneg (m * s - 1), mul_le_mul_of_nonneg_right h4 h5]
    rw [hr, neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hEpos, inv_mul_eq_div,
      le_div_iff₀ hs0]
    exact hu

lemma term_le {P : ℤ → ℂ} {ν : ℕ} (hν : ν ≤ 1) (hP0 : P 0 = 0) (hP1 : ∀ n, ‖P n‖ ≤ 1) {y : ℝ}
    (hy : 0 < y) {z : ℂ} (hz : y ≤ z.im) (n : ℤ) :
    ‖P n * (n : ℂ) ^ ν * ee ((n : ℂ) ^ 2 * z)‖ ≤ dom ν y n := by
  by_cases hn : n = 0
  · subst hn
    simp [hP0, dom]
  rw [dom, if_neg hn, norm_mul, norm_mul, norm_pow, norm_ee_sq]
  have hm : ‖(n : ℂ)‖ = |(n : ℝ)| := by simp
  have hsq : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
  have hn1 : 1 ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ n ^ 2 := by
      have := Int.one_le_abs hn
      nlinarith [sq_abs n, abs_nonneg n]
    exact_mod_cast this
  have key := pow_mul_exp_le hν hy (abs_nonneg (n : ℝ)) (by rw [hsq]; exact hn1)
  rw [hsq] at key
  rw [hm]
  have hmono : Real.exp (-(2 * π * (n : ℝ) ^ 2 * z.im)) ≤ Real.exp (-(2 * π * (n : ℝ) ^ 2 * y)) := by
    apply Real.exp_le_exp.mpr
    have : 0 ≤ 2 * π * (n : ℝ) ^ 2 := by positivity
    nlinarith
  calc ‖P n‖ * |(n : ℝ)| ^ ν * Real.exp (-(2 * π * (n : ℝ) ^ 2 * z.im))
      ≤ 1 * |(n : ℝ)| ^ ν * Real.exp (-(2 * π * (n : ℝ) ^ 2 * y)) := by
        gcongr
        exact hP1 n
    _ ≤ _ := by rw [one_mul]; exact key

theorem b2 : B2 := by
  intro P ν hν hP0 hP1
  refine ⟨?_, ?_, ?_, 1, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro z0
    have hε : 0 < z0.im / 2 := half_pos z0.im_pos
    have hU : IsOpen {z : ℍ | z0.im / 2 < z.im} :=
      isOpen_lt continuous_const (Complex.continuous_im.comp UpperHalfPlane.continuous_coe)
    have hc : ContinuousOn (fun z : ℍ => th P ν z) {z : ℍ | z0.im / 2 < z.im} := by
      unfold th
      refine continuousOn_tsum (u := dom ν (z0.im / 2)) (fun n => ?_) (summable_dom_and_tsum_le ν hε).1
        (fun n z hz => term_le hν hP0 hP1 hε (le_of_lt hz) n)
      apply Continuous.continuousOn
      unfold ee
      have := UpperHalfPlane.continuous_coe
      fun_prop
    exact hc.continuousAt (hU.mem_nhds (by
      show z0.im / 2 < z0.im
      linarith [z0.im_pos]))
  · intro z
    unfold th
    refine tsum_congr fun n => ?_
    congr 1
    rw [UpperHalfPlane.coe_vadd]
    have hint : ee ((n : ℂ) ^ 2 * (((1 : ℝ) : ℂ) + (z : ℂ))) = ee ((n : ℂ) ^ 2 * z) * ee ((n : ℂ) ^ 2) := by
      unfold ee
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have h1 : ee ((n : ℂ) ^ 2) = 1 := by
      unfold ee
      have := Complex.exp_int_mul_two_pi_mul_I (n ^ 2)
      rw [← this]
      congr 1
      push_cast
      ring
    rw [hint, h1, mul_one]
  · intro z
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (term_le hν hP0 hP1 z.im_pos le_rfl) (summable_dom_and_tsum_le ν z.im_pos).1
  · intro z
    have hs := summable_dom_and_tsum_le ν z.im_pos
    have hsum : Summable fun n : ℤ => ‖P n * (n : ℂ) ^ ν * ee ((n : ℂ) ^ 2 * z)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (term_le hν hP0 hP1 z.im_pos le_rfl) hs.1
    rw [one_mul]
    calc ‖th P ν z‖ ≤ ∑' n : ℤ, ‖P n * (n : ℂ) ^ ν * ee ((n : ℂ) ^ 2 * z)‖ :=
          norm_tsum_le_tsum_norm hsum
      _ ≤ ∑' n, dom ν z.im n :=
          hsum.tsum_le_tsum (term_le hν hP0 hP1 z.im_pos le_rfl) hs.1
      _ ≤ _ := hs.2

end GlobalTheory.CompanionTheory.ThetaBound
end
end

