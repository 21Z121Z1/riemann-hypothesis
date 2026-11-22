import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralMulConjEqOfLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0744
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0504

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionMemSpanLevelTypeDifferences
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite.TypeSpan

variable {D : D7} {V W : HSp D}

theorem levChi_mul' {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} {k k' : GA D V}
    (hk : k ∈ levG V β L) (hk' : k' ∈ levG V β L) :
    levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  have e := (Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩
  have e' : Formalism.L2.DIV.levFn β L (finE V k * finE V k') =
      Formalism.L2.DIV.levFn β L (finE V k) * Formalism.L2.DIV.levFn β L (finE V k') := e
  unfold levChi
  rw [map_mul, e', Units.val_mul]

theorem levChi_ne_zero (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (k : GA D V) :
    levChi V β L k ≠ 0 := by
  unfold levChi
  exact Units.ne_zero _

theorem eventually_levChi_one (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) :
    ∀ᶠ κ in nhds (1 : GA D V), levChi V β L κ = 1 := by
  classical
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨-, -, h3⟩ := hh
  unfold levChi
  rw [GlobalTheory.LevSplit.levFn_eq_one β L _ fun PP hP => h3 PP (by rcases hP with h | h <;> simp [h]), Units.val_one]

end GlobalTheory.DownLift.GenFinite.TypeSpan

namespace GlobalTheory.DownLift.GenFinite

open GlobalTheory.DownLift.GenFinite.TypeSpan

theorem typeSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → f ∈ Submodule.span ℂ ({φ | GlobalTheory.DownLift.GenFinite.TypeVec R i t φ} ∪ GlobalTheory.DownLift.GenFinite.TypeDiff R i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ hP i t f hf
  classical
  have hW := (hP i t).datum
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig (Vc D i).gram
  obtain ⟨U, U', hUo, -, hfix⟩ := GlobalTheory.Mem.ThetaLevel.exists_level D R.ψ hW.std (Vc D i) (Wc D i) (R.ωP i t)
    (GlobalTheory.Ker.isWeak_of_datum hW) hW.om_cont f hf
  set J := levG (Vc D i) (R.βV i) (R.datVt i t) with hJ
  set lam := levChi (Vc D i) (R.βV i) (R.datVt i t) with hlam
  set om := R.ωP i t with hom
  have hmul : ∀ a b : GA D (Vc D i), om (a * b, 1) = om (a, 1) * om (b, 1) := fun a b => by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hone : om (1, 1) = 1 := by rw [← Prod.one_eq_mk, map_one]
  have hlm : ∀ {a b : GA D (Vc D i)}, a ∈ J → b ∈ J → lam (a * b) = lam a * lam b := fun ha hb => levChi_mul' ha hb
  have hlne : ∀ a : GA D (Vc D i), lam a ≠ 0 := fun a => levChi_ne_zero _ _ a
  have hlam1 : lam 1 = 1 := by
    have e := hlm (one_mem J) (one_mem J)
    rw [mul_one] at e
    have h0 := hlne 1
    have e' : lam 1 * 1 = lam 1 * lam 1 := by rw [mul_one]; exact e
    exact (mul_left_cancel₀ h0 e').symm

  let N : Subgroup J :=
    { carrier := {κ | om ((κ : GA D (Vc D i)), 1) f = f ∧ lam κ = 1}
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨?_, ?_⟩
        · show om ((a : GA D (Vc D i)) * b, 1) f = f
          rw [hmul, Module.End.mul_apply, hb1, ha1]
        · show lam ((a : GA D (Vc D i)) * b) = 1
          rw [hlm a.2 b.2, ha2, hb2, one_mul]
      one_mem' := by
        refine ⟨?_, ?_⟩
        · show om (1, 1) f = f
          rw [hone]; rfl
        · exact hlam1
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        refine ⟨?_, ?_⟩
        · show om ((a : GA D (Vc D i))⁻¹, 1) f = f
          conv_lhs => rw [← ha1]
          rw [← Module.End.mul_apply, ← hmul, inv_mul_cancel, hone]; rfl
        · show lam ((a : GA D (Vc D i))⁻¹) = 1
          have e := hlm (inv_mem a.2) a.2
          rw [inv_mul_cancel, hlam1, ha2, mul_one] at e
          exact e.symm }
  have hNo : IsOpen (N : Set J) := by
    refine Subgroup.isOpen_of_mem_nhds N (g := 1) ?_
    have h1 : {x : GA D (Vc D i) | x ∈ U ∧ lam x = 1} ∈ nhds (1 : GA D (Vc D i)) :=
      Filter.inter_mem (hUo.mem_nhds U.one_mem) (eventually_levChi_one _ _)
    have h2 := (continuous_subtype_val (p := fun x => x ∈ J)).continuousAt (x := (1 : J)).preimage_mem_nhds h1
    exact Filter.mem_of_superset h2 fun κ hκ => ⟨hfix _ hκ.1 κ.2.1 1 U'.one_mem (one_mem _), hκ.2⟩
  haveI : CompactSpace J := isCompact_iff_compactSpace.mp (GlobalTheory.ParahoricCompact.isCompact_levG _ _ _)
  haveI : Finite (J ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNo
  letI : Fintype (J ⧸ N) := Fintype.ofFinite _

  let Fv : J → (WO (Vc D i) (Wc D i) → ℂ) := fun κ => lam κ • om ((κ : GA D (Vc D i)), 1) f
  have hFvN : ∀ (a n : J), n ∈ N → Fv (a * n) = Fv a := by
    rintro a n ⟨hn1, hn2⟩
    show lam ((a : GA D (Vc D i)) * n) • om ((a : GA D (Vc D i)) * n, 1) f = lam a • om ((a : GA D (Vc D i)), 1) f
    rw [hlm a.2 n.2, hn2, mul_one, hmul, Module.End.mul_apply, hn1]
  let Fb : J ⧸ N → (WO (Vc D i) (Wc D i) → ℂ) := fun q => Fv q.out
  have hFb : ∀ κ : J, Fb (κ : J ⧸ N) = Fv κ := by
    intro κ
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N κ
    show Fv (κ : J ⧸ N).out = Fv κ
    rw [hn]
    exact hFvN κ n n.2
  have hFbTh : ∀ q, IsThetaFunO R.ψ (Vc D i) (Wc D i) (Fb q) := fun q =>
    theta_smul _ (hW.om_pres _ _ hf)

  have hact : ∀ (κ' : J) (q : J ⧸ N), om ((κ' : GA D (Vc D i)), 1) (Fb q) = (lam κ')⁻¹ • Fb (κ' • q) := by
    intro κ' q
    induction q using QuotientGroup.induction_on with
    | H κ =>
      rw [MulAction.Quotient.smul_mk, hFb, hFb]
      show om ((κ' : GA D (Vc D i)), 1) (lam κ • om ((κ : GA D (Vc D i)), 1) f) =
        (lam κ')⁻¹ • (lam ((κ' : GA D (Vc D i)) * κ) • om ((κ' : GA D (Vc D i)) * κ, 1) f)
      rw [map_smul, hmul, Module.End.mul_apply, hlm κ'.2 κ.2, smul_smul, ← mul_assoc,
        inv_mul_cancel₀ (hlne _), one_mul]
  set c : ℂ := ((Fintype.card (J ⧸ N) : ℕ) : ℂ)⁻¹ with hc
  set fJ := c • ∑ q, Fb q with hfJ
  have hfJv : TypeVec R i t fJ := by
    refine ⟨theta_smul _ (theta_sum Finset.univ Fb f hf fun q _ => hFbTh q), fun κ hκ => ?_⟩
    show om (κ, 1) fJ = (lam κ)⁻¹ • fJ
    have e : om (κ, 1) (∑ q, Fb q) = (lam κ)⁻¹ • ∑ q, Fb q := by
      rw [map_sum]
      have := fun q => hact ⟨κ, hκ⟩ q
      simp only [] at this
      rw [Finset.sum_congr rfl fun q _ => this q, ← Finset.smul_sum]
      congr 1
      exact Equiv.sum_comp (MulAction.toPerm (⟨κ, hκ⟩ : J)) Fb
    rw [hfJ, map_smul, e, smul_comm]
  have hdiff : ∀ q, f - Fb q ∈ Submodule.span ℂ ({φ | TypeVec R i t φ} ∪ TypeDiff R i t) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H κ =>
      rw [hFb]
      have e : f - Fv κ = (-lam κ) • (om ((κ : GA D (Vc D i)), 1) f - (lam κ)⁻¹ • f) := by
        show f - lam κ • om ((κ : GA D (Vc D i)), 1) f = _
        rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ (hlne _)]
        simp only [neg_smul, one_smul]
        abel
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨κ, κ.2, f, hf, rfl⟩))
  have hcard : ((Fintype.card (J ⧸ N) : ℕ) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card (J ⧸ N) := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsplit : f = fJ + c • ∑ q, (f - Fb q) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      hc, inv_mul_cancel₀ hcard, one_smul, hfJ]
    abel
  rw [hsplit]
  exact Submodule.add_mem _ (Submodule.subset_span (Or.inl hfJv))
    (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => hdiff q))

end GlobalTheory.DownLift.GenFinite

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionMemSpanOfCoefficientSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef.Decomp

variable {D : D7}

theorem heisO_lin_sub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T x (f - g) = heisO ψ S T x f - heisO ψ S T x g := by
  rw [← GlobalTheory.SplitScalar.heisL_apply, map_sub]; rfl

theorem heisO_lin_add (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T x (f + g) = heisO ψ S T x f + heisO ψ S T x g := by
  rw [← GlobalTheory.SplitScalar.heisL_apply, map_add]; rfl

theorem heisO_lin_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (x : WO S T) :
    heisO ψ S T x (0 : WO S T → ℂ) = 0 := by
  rw [← GlobalTheory.SplitScalar.heisL_apply, map_zero]

theorem theta_of_mem_span {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {𝒯 : Set (WO S T → ℂ)}
    (h0 : IsThetaFunO ψ S T 0) (h𝒯 : ∀ φ ∈ 𝒯, IsThetaFunO ψ S T φ) {φ : WO S T → ℂ} (hφ : φ ∈ Submodule.span ℂ 𝒯) : IsThetaFunO ψ S T φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact h𝒯 x hx
  | zero => exact h0
  | add x y _ _ hx hy => exact theta_add hx hy
  | smul c x _ hx => exact theta_smul c hx

theorem exists_decomp (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (a : AE D) (f : WO S T → ℂ) (X : Finset (WO S T))
    (hX : ∀ x, IsHalf a x → (∀ ℓ, InvForm ψ S T a ℓ → ℓ (heisO ψ S T x f) = 0) ∨
      ∃ x₁ ∈ X, heisO ψ S T x f = heisO ψ S T x₁ f) :
    ∃ L : WO S T → ((WO S T → ℂ) →ₗ[ℂ] ℂ), (∀ x₁, InvForm ψ S T a (L x₁)) ∧
      ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x →
        ℓ (heisO ψ S T x f) = ∑ x₁ ∈ X, L x₁ (heisO ψ S T x f) * ℓ (heisO ψ S T x₁ f) := by
  classical
  let K : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ
    {h | ∃ u g, IsHalf (cA D a) u ∧ IsThetaFunO ψ S T g ∧ h = heisO ψ S T u g - g}
  have inv_iff : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, InvForm ψ S T a ℓ ↔ K ≤ LinearMap.ker ℓ := by
    intro ℓ
    constructor
    · intro hℓ
      rw [Submodule.span_le]
      rintro h ⟨u, g, hu, hg, rfl⟩
      simp [LinearMap.mem_ker, map_sub, hℓ u hu g hg]
    · intro hle u hu g hg
      have := hle (Submodule.subset_span ⟨u, g, hu, hg, rfl⟩)
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
      exact this
  have inv_comp : ∀ μ : ((WO S T → ℂ) ⧸ K) →ₗ[ℂ] ℂ, InvForm ψ S T a (μ ∘ₗ K.mkQ) := by
    intro μ
    rw [inv_iff]
    intro h hh
    simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero K).2 hh]
  let Fq : WO S T → (WO S T → ℂ) ⧸ K := fun x => K.mkQ (heisO ψ S T x f)
  let A : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) ⧸ K :=
    ∑ x₁ ∈ X, (LinearMap.proj x₁ : (WO S T → ℂ) →ₗ[ℂ] ℂ).smulRight (Fq x₁)
  have hA : ∀ c, A c = ∑ x₁ ∈ X, c x₁ • Fq x₁ := by
    intro c
    simp [A, LinearMap.sum_apply]
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range A).subtype (Submodule.ker_subtype _)
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective A.rangeRestrict (LinearMap.range_rangeRestrict A)
  let s := g ∘ₗ p
  have hs : ∀ q ∈ LinearMap.range A, A (s q) = q := by
    intro q hq
    have h1 : p q = ⟨q, hq⟩ := by
      have := LinearMap.congr_fun hp ⟨q, hq⟩
      simpa using this
    have h2 := LinearMap.congr_fun hg (p q)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
    have h3 : A (g (p q)) = ((A.rangeRestrict (g (p q)) : LinearMap.range A) : (WO S T → ℂ) ⧸ K) := rfl
    simp only [s, LinearMap.comp_apply]
    rw [h3, h2, h1]
  refine ⟨fun x₁ => (LinearMap.proj x₁ ∘ₗ s) ∘ₗ K.mkQ, fun x₁ => inv_comp _, ?_⟩
  intro ℓ hℓ x hx
  have hle := (inv_iff ℓ).1 hℓ
  have hmem : Fq x ∈ LinearMap.range A := by
    rcases hX x hx with h0 | ⟨x₁, hx₁, he⟩
    · have : Fq x = 0 := by
        rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
        intro μ
        exact h0 (μ ∘ₗ K.mkQ) (inv_comp μ)
      rw [this]
      exact Submodule.zero_mem _
    · refine ⟨Pi.single x₁ 1, ?_⟩
      rw [hA, Finset.sum_eq_single x₁]
      · simp [Fq, he]
      · intro b _ hb
        simp [Pi.single_apply, hb]
      · intro h
        exact absurd hx₁ h
  have key := congrArg (K.liftQ ℓ hle) (hs _ hmem)
  rw [hA, map_sum] at key
  simp only [map_smul, smul_eq_mul] at key
  have hb : ∀ y, K.liftQ ℓ hle (Fq y) = ℓ (heisO ψ S T y f) := fun y => rfl
  simp only [hb] at key
  rw [← key]
  rfl

theorem mem_span_of_coef_mem_span : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ 𝒢 𝒯 : Set (WO S T → ℂ), (∀ φ ∈ 𝒯, IsThetaFunO ψ S T φ) → (∀ Ψ ∈ 𝒢, ∀ x₁, IsHalf a x₁ → ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x φ) = Ψ x * ℓ (heisO ψ S T x₁ f)) → (∀ ℓ, InvForm ψ S T a ℓ → coef ψ S T a ℓ f ∈ Submodule.span ℂ 𝒢) → f ∈ Submodule.span ℂ 𝒯 := by
  intro D ψ S T hψ a ha f hf 𝒢 𝒯 h𝒯 h𝒢 hcoef
  obtain ⟨-, -, X, hXh, hX⟩ := GlobalTheory.T.thetaCoefficient_isSchwartzBruhat_uniform_split D ψ S T hψ (GlobalTheory.PlaceModel.latFrame S) (GlobalTheory.PlaceModel.latFrame T)
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T) a ha f hf
  obtain ⟨L, hLinv, hL⟩ := exists_decomp ψ S T a f X hX
  have hspan : ∀ Ψ ∈ Submodule.span ℂ 𝒢, ∀ x₁, IsHalf a x₁ → ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ →
      ∀ x, IsHalf a x → ℓ (heisO ψ S T x φ) = Ψ x * ℓ (heisO ψ S T x₁ f) := by
    intro Ψ hΨ x₁ hx₁
    induction hΨ using Submodule.span_induction with
    | mem Ψ hΨ => exact h𝒢 Ψ hΨ x₁ hx₁
    | zero => exact ⟨0, Submodule.zero_mem _, fun ℓ _ x _ => by simp [heisO_lin_zero]⟩
    | add Ψ₁ Ψ₂ _ _ h1 h2 =>
      obtain ⟨φ₁, m1, e1⟩ := h1
      obtain ⟨φ₂, m2, e2⟩ := h2
      refine ⟨φ₁ + φ₂, add_mem m1 m2, fun ℓ hℓ x hx => ?_⟩
      rw [heisO_lin_add, map_add, e1 ℓ hℓ x hx, e2 ℓ hℓ x hx, Pi.add_apply, add_mul]
    | smul c Ψ _ h =>
      obtain ⟨φ, m, e⟩ := h
      refine ⟨c • φ, Submodule.smul_mem _ c m, fun ℓ hℓ x hx => ?_⟩
      rw [GlobalTheory.SplitScalar.heisO_smul, map_smul, e ℓ hℓ x hx, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  have hφ : ∀ x₁ ∈ X, ∃ φ ∈ Submodule.span ℂ 𝒯, ∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x →
      ℓ (heisO ψ S T x φ) = coef ψ S T a (L x₁) f x * ℓ (heisO ψ S T x₁ f) :=
    fun x₁ hx₁ => hspan _ (hcoef _ (hLinv x₁)) x₁ (hXh x₁ hx₁)
  choose! φ hφm hφe using hφ
  have hsum : (∑ x₁ ∈ X, φ x₁) ∈ Submodule.span ℂ 𝒯 := Submodule.sum_mem _ hφm
  have h0 : IsThetaFunO ψ S T 0 := by simpa using theta_sub hf hf
  have hzero := GlobalTheory.T.splitPlace_invariantForms_separate_thetaFunctions D ψ S T hψ a ha (f - ∑ x₁ ∈ X, φ x₁)
    (theta_sub hf (theta_of_mem_span h0 h𝒯 hsum)) (by
      intro ℓ hℓ x hx
      rw [heisO_lin_sub, GlobalTheory.SplitScalar.heisO_sum, map_sub, map_sum, hL ℓ hℓ x hx, sub_eq_zero]
      refine Finset.sum_congr rfl fun x₁ hx₁ => ?_
      rw [hφe x₁ hx₁ ℓ hℓ x hx, coef, if_pos hx])
  rw [sub_eq_zero] at hzero
  exact hzero ▸ hsum

end GlobalTheory.DownLift.SplitCoef.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterLadicGaloisCharacterEqHecke
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeriesTie

theorem charOf_psiAt_chrEq : ∀ (D : D7) (a : Recip D D.nd.Om) (i : D.ntw.Tw) (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ) (χ : Formalism.L2.Host.HChar D.host.E) (r : G D.host.E D.nd.Om →* (D.ntw.O0 i)ˣ) (b : Bool), a.Good → IsOpen (r.ker : Set (G D.host.E D.nd.Om)) → GlobalTheory.GalChar.IsGal a.art κ ι χ (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r) → ∀ (f : D.ntw.O0 i →+* ℂ), (∀ y, IsIntegral ℤ y → f y = ι (κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y))) → ∀ (ch : Set (Pl D.host.E)) (Q : Finset (Pl D.host.E)), ChrEq (twistOf a f ch Q (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r)).chi χ := by
  intro D a i κ ι χ r b ha hr hg f hf ch Q
  set ψ := Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b r with hψdef
  have hker : ψ.ker = r.ker := by
    cases b
    · ext σ
      simp [hψdef, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
    · simp [hψdef, Formalism.MainNotions.BlochKatoReduction.Gen.psiAt]
  have hop : IsOpen (ψ.ker : Set (G D.host.E D.nd.Om)) := hker ▸ hr
  have hfi : ψ.ker.FiniteIndex := by
    let H : OpenNormalSubgroup (G D.host.E D.nd.Om) := { toSubgroup := ψ.ker, isOpen' := hop, isNormal' := inferInstance }
    exact inferInstanceAs (OpenNormalSubgroup.toFiniteIndexNormalSubgroup H).toSubgroup.FiniteIndex
  have hn : ψ.ker.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hpow : ∀ σ, ψ σ ^ ψ.ker.index = 1 := fun σ => by
    rw [← map_pow]
    exact ψ.mem_ker.1 (Subgroup.pow_index_mem _ σ)
  have key : ∀ (x : (AE D)ˣ) (σ : G D.host.E D.nd.Om), a.sym x = toAb D.host.E D.nd.Om σ →
      ((charOf a f ψ x : Circle) : ℂ) = ((χ.1 (Units.map a.κ.toMonoidHom x) : ℂˣ) : ℂ) := by
    intro x σ hx
    rw [charOf_eq a f hop hx hn (hpow σ)]
    have hint : IsIntegral ℤ ((ψ σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) :=
      IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (by
        rw [← Units.val_pow_eq_pow_val, hpow σ, Units.val_one]
        exact isIntegral_one)
    rw [hf _ hint]
    have h1 := hg.2.2 (Units.map a.κ.toMonoidHom x) σ hx
    simp [GlobalTheory.GalChar.inQ, GlobalTheory.GalChar.toQ, GlobalTheory.HeckeGal.infPow, GlobalTheory.HeckeGal.lPow, GlobalTheory.HeckeGal.locPow] at h1
    rw [h1]
    simp

  have hsymc : Continuous a.sym :=
    ha.artin.quot.continuous.comp (Continuous.units_map _ ha.cont)
  have hdesc : IsOpen (((descend ψ : Gab D.host.E D.nd.Om →* (D.ntw.O0 i)ˣ).ker : Set (Gab D.host.E D.nd.Om))) := by
    have hpre : (toAb D.host.E D.nd.Om) ⁻¹' ((descend ψ).ker : Set (Gab D.host.E D.nd.Om)) = (ψ.ker : Set _) := by
      ext σ
      simp [descend_toAb hop]
    have hs : Function.Surjective (toAb D.host.E D.nd.Om) := QuotientGroup.mk'_surjective _
    rw [← Set.image_preimage_eq ((descend ψ).ker : Set (Gab D.host.E D.nd.Om)) hs, hpre]
    exact QuotientGroup.isOpenMap_coe _ hop
  have hpullo : IsOpen (((a.pull ψ).ker : Set (AE D)ˣ)) := by
    have : ((a.pull ψ).ker : Set (AE D)ˣ) = a.sym ⁻¹' ((descend ψ).ker : Set _) := by
      ext x
      simp [Recip.pull]
    rw [this]
    exact hdesc.preimage hsymc
  refine ⟨⟨?_, fun k => ?_⟩, fun P e he k x hx => ?_⟩
  · refine continuous_of_continuousAt_one (charOf a f ψ) ?_
    refine ContinuousAt.congr (continuousAt_const (y := (1 : Circle))) (Filter.eventuallyEq_of_mem (hpullo.mem_nhds (map_one _)) fun x hx => ?_)
    change (1 : Circle) = charOf a f ψ x
    rw [charOf, MonoidHom.comp_apply, MonoidHom.comp_apply, (a.pull ψ).mem_ker.1 hx, map_one, map_one]
  · have hs : a.sym (Units.map (incA D).toMonoidHom k) = 1 := by
      change a.art (Units.map a.κ.toMonoidHom (Units.map (incA D).toMonoidHom k)) = 1
      rw [← MonoidHom.mem_ker, ha.artin.ker]
      apply Subgroup.le_topologicalClosure
      apply Subgroup.mem_sup_left
      exact ⟨k, Units.ext (ha.rat k).symm⟩
    change unitPart (Units.map f.toMonoidHom (descend ψ (a.sym (Units.map (incA D).toMonoidHom k)))) = 1
    rw [hs, map_one, map_one, map_one]
  · obtain ⟨σ, hσ⟩ := a.exists_sym x
    have hy : Units.map a.κ.toMonoidHom x =
        Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) :=
      Units.ext ((congrArg a.κ hx).trans (ha.loc P e he k))
    change ((charOf a f ψ x : Circle) : ℂ) = _
    rw [key x σ hσ, hy]
    rfl
end GlobalTheory.SeriesTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.MirTower
open scoped ENNReal NNReal ComplexConjugate

namespace GlobalTheory.MirTower

theorem unfold_mirabolic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) [MeasurableSpace (GA E a)] [BorelSpace (GA E a)] (μ : Measure (GA E a)) [μ.IsHaarMeasure] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (𝓕 𝓕₀ : Set (GA E a)), IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕 μ → IsFundamentalDomain (ratMirU E a 0) 𝓕₀ μ → ∀ (w : GA E a → ℝ≥0), Measurable w → (∀ γ ∈ mirU E a (a - 1), ∀ g, w (ratGL E a γ * g) = w g) → (∀ (k : ℕ) (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), w (blkU y * g) = w g) → (∀ f, Good ψ (a - 1) f → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ = ∫⁻ g in 𝓕₀, ‖whit ψ (a - 1) f g‖ₑ ^ 2 * w g ∂μ) ∧ ∀ f f', Good ψ (a - 1) f → Good ψ (a - 1) f' → ∫⁻ g in 𝓕, ‖f g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → ∫⁻ g in 𝓕, ‖f' g‖ₑ ^ 2 * w g ∂μ ≠ ⊤ → IntegrableOn (fun g => f g * conj (f' g) * (w g : ℝ)) 𝓕 μ ∧ IntegrableOn (fun g => whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ)) 𝓕₀ μ ∧ ∫ g in 𝓕, f g * conj (f' g) * (w g : ℝ) ∂μ = ∫ g in 𝓕₀, whit ψ (a - 1) f g * conj (whit ψ (a - 1) f' g) * (w g : ℝ) ∂μ := by
  intro E _ _ a _ _ μ _ ψ hψ 𝓕 𝓕₀ h𝓕 h𝓕₀ w hw hwΓ hwU

  have hm : a - 1 < a ∨ a - 1 = 0 := by omega

  have : SecondCountableTopology (GA E a) := secondCountable_GA

  have : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Ad E))
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (GA E a) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SFinite μ := inferInstance
  refine ⟨fun f hf => ?_, fun f f' hf hf' h1 h2 => ?_⟩
  · exact lintegral_tower μ hψ hm h𝓕 h𝓕₀ (fun g => (w g : ℝ≥0∞)) (by fun_prop)
      (fun γ hγ g => by simp only [hwΓ γ hγ g]) (fun k _ y g => by simp only [hwU k y g]) hf
  · exact integral_tower μ hψ hm h𝓕 h𝓕₀ w hw hwΓ (fun k _ y g => hwU k y g) hf hf' h1 h2

end GlobalTheory.MirTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L), (∀ g : GAf L n, ∃ x y : GAf L n, TrivOutside {s.v} x ∧ TrivOutside {s.v}ᶜ y ∧ g = x * y) ∧ (∀ x y : GAf L n, TrivOutside {s.v} x → TrivOutside {s.v}ᶜ y → Commute x y) ∧ (∀ A : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)), ∃! x : GAf L n, TrivOutside {s.v} x ∧ s.loc n x = A) := by
  first | exact @GlobalTheory.SplitAdelic.main | exact GlobalTheory.SplitAdelic.main | (intros; apply GlobalTheory.SplitAdelic.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedForms
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.NL

theorem usedLocalConclusion_and_prvE : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), DeltaInvariantLattices.UsedLocalConclusion D HW F Cm ∧ DeltaInvariantLattices.ConclusionE D HW F := by
  intro D HW F Cm
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, c2, a, b, c, d, l3, hE⟩ := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  refine ⟨⟨fun l _ K s LL g => ⟨p1 l K s LL g, p2 l K s LL g, p3 l K s LL g, p4 l K s LL g, p5 l K s LL g,
    p6 l K s LL g, p7 l K s LL g, p8 l K s LL g, p9 l K s LL g, p10 l K s LL g⟩, c2,
    (DeltaInvariantLattices.herr_prop_two_iff D HW F).2 ⟨a, b, c, d⟩, l3⟩, hE⟩

end GlobalTheory.NL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneAbove
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

namespace GlobalTheory.WDAboveProof

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → WDAbove D := by
  intro D hT h1 h2 h5 i r hr x PI hPx w hw hsp
  obtain ⟨Pa, hB⟩ := h1 i PI
  obtain ⟨ρ, hρc, hρs, hρw⟩ := GlobalTheory.T.exists_galois_rep_base_change_twist D hT h2 i PI Pa hB
  obtain ⟨Pm, hPm⟩ := GlobalTheory.BaseChangeConj.rep_conj_of_baseChange D h5 i r hr x PI Pa hPx hB ρ hρc hρs
    (fun w' _ => (hρw w').2)
  have hc := (hT.2.2.2.2.2 i).2.1 D.R.nV ρ _ hρc Pm hPm
  have hdR : D.naut.IsdRW i ρ w := ((hρw w).1).resolve_left (not_not.2 hw)
  refine ⟨(hc.1 w hw).2 hdR, ?_⟩
  rw [hc.2.1 w (hρw w).1, (hρw w).2, hB.2.2.2.1 w hsp]

end GlobalTheory.WDAboveProof
end

