import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KHighestEqSmulOfMinusKilled
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOrthSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0624
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightIsoOfEqualCasimir
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.LowGen

variable {p q : ℕ}

theorem mem_hwSub {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (μ : Ix p q → ℚ) (x : V) : x ∈ hwSub act μ ↔
      (∀ a, act (Eab a a) x = ((μ a : ℚ) : ℂ) • x) ∧ ∀ a b, posC a b → act (Eab a b) x = 0 := by
  simp [hwSub, wtSub, Submodule.mem_iInf, sub_eq_zero]

theorem genSub_stable {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (S : Set V) (Z : Mat p q) : ∀ y ∈ genSub act S, act Z y ∈ genSub act S := by
  intro y hy
  rw [genSub, Submodule.mem_sInf] at hy ⊢
  exact fun N hN => hN.2 Z y (hy N hN)

theorem mem_genSub_self {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (u : V) : u ∈ genSub act {u} := by
  rw [genSub, Submodule.mem_sInf]
  exact fun N hN => hN.1 rfl

theorem genSub_le {V : Type} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    {u : V} {N : Submodule ℂ V} (hu : u ∈ N) (hN : ∀ Z, ∀ y ∈ N, act Z y ∈ N) : genSub act {u} ≤ N :=
  sInf_le ⟨Set.singleton_subset_iff.2 hu, hN⟩

theorem gen_irred_adm {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (hlie : IsLieAct act) (ip : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (herm : ∀ x y, star (ip x y) = ip y x) (pos : ∀ x, x ≠ 0 → 0 < (ip x x).re)
    (hadj : ∀ Z x y, ip (act Z x) y = ip x (act (adjZ Z) y))
    {lam : Ix p q → ℚ} (hl : IsParam lam) (hg1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1))
    (hg2 : GapGt lam (((p + q : ℕ) : ℝ) - 1)) (u : V)
    (hfin : ∃ W : Submodule ℂ V, FiniteDimensional ℂ W ∧ u ∈ W ∧ KStable act W)
    (hu : u ∈ hwSub act (blattner lam))
    (hc : casimir act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u) :
    (∀ Q : Submodule ℂ V, Q ≤ genSub act {u} → (∀ Z, ∀ y ∈ Q, act Z y ∈ Q) → u ∉ Q → Q = ⊥) ∧
    ∀ μ, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ x ∈ genSub act {u}, x ∈ hwSub act μ → x ∈ S := by
  first
  | exact @_root_.GlobalTheory.FiltrationEquivalenceRelation.main
  | exact _root_.GlobalTheory.FiltrationEquivalenceRelation.main
  | (apply _root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiltrationEquivalenceRelation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiltrationEquivalenceRelation.main ..)

def prodAct {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (a' : Mat p q →ₗ[ℂ] Module.End ℂ V') :
    Mat p q →ₗ[ℂ] Module.End ℂ (V × V') where
  toFun Z := (a Z).prodMap (a' Z)
  map_add' Y Z := by ext <;> simp
  map_smul' c Z := by ext <;> simp

@[simp] theorem prodAct_apply {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (a' : Mat p q →ₗ[ℂ] Module.End ℂ V') (Z : Mat p q) (x : V × V') :
    prodAct a a' Z x = (a Z x.1, a' Z x.2) := rfl

def prodForm {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (b' : V' →ₗ⋆[ℂ] V' →ₗ[ℂ] ℂ) : (V × V') →ₗ⋆[ℂ] (V × V') →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => b x.1 y.1 + b' x.2 y.2)
    (fun x y z => by simp; ring) (fun c x y => by simp; ring) (fun x y z => by simp; ring)
    (fun c x y => by simp; ring)

theorem prodForm_apply {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (b : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (b' : V' →ₗ⋆[ℂ] V' →ₗ[ℂ] ℂ) (x y : V × V') :
    prodForm b b' x y = b x.1 y.1 + b' x.2 y.2 := rfl

theorem ip_nonneg (M : UGKMod p q) (x : M.M.V) : 0 ≤ (M.ip x x).re := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (M.pos x hx).le

theorem diag_irred {lam : Ix p q → ℚ} (hl : IsParam lam) (hg1 : GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1))
    (hg2 : GapGt lam (((p + q : ℕ) : ℝ) - 1)) (M M' : UGKMod p q) (u : M.M.V) (u' : M'.M.V)
    (hu : u ∈ hwSub M.M.act (blattner lam)) (hu' : u' ∈ hwSub M'.M.act (blattner lam))
    (hc : casimir M.M.act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u)
    (hc' : casimir M'.M.act u' = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u') :
    ∀ Q : Submodule ℂ (M.M.V × M'.M.V), Q ≤ genSub (prodAct M.M.act M'.M.act) {(u, u')} →
      (∀ Z, ∀ y ∈ Q, prodAct M.M.act M'.M.act Z y ∈ Q) → (u, u') ∉ Q → Q = ⊥ := by
  refine (gen_irred_adm (prodAct M.M.act M'.M.act) ?_ (prodForm M.ip M'.ip) ?_ ?_ ?_ hl hg1 hg2 (u, u')
    ?_ ?_ ?_).1
  · intro X Y
    refine LinearMap.ext fun x => ?_
    simp only [prodAct_apply, M.M.lie X Y, M'.M.lie X Y, LinearMap.sub_apply, Module.End.mul_apply]
    rfl
  · intro x y
    rw [prodForm_apply, prodForm_apply, star_add, M.herm, M'.herm]
  · intro x hx
    rw [prodForm_apply, Complex.add_re]
    have h1 := ip_nonneg M x.1
    have h2 := ip_nonneg M' x.2
    by_cases h : x.1 = 0
    · have := M'.pos x.2 fun h' => hx (Prod.ext h h')
      linarith
    · have := M.pos x.1 h
      linarith
  · intro Z x y
    simp only [prodForm_apply, prodAct_apply, M.adj, M'.adj]
  · obtain ⟨W, hW, huW, hst⟩ := M.M.kfin u
    obtain ⟨W', hW', huW', hst'⟩ := M'.M.kfin u'
    exact ⟨W.prod W', Module.Finite.of_fg (Submodule.FG.prod (Submodule.FG.of_finite) (Submodule.FG.of_finite)), ⟨huW, huW'⟩,
      fun X hX w hw => ⟨hst X hX _ hw.1, hst' X hX _ hw.2⟩⟩
  · rw [mem_hwSub] at hu hu' ⊢
    exact ⟨fun a => Prod.ext (hu.1 a) (hu'.1 a), fun a b h => Prod.ext (hu.2 a b h) (hu'.2 a b h)⟩
  · refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst, ← hc]
      simp [casimir, Prod.fst_sum]
    · rw [Prod.smul_snd, ← hc']
      simp [casimir, Prod.snd_sum]

theorem gen_iso_of_lowest_type : admQ7 → admQ8 → ∀ (p q : ℕ) (lam : Ix p q → ℚ), IsParam lam → GapGt lam (((p + q : ℕ) : ℝ) ^ 3 / 24 + 1) → GapGt lam (((p + q : ℕ) : ℝ) - 1) → ∀ (M M' : UGKMod p q) (u : M.M.V) (u' : M'.M.V), IsHW M.M.act (blattner lam) u → IsHW M'.M.act (blattner lam) u' → casimir M.M.act u = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u → casimir M'.M.act u' = ((normSq lam - rhoSq (p + q) : ℚ) : ℂ) • u' → IrrGK M'.M → (∃ e : M'.M.V →ₗ[ℂ] M.M.V, Function.Injective e ∧ (∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x)) ∧ e u' = u ∧ LinearMap.range e = genSub M.M.act {u}) ∧ AdmGK M'.M := by
  intro _ _ p q lam hl hg1 hg2 M M' u u' hu hu' hc hc' hirr
  constructor
  · set N := genSub (prodAct M.M.act M'.M.act) {(u, u')} with hN
    have hNs := genSub_stable (prodAct M.M.act M'.M.act) {(u, u')}
    have hw : (u, u') ∈ N := mem_genSub_self _ _
    let π : N →ₗ[ℂ] M'.M.V := LinearMap.snd ℂ _ _ ∘ₗ N.subtype
    have hinj : Function.Injective π := by
      have h := diag_irred hl hg1 hg2 M M' u u' hu.2 hu'.2 hc hc' (N ⊓ LinearMap.ker (LinearMap.snd ℂ _ _))
        inf_le_left (fun Z y hy => ⟨hNs Z y hy.1, by
          have h2 : y.2 = 0 := hy.2
          change M'.M.act Z y.2 = 0
          rw [h2, map_zero]⟩) (fun h => hu'.1 h.2)
      rw [injective_iff_map_eq_zero]
      intro x hx
      have : (x : M.M.V × M'.M.V) ∈ N ⊓ LinearMap.ker (LinearMap.snd ℂ _ _) := ⟨x.2, hx⟩
      rw [h] at this
      exact Subtype.ext this
    have hsurj : Function.Surjective π := by
      rcases hirr.2 (LinearMap.range π) (by
        rintro Z _ ⟨x, rfl⟩
        exact ⟨⟨_, hNs Z x x.2⟩, rfl⟩) with h | h
      · have : u' ∈ LinearMap.range π := ⟨⟨_, hw⟩, rfl⟩
        rw [h] at this
        exact absurd this hu'.1
      · exact LinearMap.range_eq_top.1 h
    let φ := LinearEquiv.ofBijective π ⟨hinj, hsurj⟩
    let e : M'.M.V →ₗ[ℂ] M.M.V := (LinearMap.fst ℂ _ _ ∘ₗ N.subtype) ∘ₗ φ.symm.toLinearMap
    have he : ∀ x : N, e (x : M.M.V × M'.M.V).2 = (x : M.M.V × M'.M.V).1 := fun x =>
      congrArg (fun y : N => (y : M.M.V × M'.M.V).1) (φ.symm_apply_apply x)
    have heZ : ∀ Z x, e (M'.M.act Z x) = M.M.act Z (e x) := by
      intro Z x
      obtain ⟨y, rfl⟩ := hsurj x
      have h1 := he ⟨_, hNs Z y y.2⟩
      have h2 := he y
      exact h1.trans (congrArg (M.M.act Z) h2.symm)
    have heu : e u' = u := he ⟨_, hw⟩
    refine ⟨e, ?_, heZ, heu, le_antisymm ?_ (genSub_le ⟨u', heu⟩ ?_)⟩
    · rcases hirr.2 (LinearMap.ker e) (fun Z y hy => by
        rw [LinearMap.mem_ker] at hy ⊢
        rw [heZ, hy, map_zero]) with h | h
      · exact LinearMap.ker_eq_bot.1 h
      · have : u' ∈ LinearMap.ker e := h ▸ Submodule.mem_top
        rw [LinearMap.mem_ker, heu] at this
        exact absurd this hu.1
    · rintro _ ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := hsurj x
      have h1 : N ≤ (genSub M.M.act {u}).comap (LinearMap.fst ℂ _ _) :=
        genSub_le (mem_genSub_self _ u) fun Z z hz => genSub_stable _ _ Z _ hz
      exact (he y).symm ▸ h1 y.2
    · rintro Z _ ⟨x, rfl⟩
      exact ⟨_, heZ Z x⟩
  · intro μ
    obtain ⟨S, hS, hS'⟩ := (gen_irred_adm M'.M.act M'.M.lie M'.ip M'.herm M'.pos M'.adj hl hg1 hg2 u'
      (M'.M.kfin u') hu'.2 hc').2 μ
    have htop : genSub M'.M.act {u'} = ⊤ := by
      rcases hirr.2 _ (genSub_stable M'.M.act {u'}) with h | h
      · have := mem_genSub_self M'.M.act u'
        rw [h] at this
        exact absurd this hu'.1
      · exact h
    exact Submodule.finiteDimensional_of_le (S₂ := S) fun x hx => hS' x (htop ▸ Submodule.mem_top) hx

end GlobalTheory.LowGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureTorsorEtaleHeightOneAbhyankarStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_torsor_etale_height_one_abhyankar : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A] [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₁] [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    [Algebra.Etale A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∀ a : A, a ≠ 0 →
    (∀ (p₁ : Ideal A₁) [p₁.IsPrime], p₁.height = 1 → f a ∈ p₁ →
        (p₁.comap f).height = 1 ∧
        ∃ π : A, Irreducible (algebraMap A (Localization.AtPrime (p₁.comap f)) π) ∧
          ∃ y : A₁, y ^ q = f π) →
    ∀ (P₁ : Ideal (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj)) [P₁.IsPrime], P₁.height ≤ 1 → algebraMap A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∈ P₁ →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA) P₁ := by
  first | (exact @GlobalTheory.KeyOriginBC.closureEtaleAt_of_mem_height_le_one) | (exact GlobalTheory.KeyOriginBC.closureEtaleAt_of_mem_height_le_one) | (intros; apply GlobalTheory.KeyOriginBC.closureEtaleAt_of_mem_height_le_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMap
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

variable {R S : Type} [CommRing R] [CommRing S] (σ : R →+* S) {d : ℕ} {τ : Type}

theorem map_powerSeriesEvalTwoGroups (c : MvPowerSeries (Fin d ⊕ Fin d) R) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    MvPowerSeries.map σ (at2 c u v) =
      at2 (MvPowerSeries.map σ c) (fun i => MvPowerSeries.map σ (u i))
        (fun i => MvPowerSeries.map σ (v i)) := by
  have hs : HasSubst (Sum.elim u v) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp [hu, hv])
  unfold at2
  rw [map_subst hs]
  congr 1
  funext s
  cases s <;> rfl

theorem constantCoeff_powerSeriesEvalTwoGroups_zero_of {c : MvPowerSeries (Fin d ⊕ Fin d) R}
    (hc : constantCoeff c = 0) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    constantCoeff (at2 c u v) = 0 := by
  have h0 : ∀ s, constantCoeff (Sum.elim u v s) = 0 := fun s => by cases s <;> simp [hu, hv]
  exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 hc

theorem map_op_of_const (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    (fun i => MvPowerSeries.map σ (op μ u v i)) =
      op (fun i => MvPowerSeries.map σ (μ i)) (fun i => MvPowerSeries.map σ (u i))
        (fun i => MvPowerSeries.map σ (v i)) := by
  funext i
  exact map_powerSeriesEvalTwoGroups σ (μ i) hu hv

theorem isLaw_map (R S : Type) [CommRing R] [CommRing S] (σ : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (h : IsLaw μ) :
    IsLaw (fun i => MvPowerSeries.map σ (μ i)) := by
  have hX : ∀ {κ : Type} (f : Fin d → κ), (fun i => MvPowerSeries.map σ
      (X (f i) : MvPowerSeries κ R)) = fun i => (X (f i) : MvPowerSeries κ S) := by
    intro κ f; funext i; exact map_X σ (f i)
  have hcX : ∀ {κ : Type} (f : Fin d → κ) (i : Fin d),
      constantCoeff (X (f i) : MvPowerSeries κ R) = 0 := fun f i => constantCoeff_X _
  refine ⟨fun i => ?_, ?_, fun i => ?_, ?_⟩
  · rw [constantCoeff_map, h.const i, map_zero]
  · have h1 := congrArg (fun w : Fin d → MvPowerSeries (Fin d) R =>
      fun i => MvPowerSeries.map σ (w i)) h.unit
    rw [map_op_of_const σ μ (u := fun i => (X i : MvPowerSeries (Fin d) R)) (fun i => constantCoeff_X i)
      (fun _ => map_zero _)] at h1
    simpa only [map_X, map_zero] using h1
  · have h1 := congrArg (MvPowerSeries.map σ) (h.comm i)
    unfold swap at h1 ⊢
    rw [map_powerSeriesEvalTwoGroups σ (μ i) (hcX Sum.inr) (hcX Sum.inl)] at h1
    simpa only [map_X] using h1
  · have hx1 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx2 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have hx3 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
    have c12 : ∀ i, constantCoeff (op μ x1 x2 i) = 0 := fun i =>
      constantCoeff_powerSeriesEvalTwoGroups_zero_of (h.const i) hx1 hx2
    have c23 : ∀ i, constantCoeff (op μ x2 x3 i) = 0 := fun i =>
      constantCoeff_powerSeriesEvalTwoGroups_zero_of (h.const i) hx2 hx3
    have h1 := congrArg (fun w : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R =>
      fun i => MvPowerSeries.map σ (w i)) h.assoc
    rw [map_op_of_const σ μ c12 hx3, map_op_of_const σ μ hx1 c23,
      map_op_of_const σ μ hx1 hx2, map_op_of_const σ μ hx2 hx3] at h1
    have e1 : (fun i => MvPowerSeries.map σ (x1 (R := R) (d := d) i)) = x1 := hX _
    have e2 : (fun i => MvPowerSeries.map σ (x2 (R := R) (d := d) i)) = x2 := hX _
    have e3 : (fun i => MvPowerSeries.map σ (x3 (R := R) (d := d) i)) = x3 := hX _
    rwa [e1, e2, e3] at h1

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevExistsPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}

def secPush (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) : Over.mk (T.hom ≫ f) ⟶ o.A :=
  Over.homMk (u.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]; rfl)

theorem secPush_left (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) :
    (secPush m T u).left = u.left ≫ m.φ := rfl

theorem secPush_inj (m : ObjMap o' o f) (T : Over S') {u v : T ⟶ o'.A}
    (h : secPush m T u = secPush m T v) : u = v := by
  have h' := congrArg CommaMorphism.left h
  exact Over.OverMorphism.ext (m.cart.1.hom_ext h' (by rw [Over.w, Over.w]))

theorem secPush_mul (m : ObjMap o' o f) (T : Over S') (u v : T ⟶ o'.A) :
    secPush m T (u * v) = secPush m T u * secPush m T v := by
  apply Over.OverMorphism.ext
  rw [secPush_left]
  exact (m.cart.2 T u v (secPush m T u) (secPush m T v) rfl rfl).symm

theorem secPush_one (m : ObjMap o' o f) (T : Over S') :
    secPush m T 1 = 1 := by
  have h := secPush_mul m T 1 1
  rw [_root_.mul_one] at h
  exact (_root_.mul_eq_left.mp h.symm)

theorem secPush_act (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) (c : D.O) :
    secPush m T (u ≫ o'.act.act c) = secPush m T u ≫ o.act.act c := by
  apply Over.OverMorphism.ext
  simp only [secPush_left, Over.comp_left, Category.assoc, m.act]

theorem isEtLev_exists_pull : ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S} (m : ObjMap o' o f) {w0 : Ideal (𝓞 D.F)} {r : ℕ} {lv : D.La → (𝟙_ (Over S) ⟶ o.A)}, IsEtLev o w0 r lv → ∃ lv' : D.La → (𝟙_ (Over S') ⟶ o'.A), IsEtLev o' w0 r lv' ∧ ∀ y, (lv' y).left ≫ m.φ = f ≫ (lv y).left := by
  intro p _ D R _ b N S S' s s' o o' f m w0 r lv hlv
  have hu : ∀ {X : Scheme.{0}} (T : Over X), (toUnit T).left = T.hom := fun T =>
    (Category.comp_id _).symm.trans (Over.w (toUnit T))
  have wα : ∀ y, (f ≫ (lv y).left) ≫ o.A.hom = 𝟙 S' ≫ f := fun y => by
    rw [Category.assoc, Over.w]; simp
  let lv' : D.La → (𝟙_ (Over S') ⟶ o'.A) := fun y =>
    Over.homMk (m.cart.1.lift (f ≫ (lv y).left) (𝟙 S') (wα y)) (m.cart.1.lift_snd _ _ _)
  have hα : ∀ y, (lv' y).left ≫ m.φ = f ≫ (lv y).left := fun y => m.cart.1.lift_fst _ _ _
  have hP1 : ∀ y, secPush m (𝟙_ (Over S')) (lv' y) =
      toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)) ≫ lv y := fun y => by
    apply Over.OverMorphism.ext
    rw [secPush_left, hα, Over.comp_left, hu]; simp
  have hP : ∀ (T : Over S') y, secPush m T (toUnit T ≫ lv' y) =
      toUnit (Over.mk (T.hom ≫ f)) ≫ lv y := fun T y => by
    apply Over.OverMorphism.ext
    rw [secPush_left, Over.comp_left, Category.assoc, hα, Over.comp_left, hu, hu]; simp
  refine ⟨lv', ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x' => ?_⟩, hα⟩
  · apply secPush_inj m
    rw [secPush_mul, hP1, hP1, hP1, hlv.1, MonObj.comp_mul]
  · apply secPush_inj m
    rw [secPush_act, hP1, hP1, hlv.2.1, Category.assoc]
  · apply secPush_inj m
    rw [hP1, secPush_one, hlv.2.2.1 x hx, MonObj.comp_one]
  · obtain ⟨hinj, hsurj⟩ := hlv.2.2.2 k (x' ≫ f)
    refine ⟨fun y hy => hinj y ?_, fun g hg => ?_⟩
    · have h := congrArg (secPush m (Over.mk x')) hy
      rw [hP, secPush_one] at h
      exact h
    · obtain ⟨y, hy⟩ := hsurj (secPush m (Over.mk x') g) (fun c hc => by
        rw [← secPush_act, hg c hc, secPush_one])
      refine ⟨y, secPush_inj m _ ?_⟩
      rw [hP]
      exact hy

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
section
noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def IsEtLevOver {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (l : D.La → (T ⟶ o.A)) : Prop :=
  (∀ x y, l (x + y) = l x * l y) ∧ (∀ (c : D.O) x, l (c • x) = l x ≫ o.act.act c) ∧
    (∀ x ∈ wSub D w0 r, l x = 1) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
      (∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ l y = 1 → y ∈ wSub D w0 r) ∧
      ∀ g : Over.mk (x ≫ T.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
        ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ l y = g

def ptOf {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} {T : Scheme.{0}} {t : T ⟶ S} {s₁ : T ⟶ Sp R} {o : Obj b N s}
    {o₁ : Obj b N s₁} (m : ObjMap o₁ o t) (l : 𝟙_ (Over T) ⟶ o₁.A) : Over.mk t ⟶ o.A :=
  Over.homMk (l.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w l]
    exact Category.id_comp t)

def levAct {w0 : Ideal (𝓞 D.F)} {r : ℕ} (g : LevGrp D w0 r) (y : D.La) : D.La :=
  Function.surjInv (Submodule.mkQ_surjective (wSub D w0 r)) (g ((wSub D w0 r).mkQ y))

theorem mkQ_levAct {w0 : Ideal (𝓞 D.F)} {r : ℕ} (g : LevGrp D w0 r) (y : D.La) :
    (wSub D w0 r).mkQ (levAct g y) = g ((wSub D w0 r).mkQ y) :=
  Function.surjInv_eq _ _

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFullSymplecticLevelStructureUniqueOfLevelsStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField GlobalTheory.FullLevel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFullSymplecticLevelStructure_unique_of_levels : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} (l : Level H) {k : Type} [Field k]
    {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop},
    (∀ (g g' : Q) (c c' : kˣ), e l.M' g g' c → e l.M' g g' c' → c = c') →
    ∀ {z : kˣ}, IsPrimitiveRoot z l.M' → ∀ {etaA eta ev ev' : D.La → Q},
    IsSympLevel D act e l.M' z ev → Induces l etaA eta ev →
    IsSympLevel D act e l.M' z ev' → Induces l etaA eta ev' → ev = ev' := by
  first | exact @GlobalTheory.FullLevel.isSympLevel_unique | exact GlobalTheory.FullLevel.isSympLevel_unique | (intros; apply GlobalTheory.FullLevel.isSympLevel_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGaloisCoverGrpSchemeSquareProductMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'] (G : Subgroup (𝟙_ (Over S) ⟶ A)) (ψ : A ⟶ A'), IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → GlobalTheory.ZM.IsGaloisCover (G × G) (fun h => (GlobalTheory.UPel.HT.Hecke.transl (lift h.1.1 h.2.1 : 𝟙_ (Over S) ⟶ G2 A)).left) (GlobalTheory.UPel.HT.Hecke.sq2 ψ) := by
  first | exact @GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap | exact GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap | (intros; apply GlobalTheory.UPel.HT.Hecke.isGaloisCover_grpSchemeSquareProductMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDiv

theorem isHopfIdeal_kerIdeal_of_bialgHom (k A B : Type) [CommRing k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] (f : B →ₐc[k] A) : (kerIdeal f).IsHopfIdeal k where
  counit_eq_zero x hx :=
    (kerIdeal_le_ker_iff f (counitAlgHom k A)).2 (fun c => by simp) hx
  map_mkQ_comul_eq_zero x hx := by
    have h0 := (kerIdeal_le_ker_iff f (Ideal.Quotient.mkₐ k (kerIdeal f))).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
    have h : kerIdeal f ≤ RingHom.ker
        ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
          (Ideal.Quotient.mkₐ k (kerIdeal f))).comp (comulAlgHom k A)) := by
      refine (kerIdeal_le_ker_iff f _).2 fun c => ?_
      have key : ∀ t : B ⊗[k] B, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k (kerIdeal f))
          (Ideal.Quotient.mkₐ k (kerIdeal f)) (pullbackTwo f t) =
          algebraMap k _ (counit (R := k)
            (TensorProduct.lid k B (LinearMap.rTensor B (counit (R := k) (A := B)) t))) := by
        intro t
        induction t with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul x y =>
          rw [TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul,
            TensorProduct.lid_tmul, map_smul]
          erw [h0, h0]
          simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, smul_tmul',
            smul_smul, mul_comm]
      rw [AlgHom.comp_apply, comulAlgHom_apply, ← pullTwo_comul, key, rTensor_counit_comul,
        TensorProduct.lid_tmul, one_smul]
    exact h hx
  antipode_mem x hx := by
    have h : kerIdeal f ≤ (kerIdeal f).comap (HopfAlgebra.antipodeAlgHom k A) := by
      refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
      have ha' : counit (R := k) a = 0 := ha
      change HopfAlgebra.antipode k (f a) ∈ kerIdeal f
      rw [← bialgHom_map_antipode]
      exact Ideal.mem_map_of_mem (f : B →ₐ[k] A) (by simp [RingHom.mem_ker, ha'])
    exact h hx

end GlobalTheory.PDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfComponentsIntoGroupSchemeProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMonHom_of_components_into_groupScheme_product : ∀ (T : Scheme.{0}) (A' B' C : Over T) [GrpObj A'] [GrpObj B'] [GrpObj C] (r : ℕ) (pr' : Fin r → (B' ⟶ A')), (∀ u, IsMonHom (pr' u)) → (∀ (X : Over T) (y : Fin r → (X ⟶ A')), ∃! x : X ⟶ B', ∀ u, x ≫ pr' u = y u) → ∀ Φ : C ⟶ B', (∀ u, IsMonHom (Φ ≫ pr' u)) → IsMonHom Φ := by
  first | (exact @GlobalTheory.Serre.isMonHom_of_components) | (exact GlobalTheory.Serre.isMonHom_of_components) | (intros; apply GlobalTheory.Serre.isMonHom_of_components  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIntegralityRamifiedOfExpansionStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeValueIntegrality_ramified_of_expansion : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → Expansion → LatIntRam := by
  first | exact @GlobalTheory.LatValRam.latIntRam | exact GlobalTheory.LatValRam.latIntRam | (intros; apply GlobalTheory.LatValRam.latIntRam <;> assumption)
end

