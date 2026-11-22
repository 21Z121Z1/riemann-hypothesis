import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0969
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.Bundle0001
import Formalism.FormalDegreeBessel.FormalDegreeRatio.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hilbert90TensorPadicUnramifiedExtension
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

section HilbertNinety

theorem iterate_groupEndomorphism_inv_apply {H : Type*} [Group H] (θ : H →* H) (i : ℕ) (x : H) :
    (⇑θ)^[i] x⁻¹ = ((⇑θ)^[i] x)⁻¹ := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_inv]

theorem twistedNormProductIterate_succ_mul_iterate {H : Type} [Group H] (θ : H →* H) (n : ℕ) (δ : H) :
    nrmG θ (n + 1) δ = nrmG θ n δ * (⇑θ)^[n] δ := by
  simp [nrmG, List.range_succ, List.map_append, List.prod_append]

theorem units_map_ringHom_iterate_val {A : Type*} [CommRing A] (f : A →+* A) (i : ℕ) (u : Aˣ) :
    (((⇑(Units.map f.toMonoidHom))^[i] u : Aˣ) : A) = (⇑f)^[i] (u : A) := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Units.coe_map, ← ih] <;> rfl

theorem iterate_twisted_ringHom_mul_inv_eq_norm {A : Type} [CommRing A] (f : A →+* A) (a : Aˣ) (i : ℕ) (v : A) :
    (fun x => f x * ((a⁻¹ : Aˣ) : A))^[i] v =
      (⇑f)^[i] v * (((nrmG (Units.map f.toMonoidHom) i a)⁻¹ : Aˣ) : A) := by
  induction i generalizing v with
  | zero => simp [nrmG]
  | succ n ih =>
    simp only [Function.iterate_succ_apply]
    rw [ih, twistedNormProductIterate_succ_mul_iterate, _root_.mul_inv_rev, Units.val_mul, ← iterate_groupEndomorphism_inv_apply, units_map_ringHom_iterate_val,
      ← RingHom.coe_pow, map_mul]
    ring

variable (p : ℕ) [Fact p.Prime]

theorem unramifiedPadicFrobeniusAlgEquiv_pow_apply_eq_iterate (r : ℕ) (hr : 0 < r) (i : ℕ) (y : Qr p r) :
    (frobQEquiv p r hr ^ i) y = (⇑(frobQ p r))^[i] y := by
  induction i generalizing y with
  | zero => rfl
  | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, ih, Function.iterate_succ_apply] <;> rfl

theorem padicUnramifiedFrobenius_iterate_degree_apply_eq (r : ℕ) (hr : 0 < r) (y : Qr p r) : (⇑(frobQ p r))^[r] y = y := by
  have h1 : frobQEquiv p r hr ^ r = 1 := by
    have := pow_orderOf_eq_one (frobQEquiv p r hr)
    rwa [orderOf_frobQEquiv] at this
  rw [← unramifiedPadicFrobeniusAlgEquiv_pow_apply_eq_iterate p r hr, h1]
  rfl

theorem exists_ne_padicUnramifiedFrobenius_iterate_lt_degree (r : ℕ) (hr : 0 < r) (i : ℕ) (hi0 : 0 < i) (hir : i < r) :
    ∃ y : Qr p r, (⇑(frobQ p r))^[i] y ≠ y := by
  by_contra h
  push_neg at h
  have h1 : frobQEquiv p r hr ^ i = 1 := AlgEquiv.ext fun y => by
    rw [unramifiedPadicFrobeniusAlgEquiv_pow_apply_eq_iterate, h y]; rfl
  have h2 := orderOf_dvd_of_pow_eq_one h1
  rw [orderOf_frobQEquiv] at h2
  exact absurd (Nat.le_of_dvd hi0 h2) (not_le.2 hir)

variable (B : Type) [CommRing B] [Algebra ℚ_[p] B]

theorem tensorMap_padicUnramifiedFrobenius_iterate_tmul (r i : ℕ) (b : B) (y : Qr p r) :
    (⇑(Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)))^[i] (b ⊗ₜ y) =
      b ⊗ₜ (⇑(frobQ p r))^[i] y := by
  induction i with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp

theorem tensorMap_padicUnramifiedFrobenius_iterate_degree (r : ℕ) (hr : 0 < r) (x : B ⊗[ℚ_[p]] Qr p r) :
    (⇑(Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)))^[r] x = x := by
  change ((Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom ^ r) x = x
  induction x using TensorProduct.induction_on with
  | zero => exact map_zero _
  | tmul b y =>
    rw [RingHom.coe_pow]
    exact (tensorMap_padicUnramifiedFrobenius_iterate_tmul p B r r b y).trans (by rw [padicUnramifiedFrobenius_iterate_degree_apply_eq p r hr])
  | add x y hx hy => rw [map_add, hx, hy]

end HilbertNinety

end GlobalTheory.LKMid

namespace GlobalTheory.LKMid

theorem hilbert90_frobenius_tensor_unramified_padic : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ (B : Type) [CommRing B] [Algebra ℚ_[p] B]
    [Module.Finite ℚ_[p] B] (a : (B ⊗[ℚ_[p]] Qr p r)ˣ),
    nrmG (Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom) r a = 1 →
    ∃ g : (B ⊗[ℚ_[p]] Qr p r)ˣ, a = g⁻¹ *
      Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom g := by
  intro p _ r hr B _ _ _ a ha
  haveI : FiniteDimensional ℚ_[p] (Qr p r) := ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr
  let σ := Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)
  let τ : B ⊗[ℚ_[p]] Qr p r → B ⊗[ℚ_[p]] Qr p r := fun x => σ x * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _)
  have hτr : ∀ v, τ^[r] v = v := by
    intro v
    have := iterate_twisted_ringHom_mul_inv_eq_norm σ.toRingHom a r v
    rw [ha, inv_one, Units.val_one, mul_one] at this
    exact this.trans (tensorMap_padicUnramifiedFrobenius_iterate_degree p B r hr v)

  let W : Submodule ℚ_[p] (B ⊗[ℚ_[p]] Qr p r) :=
    { carrier := {v | τ v = v}
      add_mem' := by
        intro x y hx hy
        show σ (x + y) * _ = x + y
        rw [map_add, add_mul]
        rw [show σ x * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = x from hx,
          show σ y * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = y from hy]
      zero_mem' := by
        show σ 0 * _ = 0
        rw [map_zero, zero_mul]
      smul_mem' := by
        intro c x hx
        show σ (c • x) * _ = c • x
        rw [map_smul, smul_mul_assoc]
        rw [show σ x * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = x from hx] }

  let e : (Qr p r ⊗[ℚ_[p]] B) ≃ₐ[ℚ_[p]] (B ⊗[ℚ_[p]] Qr p r) := Algebra.TensorProduct.comm ℚ_[p] (Qr p r) B
  have he_smul : ∀ (c : Qr p r) (w : Qr p r ⊗[ℚ_[p]] B), e (c • w) = ((1 : B) ⊗ₜ c) * e w := by
    intro c w
    rw [Algebra.smul_def, map_mul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.comm_tmul] <;> rfl
  let s : Qr p r ≃+* Qr p r := (frobQEquiv p r hr).toRingEquiv
  have hs : ∀ y, s y = frobQ p r y := fun _ => rfl
  let F : (Qr p r ⊗[ℚ_[p]] B) →+ (Qr p r ⊗[ℚ_[p]] B) :=
    { toFun := fun w => e.symm (τ (e w))
      map_zero' := by simp [τ]
      map_add' := fun x y => by simp only [τ, map_add, add_mul] }
  have hFe : ∀ w, e (F w) = τ (e w) := fun w => AlgEquiv.apply_symm_apply e _
  have hF : ∀ (c : Qr p r) (w : Qr p r ⊗[ℚ_[p]] B), F (c • w) = s c • F w := by
    intro c w
    apply e.injective
    rw [hFe, he_smul, he_smul, hFe, hs]
    simp only [τ, σ, map_mul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, mul_assoc]
  have hFi : ∀ (i : ℕ) (w : Qr p r ⊗[ℚ_[p]] B), F^[i] w = e.symm (τ^[i] (e w)) := by
    intro i
    induction i with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      apply e.injective
      rw [hFe, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have hFr : ∀ w, F^[r] w = w := by
    intro w
    rw [hFi, hτr, AlgEquiv.symm_apply_apply]
  have hsr : ∀ x, (⇑s)^[r] x = x := fun x => padicUnramifiedFrobenius_iterate_degree_apply_eq p r hr x
  have hsi : ∀ i, 0 < i → i < r → ∃ x, (⇑s)^[i] x ≠ x := fun i h0 h1 => exists_ne_padicUnramifiedFrobenius_iterate_lt_degree p r hr i h0 h1
  have hspan := GlobalTheory.semilinear_fixed_span (Qr p r) s r hr hsr hsi (Qr p r ⊗[ℚ_[p]] B) F hF hFr

  have hkey : ∀ m : Ideal (B ⊗[ℚ_[p]] Qr p r), m.IsMaximal → ∃ w ∈ W, w ∉ m := by
    intro m hm
    by_contra h
    push_neg at h
    let I' : Submodule (Qr p r) (Qr p r ⊗[ℚ_[p]] B) :=
      { carrier := {v | e v ∈ m}
        add_mem' := by
          intro x y hx hy
          show e (x + y) ∈ m
          rw [map_add]
          exact m.add_mem hx hy
        zero_mem' := by
          show e 0 ∈ m
          rw [map_zero]
          exact m.zero_mem
        smul_mem' := by
          intro c x hx
          show e (c • x) ∈ m
          rw [he_smul]
          exact m.mul_mem_left _ hx }
    have hle : Submodule.span (Qr p r) {v | F v = v} ≤ I' := by
      rw [Submodule.span_le]
      intro v hv
      have hv' : τ (e v) = e v := by
        have h2 : e (F v) = e v := congrArg e hv
        rwa [hFe] at h2
      exact h _ hv'
    rw [hspan] at hle
    have h1 : e 1 ∈ m := hle Submodule.mem_top
    rw [map_one] at h1
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 h1)
  haveI : IsArtinianRing (B ⊗[ℚ_[p]] Qr p r) := IsArtinianRing.of_finite ℚ_[p] (B ⊗[ℚ_[p]] Qr p r)
  have hfin := IsArtinianRing.setOf_isMaximal_finite (B ⊗[ℚ_[p]] Qr p r)
  let fS : Ideal (B ⊗[ℚ_[p]] Qr p r) → Subspace ℚ_[p] W := fun I => (I.restrictScalars ℚ_[p]).comap W.subtype
  have htop : (⊤ : Subspace ℚ_[p] W) ∉ hfin.toFinset.image fS := by
    intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨I, hI, hIt⟩ := hmem
    rw [Set.Finite.mem_toFinset] at hI
    obtain ⟨w, hwW, hwI⟩ := hkey I hI
    have : (⟨w, hwW⟩ : W) ∈ fS I := by rw [hIt]; exact Submodule.mem_top
    exact hwI this
  obtain ⟨w, hw⟩ := (Set.ne_univ_iff_exists_notMem _).1 (Subspace.biUnion_ne_univ_of_top_notMem htop)
  have hunit : IsUnit (w : B ⊗[ℚ_[p]] Qr p r) := by
    by_contra hu
    obtain ⟨I, hI, hwI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hu)
    apply hw
    rw [Set.mem_iUnion₂]
    exact ⟨fS I, Finset.mem_image.2 ⟨I, (Set.Finite.mem_toFinset _).2 hI, rfl⟩, hwI⟩
  have hfix : σ (w : B ⊗[ℚ_[p]] Qr p r) * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) = w := w.2
  have hσ : σ (hunit.unit : B ⊗[ℚ_[p]] Qr p r) = (hunit.unit : B ⊗[ℚ_[p]] Qr p r) * a := by
    rw [IsUnit.unit_spec]
    calc σ (w : B ⊗[ℚ_[p]] Qr p r)
        = σ (w : B ⊗[ℚ_[p]] Qr p r) * ((a⁻¹ : (B ⊗[ℚ_[p]] Qr p r)ˣ) : _) * a := by
          rw [mul_assoc, Units.inv_mul, mul_one]
      _ = w * a := by rw [hfix]
  refine ⟨hunit.unit, Units.ext ?_⟩
  rw [Units.val_mul, Units.coe_map]
  show (a : B ⊗[ℚ_[p]] Qr p r) = _ * σ _
  rw [hσ, Units.inv_mul_cancel_left]

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicShapeIntegralWeightGoodEmbedding
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

open Formalism.L2.NTheta in

theorem lamAt_strictAnti {R : Ranks} (h : HCParam R) {n : ℕ} (hn : n = R.r) :
    StrictAnti fun a : Fin n => lamAt h a := by
  intro a b hab
  have h1 : (a : ℕ) < b := hab
  have h2 := b.2
  have h3 := lamAt_add_add_le h (b - a) a (by omega)
  rw [show (a : ℕ) + (b - a) = b by omega] at h3
  have h4 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by
    have : 1 ≤ (b : ℕ) - a := by omega
    exact_mod_cast this
  show lamAt h b < lamAt h a
  linarith

open Formalism.L2.NTheta in

theorem holPar_kapW_eq {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n) :
    holPar p q (kapW h p q) = Finset.univ.image fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p)) := by
  have ho : Odd (p + q) := by rw [hpq, hn]; exact odd_r R
  ext x
  simp only [holPar, Finset.mem_image, Finset.mem_univ, true_and, holEnt_kapW h p q ho]
  constructor
  · rintro ⟨a | a, rfl⟩
    · exact ⟨⟨a, by have := a.2; omega⟩, by simp⟩
    · exact ⟨⟨p + a, by have := a.2; omega⟩, by simp⟩
  · rintro ⟨a, rfl⟩
    by_cases ha : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, ha⟩, by simp [ha]⟩
    · refine ⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_⟩
      simp [ha, show p + ((a : ℕ) - p) = a by omega]

open Formalism.L2.NTheta in

theorem isEnum_holPar_kapW {R : Ranks} (h : HCParam R) {n p q : ℕ} (hn : n = R.r) (hpq : p + q = n)
    {lam : Fin n → ℝ} {ε : Fin n → Bool} (he : IsEnum (holPar p q (kapW h p q)) lam ε) (a : Fin n) :
    lam a = (lamAt h a : ℝ) ∧ ε a = decide ((a : ℕ) < p) := by
  obtain ⟨hs, f, hf, hS⟩ := he
  rw [holPar_kapW_eq h hn hpq] at hS
  have hg := lamAt_strictAnti h hn
  have hfs : StrictAnti f := fun a b hab => by
    have := hs hab
    rw [hf, hf] at this
    exact_mod_cast this
  have m1 : ∀ a, ∃ b : Fin n, (lamAt h b, decide ((b : ℕ) < p)) = (f a, ε a) := fun a => by
    have : (f a, ε a) ∈ Finset.univ.image fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p)) := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, hb⟩
  have m2 : ∀ a : Fin n, ∃ b, (f b, ε b) = (lamAt h a, decide ((a : ℕ) < p)) := fun a => by
    have : (lamAt h a, decide ((a : ℕ) < p)) ∈ Finset.univ.image fun a : Fin n => (f a, ε a) := by
      rw [← hS]; exact Finset.mem_image_of_mem (fun a : Fin n => (lamAt h a, decide ((a : ℕ) < p))) (Finset.mem_univ a)
    obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
    exact ⟨b, hb⟩
  have e : f = fun a : Fin n => lamAt h a := by
    refine (StrictMono.range_inj hfs.dual_right hg.dual_right).1 ?_ |> fun e => funext fun a => congrFun e a
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := m1 a
      exact ⟨b, congrArg Prod.fst hb⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := m2 a
      exact ⟨b, congrArg Prod.fst hb⟩
  subst e
  refine ⟨hf a, ?_⟩
  obtain ⟨b, hb⟩ := m1 a
  obtain rfl : b = a := hg.injective (congrArg Prod.fst hb)
  exact (congrArg Prod.snd hb).symm

theorem holShape_of_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → HolShape (R.MW i σ) ∧ (∀ ρ, nNeg ((R.MW i σ).ε ρ) = (D.R.sigW ((i : ℕ) + 1)).2) ∧ ∃ w, WtIs (R.MW i σ) w := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ ht i σ hσ
  have hs : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := fun ρ => D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
    have := D.R.m_add_three_le_k
    have hi := i.2
    rw [rank_Wc i]
    simp only [Ranks.sigW, Ranks.r]
    omega
  have key : ∀ ρ a, (R.MW i σ).lam ρ a = (Formalism.L2.NTheta.lamAt (D.hc (lab σ ρ)) a : ℝ) ∧
      (R.MW i σ).ε ρ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun ρ a => by
    have he := (R.MW i σ).enum ρ
    unfold Links.parAt at he
    rw [if_pos ((GlobalTheory.ConjReading.branch_of_pins T ht.alg ht.laws.pins σ ρ).1 hσ)] at he
    rw [← hs ρ]
    exact isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs ρ]; exact hr) he a
  have hc : ∀ ρ, Formalism.QuantumDeterminants.IsHCParam ((R.MW i σ).lam ρ) := fun ρ => by
    refine ⟨((R.MW i σ).enum ρ).1, fun a => ?_⟩
    obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int (D.hc (lab σ ρ)) a
    obtain ⟨s, hs'⟩ := Formalism.L2.NTheta.odd_r D.R
    refine ⟨z - s, ?_⟩
    have hn : (((Wc D i).rank : ℕ) : ℝ) = 2 * s + 1 := by rw [rank_Wc i, hs']; push_cast; rfl
    rw [(key ρ a).1, hz, hn]
    push_cast
    ring
  refine ⟨fun ρ => ⟨hc ρ, _, by omega, fun a => (key ρ a).2⟩, fun ρ => ?_, ?_⟩
  · rw [nNeg_shape (by omega) fun a => (key ρ a).2]
    omega
  · choose w hw using fun ρ a => Formalism.QuantumDeterminants.low_k_integrable_holds _ ((R.MW i σ).ε ρ) _ (hc ρ).2 a
    exact ⟨fun ρ c => w ρ (revNeg ((R.MW i σ).ε ρ) (arr (nNeg ((R.MW i σ).ε ρ)) c)), fun ρ c => (hw ρ _).symm⟩

end GlobalTheory.HolDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyConeIdealEqFieldDegree
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.CompHt

theorem finrank_quotPiece_coneIdeal_eq_finrank_map {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    {N : ℕ} (y : Fin N → Ω) (n : ℕ) :
    Module.finrank K (quotPiece (coneIdeal K y) n) =
      Module.finrank K ((homogeneousSubmodule (Fin N) K n).map
        (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap) := by
  have e1 := finrank_quotPiece_add (coneIdeal K y) n
  have e2 := GradedHilbert.finrank_map_add_finrank_inf_ker
    (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap (homogeneousSubmodule (Fin N) K n)
  have e3 : ((coneIdeal K y).restrictScalars K ⊓ homogeneousSubmodule (Fin N) K n : Submodule K _)
      = homogeneousSubmodule (Fin N) K n ⊓
        LinearMap.ker (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
    ext g
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_homogeneousSubmodule,
      LinearMap.mem_ker, AlgHom.toLinearMap_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (mem_coneIdeal_of_isHomogeneous y h2).1 h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(mem_coneIdeal_of_isHomogeneous y h1).2 h2, h1⟩
  rw [e3] at e1
  omega

theorem aeval_mem_map_homogeneousSubmodule {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    {N : ℕ} (y : Fin N → Ω) {j : Fin N} (hj : y j = 1) (g : MvPolynomial (Fin N) K) {n : ℕ}
    (hn : g.totalDegree ≤ n) :
    aeval y g ∈ (homogeneousSubmodule (Fin N) K n).map
        (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
  rw [← sum_homogeneousComponent g, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hi' : i ≤ n := by
    have := Finset.mem_range.1 hi
    omega
  refine ⟨homogeneousComponent i g * X j ^ (n - i), ?_, by simp [hj]⟩
  have := (homogeneousComponent_isHomogeneous i g).mul ((isHomogeneous_X K j).pow (n - i))
  rw [one_mul, Nat.add_sub_cancel' hi'] at this
  exact this

theorem idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin (K : Type) [Field K] (N : ℕ)
    (y : Fin N → AlgebraicClosure K) (j : Fin N) (hj : y j = 1) :
    GlobalTheory.idealHilbertPoly (coneIdeal K y) =
      Polynomial.C (Module.finrank K (IntermediateField.adjoin K (Set.range y)) : ℚ) := by
  have halg : ∀ x ∈ Set.range y, IsAlgebraic K x := fun x _ => Algebra.IsAlgebraic.isAlgebraic x
  haveI : FiniteDimensional K (IntermediateField.adjoin K (Set.range y)) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral
  set S : Submodule K (AlgebraicClosure K) :=
    Subalgebra.toSubmodule (IntermediateField.adjoin K (Set.range y)).toSubalgebra with hS
  have hmem : ∀ x, x ∈ S ↔ ∃ g : MvPolynomial (Fin N) K, aeval y g = x := by
    intro x
    rw [hS, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, Subalgebra.mem_toSubmodule,
      Algebra.adjoin_range_eq_range_aeval]
    rfl
  have hfin : Module.Finite K S := ‹FiniteDimensional K (IntermediateField.adjoin K (Set.range y))›
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hfin
  have hev : ∀ᶠ n : ℕ in atTop, ∀ x ∈ s, x ∈ (homogeneousSubmodule (Fin N) K n).map
      (aeval y : MvPolynomial (Fin N) K →ₐ[K] AlgebraicClosure K).toLinearMap := by
    rw [eventually_all_finset]
    intro x hx
    obtain ⟨g, rfl⟩ := (hmem x).1 (hs ▸ Submodule.subset_span hx)
    filter_upwards [eventually_ge_atTop g.totalDegree] with n hn
    exact aeval_mem_map_homogeneousSubmodule y hj g hn
  apply polynomial_eq_of_eventually_eval_nat
  filter_upwards [eventually_finrank_quotPiece (isHomogeneous_coneIdeal (K := K) y), hev]
    with n h1 h2
  have hW : (homogeneousSubmodule (Fin N) K n).map
      (aeval y : MvPolynomial (Fin N) K →ₐ[K] AlgebraicClosure K).toLinearMap = S := by
    apply le_antisymm
    · rintro _ ⟨g, -, rfl⟩
      exact (hmem _).2 ⟨g, rfl⟩
    · rw [← hs, Submodule.span_le]
      exact fun x hx => h2 x hx
  rw [← h1, finrank_quotPiece_coneIdeal_eq_finrank_map, hW, Polynomial.eval_C]
  rfl

end GlobalTheory.CompHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageIdealEqConeIdealOfGeneric
section
set_option autoImplicit false

namespace GlobalTheory.CompHt

open MvPolynomial NumberField Module GlobalTheory.ChowHt GlobalTheory.CompHt
open AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G GlobalTheory.Twist GlobalTheory.Adelic
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

theorem form_eq_zero_of_generic {K : Type} [Field K] (S : LinSys K) [IsReduced S.Y] {η : S.Y}
    (hη : IsGenericPoint η Set.univ) {d : ℕ} {g : MvPolynomial (Fin S.N) K} (hg : g.IsHomogeneous d)
    (h : η ∉ nonzeroLocus (S.form hg)) : S.form hg = 0 := by
  refine zglobal_ext fun i => ?_
  rw [zfun_zero, ← basicOpen_eq_bot_iff, basicOpen_zfun, eq_bot_iff]
  intro y hy
  exact (h ((hη.mem_open_set_iff (nonzeroLocus (S.form hg)).isOpen).2 ⟨y, trivial, hy.2⟩)).elim

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem imageIdeal_eq_coneIdeal_of_generic (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (S : LinSys K)
    [IsIntegral S.Y] (x : S.Pt Ω) (hx : IsGenericPoint (ptOf x.1) Set.univ) (a : Ω) (y : Fin S.N → Ω) (ha : a ≠ 0)
    (h : S.coords x.1 = a • y) : S.imageIdeal = coneIdeal K y := by
  rw [← coneIdeal_smul ha y, ← h]
  have key : ∀ {d : ℕ} {g : MvPolynomial (Fin S.N) K} (_ : g.IsHomogeneous d),
      g ∈ S.imageIdeal ↔ g ∈ coneIdeal K (S.coords x.1) := fun {d g} hg => by
    rw [mem_coneIdeal_of_isHomogeneous _ hg, aeval_def,
      ← congrArg (fun φ => eval₂ φ (S.coords x.1) g) (LinSys.baseHom_ptOver x)]
    refine ⟨S.eval₂_coords_eq_zero x.1, fun h0 => (S.mem_imageIdeal_iff hg).2
      (form_eq_zero_of_generic S hx hg fun hm => ?_)⟩
    exact (S.powVal_ne_zero_iff x.1 _).2 hm ((S.powVal_form x.1 hg).trans h0)
  ext g
  rw [S.isHomogeneous_imageIdeal.mem_iff, (isHomogeneous_coneIdeal (K := K) (S.coords x.1)).mem_iff]
  exact forall_congr' fun d => key (DirectSum.decompose (homogeneousSubmodule (Fin S.N) K) g d).2

end GlobalTheory.CompHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
section
noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

abbrev Qv (v : AwayP p) : Type := v.1.adicCompletion ℚ

abbrev Gv (G : HTGroup p) (v : AwayP p) : Type := UPts G.star (Qv v)

def piV (G : HTGroup p) (v : AwayP p) : G.GAf →* Gv G v := ubcMap (AfP.eval v)

def basV (G : HTGroup p) (v : AwayP p) : Module.Basis (Fin (Module.finrank ℚ G.C)) (Qv v) (Qv v ⊗[ℚ] G.C) :=
  Algebra.TensorProduct.basis (Qv v) (Module.finBasis ℚ G.C)

def IsIntV (G : HTGroup p) (v : AwayP p) (y : Qv v ⊗[ℚ] G.C) : Prop :=
  ∀ i, (basV G v).repr y i ∈ v.1.adicCompletionIntegers ℚ

def IntV (G : HTGroup p) (v : AwayP p) : Set (Gv G v) :=
  {g | IsIntV G v (((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
    IsIntV G v ((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1)⁻¹ : (Qv v ⊗[ℚ] G.C)ˣ) : Qv v ⊗[ℚ] G.C) ∧
    ((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2 : (Qv v)ˣ) : Qv v) ∈ v.1.adicCompletionIntegers ℚ) ∧
    (((((g : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).2)⁻¹ : (Qv v)ˣ) : Qv v) ∈ v.1.adicCompletionIntegers ℚ)}

theorem inv_mem_IntV (G : HTGroup p) (v : AwayP p) {g : Gv G v} (h : g ∈ IntV G v) : g⁻¹ ∈ IntV G v := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h2
  · simpa using h1
  · exact h4
  · simpa using h3

end GlobalTheory.OrbFinAf
end
end

