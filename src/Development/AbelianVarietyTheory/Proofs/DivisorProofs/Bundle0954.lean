import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0921
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomConjOfTraceEqHarrisTaylorOrder
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem rep_conj_of_trace_eq : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ) (ρ ρ' : D.O →+* Matrix (Fin g) (Fin g) ℂ), (∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (ρ' (algebraMap (𝓞 D.F) D.O c)).trace) → ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ a, ρ' a * h = h * ρ a := by
  classical
  intro p _ D g ρ ρ' htr
  obtain ⟨φ, hφ, hspan⟩ := GlobalTheory.T.exists_ringHom_order_pi_matrix_embeddings p D
  haveI := D.freeO
  haveI := D.finO
  have hdim : Module.finrank ℂ ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) = Module.finrank ℤ D.O := by
    rw [Module.finrank_pi_fintype, D.rankO]
    simp [Module.finrank_matrix, NumberField.Embeddings.card]
    ring
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_algHom_extend_ringHom_of_span_eq_top_of_finrank_eq D.O _ _ φ ρ hspan hdim
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_algHom_extend_ringHom_of_span_eq_top_of_finrank_eq D.O _ _ φ ρ' hspan hdim
  have key : ∀ (s : ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (f : (D.F →+* ℂ) → ℂ),
      (s (fun τ => Matrix.scalar (Fin D.m) (f τ))).trace = ∑ τ, f τ * (s (Pi.single τ 1)).trace := by
    intro s f
    have : (fun τ => Matrix.scalar (Fin D.m) (f τ)) = ∑ τ, f τ • (Pi.single τ 1 : (D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) := by
      ext τ i j
      simp [Finset.sum_apply, Pi.single_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    rw [this, map_sum, Matrix.trace_sum]
    simp [map_smul, Matrix.trace_smul]
  let χ : (D.F →+* ℂ) → (𝓞 D.F →* ℂ) := fun τ => (τ.comp (algebraMap (𝓞 D.F) D.F)).toMonoidHom
  have hχ : Function.Injective χ := by
    intro τ τ' h
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 D.F))
    ext x
    exact DFunLike.congr_fun h x
  have hlin := (linearIndependent_monoidHom (𝓞 D.F) ℂ).comp χ hχ
  rw [Fintype.linearIndependent_iff] at hlin
  have heq : ∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace := by
    have := hlin (fun τ => (σ (Pi.single τ 1)).trace - (σ' (Pi.single τ 1)).trace) (by
      funext c
      have h1 := htr c
      have hφ' : φ (algebraMap (𝓞 D.F) D.O c) = fun τ => Matrix.scalar (Fin D.m) (τ (c : D.F)) := funext (hφ c)
      rw [← hσ, ← hσ', hφ', key, key] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
      simp only [χ, MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      simpa [mul_comm] using h1)
    intro τ
    exact sub_eq_zero.mp (this τ)
  exact GlobalTheory.T.representations_equal_traces_conjugate (D.F →+* ℂ) D.m g D.m_pos σ σ' heq |>.imp fun h hh => ⟨hh.1, fun a => by rw [← hσ, ← hσ']; exact hh.2 _⟩

end GlobalTheory.UPel.HT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomKerEqIffFrobeniusTwist
section
open Polynomial

namespace GlobalTheory.FrobOrbit

theorem card_le_of_pow_eq_self {k : Type} [Field k] {n : ℕ} (hn : 1 < n) (Z : Finset k)
    (hZ : ∀ x ∈ Z, x ^ n = x) : Z.card ≤ n := by
  have hd := FiniteField.X_pow_card_sub_X_natDegree_eq k hn
  have hne : (X ^ n - X : k[X]) ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hd
    omega
  have := card_le_degree_of_subset_roots (p := (X ^ n - X : k[X])) (Z := Z) (by
    intro x hx
    rw [mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X, hZ x hx, sub_self])
  rwa [hd] at this

theorem field_case (K k : Type) [Field K] [Fintype K] [Field k] (p : ℕ) [hp : Fact p.Prime]
    [CharP k p] (f : K →+* k) (h : ℕ) (hh : 0 < h) (hc : Fintype.card K = p ^ h) :
    (∀ a, f a ^ p ^ h = f a) ∧ (∀ x : k, x ^ p ^ h = x → ∃ a, f a = x) ∧
    (∀ s t : ℕ, s < h → t < h → (∀ a, f a ^ p ^ s = f a ^ p ^ t) → s = t) ∧
    ∀ g : K →+* k, ∃ s : ℕ, s < h ∧ ∀ a, g a = f a ^ p ^ s := by
  classical
  have h1 : 1 < p := hp.out.one_lt
  have hfix : ∀ a, f a ^ p ^ h = f a := fun a => by
    rw [← map_pow, ← hc, FiniteField.pow_card]
  have himg : (Finset.univ.image f).card = p ^ h := by
    rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, hc]
  have hlt : ∀ s t : ℕ, s < t → t < h → ¬ ∀ a, f a ^ p ^ s = f a ^ p ^ t := by
    intro s t hst hth H
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hst
    have hle := card_le_of_pow_eq_self (k := k) (n := p ^ (d + 1))
      (Nat.one_lt_pow (Nat.succ_ne_zero d) h1) (Finset.univ.image f) (by
        intro x hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
        apply (iterateFrobenius k p s).injective
        rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, H a]
        congr 2
        omega)
    rw [himg] at hle
    have := (Nat.pow_le_pow_iff_right h1).1 hle
    omega
  have hinj : ∀ s t : ℕ, s < h → t < h → (∀ a, f a ^ p ^ s = f a ^ p ^ t) → s = t := by
    intro s t hs ht H
    rcases lt_trichotomy s t with hst | hst | hst
    · exact absurd H (hlt s t hst ht)
    · exact hst
    · exact absurd (fun a => (H a).symm) (hlt t s hst hs)
  refine ⟨hfix, ?_, hinj, ?_⟩
  · intro x hx
    by_contra hne
    have hx' : x ∉ Finset.univ.image f := by
      intro hm
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hm
      exact hne ⟨a, ha⟩
    have hle := card_le_of_pow_eq_self (k := k) (n := p ^ h)
      (Nat.one_lt_pow hh.ne' h1) (insert x (Finset.univ.image f)) (by
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact hx
        · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
          exact hfix a)
    rw [Finset.card_insert_of_notMem hx', himg] at hle
    omega
  · intro g
    haveI : CharP K p := RingHom.charP f f.injective p
    letI : Algebra (ZMod p) K := ZMod.algebra K p
    letI : Algebra (ZMod p) k := ZMod.algebra k p
    let toAlg : (K →+* k) → (K →ₐ[ZMod p] k) := fun φ =>
      { φ with
        commutes' := fun r =>
          congrArg (fun ψ : ZMod p →+* k => ψ r)
            (Subsingleton.elim (φ.comp (algebraMap (ZMod p) K)) (algebraMap (ZMod p) k)) }
    have toAlg_apply : ∀ φ a, toAlg φ a = φ a := fun _ _ => rfl
    have hrank : Module.finrank (ZMod p) K = h := by
      have := Module.card_eq_pow_finrank (K := ZMod p) (V := K)
      rw [ZMod.card, hc] at this
      exact (Nat.pow_right_injective h1 this).symm
    let F : Fin h → (K →ₐ[ZMod p] k) := fun s => toAlg ((iterateFrobenius k p s.val).comp f)
    have hF : ∀ s a, F s a = f a ^ p ^ s.val := fun s a => rfl
    have hFinj : Function.Injective F := by
      intro s t hst
      apply Fin.ext
      apply hinj _ _ s.2 t.2
      intro a
      rw [← hF, ← hF, hst]
    have hbij := hFinj.bijective_of_nat_card_le (by
      have := card_algHom_le_finrank (ZMod p) K k
      rw [hrank] at this
      simpa using this)
    obtain ⟨s, hs⟩ := hbij.2 (toAlg g)
    exact ⟨s.val, s.2, fun a => by rw [← hF, hs, toAlg_apply]⟩

theorem ringHom_ker_eq_iff_frobenius_twist :
    ∀ (R k : Type) [CommRing R] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : R →+* k) (h : ℕ),
      0 < h → Nat.card (R ⧸ RingHom.ker f) = p ^ h →
      (∀ x : k, x ^ p ^ h = x → ∃ a, f a = x) ∧
      ∃ F : ZMod h → (R →+* k), (∀ s a, F s a = f a ^ p ^ s.val) ∧
        (∀ s a, F (s + 1) a = F s a ^ p) ∧ Function.Injective F ∧
        ∀ g : R →+* k, RingHom.ker g = RingHom.ker f ↔ ∃ s, F s = g := by
  intro R k _ _ p hp _ f h hh hc
  haveI : NeZero h := ⟨hh.ne'⟩
  haveI : Finite (R ⧸ RingHom.ker f) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.out.ne_zero)
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  haveI : (RingHom.ker f).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isDomain_to_isField _)
  letI : Field (R ⧸ RingHom.ker f) := Ideal.Quotient.field _
  letI : Fintype (R ⧸ RingHom.ker f) := Fintype.ofFinite _
  obtain ⟨hfix, hsurj, hinj, hall⟩ := field_case (R ⧸ RingHom.ker f) k p (RingHom.kerLift f) h hh
    (by rw [← Nat.card_eq_fintype_card, hc])
  have hmk : ∀ a, RingHom.kerLift f (Ideal.Quotient.mk _ a) = f a := RingHom.kerLift_mk f
  have hfix' : ∀ a, f a ^ p ^ h = f a := fun a => by
    have := hfix (Ideal.Quotient.mk _ a)
    exact this
  have hmod : ∀ (a : R) (n : ℕ), f a ^ p ^ (n % h) = f a ^ p ^ n := by
    intro a n
    have hm : ∀ m : ℕ, f a ^ p ^ (h * m) = f a := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hfix']
    conv_rhs => rw [← Nat.div_add_mod n h, pow_add, pow_mul, hm]
  refine ⟨fun x hx => ?_, fun s => (iterateFrobenius k p s.val).comp f, fun s a => rfl,
    fun s a => ?_, fun s t hst => ?_, fun g => ⟨fun hg => ?_, ?_⟩⟩
  · obtain ⟨a, ha⟩ := hsurj x hx
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨b, ha⟩
  · change f a ^ p ^ (s + 1).val = (f a ^ p ^ s.val) ^ p
    have hv : (s + 1).val = (s.val + 1) % h := by
      rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
    rw [hv, hmod, pow_succ, pow_mul]
  · apply ZMod.val_injective h
    apply hinj _ _ (ZMod.val_lt s) (ZMod.val_lt t)
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact congrArg (fun φ : R →+* k => φ b) hst
  · obtain ⟨s, hs, hgs⟩ := hall (Ideal.Quotient.lift (RingHom.ker f) g
      (fun a ha => by rw [← hg] at ha; exact ha))
    refine ⟨(s : ZMod h), RingHom.ext fun a => ?_⟩
    change f a ^ p ^ ((s : ZMod h)).val = g a
    rw [ZMod.val_cast_of_lt hs]
    exact (hgs (Ideal.Quotient.mk _ a)).symm
  · rintro ⟨s, rfl⟩
    ext a
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change f a ^ p ^ s.val = 0 ↔ f a = 0
    exact pow_eq_zero_iff (pow_ne_zero _ hp.out.ne_zero)

end GlobalTheory.FrobOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
section
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep

namespace GlobalTheory.SphGal

open GlobalTheory.LFun GlobalTheory.PRep

theorem satEig_map_mul (q m : ℕ) (B : Multiset ℂˣ) (z : ℂˣ) (j : ℕ) :
    satEig q m (B.map (· * z)) j = (z : ℂ) ^ j * satEig q m B j := by
  have h := Multiset.pow_smul_esymm (z : ℂ) j (B.map fun b : ℂˣ => (b : ℂ))
  simp only [smul_eq_mul, Multiset.map_map, Function.comp_def] at h
  simp only [satEig, Multiset.map_map, Function.comp_def, Units.val_mul]
  rw [mul_left_comm, h]
  simp only [mul_comm]

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {m : ℕ}

theorem isUnitAt_det_of_mem {k : GL (Fin m) (w.adicCompletion E)} (hk : k ∈ KGL w m) :
    Formalism.L2.Host.IsUnitAt w (Matrix.GeneralLinearGroup.det k) := by
  obtain ⟨k, rfl⟩ := hk
  have e : ((Matrix.GeneralLinearGroup.det (bc (Ov E w).subtype k) : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      ((Matrix.GeneralLinearGroup.det k : (Ov E w)ˣ) : Ov E w) :=
    ((Ov E w).subtype.map_det k.val).symm
  change Valued.v _ = 1
  rw [e]
  generalize Matrix.GeneralLinearGroup.det k = u
  have h1 : Valued.v ((u : Ov E w) : w.adicCompletion E) ≤ 1 := (u : Ov E w).2
  have h2 : Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) ≤ 1 := ((u⁻¹ : (Ov E w)ˣ) : Ov E w).2
  have h3 : Valued.v ((u : Ov E w) : w.adicCompletion E) *
      Valued.v (((u⁻¹ : (Ov E w)ˣ) : Ov E w) : w.adicCompletion E) = 1 := by
    rw [← map_mul, ← Subring.coe_mul, Units.mul_inv]; simp
  exact le_antisymm h1 (h3 ▸ mul_le_of_le_one_right' h2)

theorem det_diagJ {L : Type} [Field L] (ϖ : L) {j : ℕ} (hj : j ≤ m) : (diagJ m ϖ j).det = ϖ ^ j := by
  rw [diagJ, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    Fin.card_filter_val_lt, min_eq_right hj]

theorem loc_det_of_Tj {χ : Formalism.L2.Host.HChar E} (hχ : χ.UnrAt w) {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ)
    {j : ℕ} (hj : j ≤ m) {g : GL (Fin m) (w.adicCompletion E)} (hg : Tj ℂ m (Ov E w) ϖ j g ≠ 0) :
    χ.loc w (Matrix.GeneralLinearGroup.det g) = χ.val w ^ j := by
  obtain ⟨a, ha, b, hb, e⟩ := Set.mem_of_indicator_ne_zero hg
  have h0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  have e2 : Matrix.GeneralLinearGroup.det g =
      Matrix.GeneralLinearGroup.det a * Units.mk0 ϖ h0 ^ j * Matrix.GeneralLinearGroup.det b := by
    apply Units.ext
    change g.val.det = a.val.det * _ * b.val.det
    rw [e, Matrix.det_mul, Matrix.det_mul, det_diagJ ϖ hj]
    simp
  rw [e2, map_mul, map_mul, hχ _ (isUnitAt_det_of_mem ha), hχ _ (isUnitAt_det_of_mem hb), map_pow,
    χ.val_eq hχ (Units.mk0 ϖ h0) hϖ, one_mul, mul_one]

theorem hasSatGL_of_twist {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin m) (w.adicCompletion E)) V}
    {ρ' : Representation ℂ (GL (Fin m) (w.adicCompletion E)) W} {χ : Formalism.L2.Host.HChar E} (hχ : χ.UnrAt w)
    (T : V ≃ₗ[ℂ] W)
    (hT : ∀ g x, ρ' g (T x) = ((χ.loc w (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (ρ g x))
    {B : Multiset ℂˣ} (h : HasSatGL w ρ B) : HasSatGL w ρ' (B.map (· * χ.val w)) := by
  have hf : ∀ x, T x ∈ fixed ρ' (KGL w m) ↔ x ∈ fixed ρ (KGL w m) := fun x => by
    simp only [GlobalTheory.LGrp.mem_fixed]
    refine forall₂_congr fun k hk => ?_
    rw [hT, hχ _ (isUnitAt_det_of_mem hk), Units.val_one, one_smul, T.injective.eq_iff]
  constructor
  · obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h.1
    exact (Submodule.ne_bot_iff _).2 ⟨T x, (hf x).2 hx, (map_ne_zero_iff T T.injective).2 h0⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    have hx := h.2 x ((hf x).1 hy) ((map_ne_zero_iff T T.injective).1 h0)
    refine ⟨h0, hy, by rw [Multiset.card_map, hx.2.2.1], fun ϖ hϖ j hj => ?_⟩
    rw [satEig_map_mul, mul_smul, ← map_smul T, ← hx.2.2.2 ϖ hϖ j hj, heckeVec, heckeVec]
    have e := T.toAddEquiv.map_finsum
      (fun c : _ ⧸ KGL w m => Tj ℂ m (Ov E w) ϖ j c.out • ρ c.out x)
    rw [show T _ = _ from e, smul_finsum]
    refine finsum_congr fun c => ?_
    by_cases hc : Tj ℂ m (Ov E w) ϖ j c.out = 0
    · simp [hc]
    · rw [hT, loc_det_of_Tj hχ hϖ hj hc, smul_comm]
      simp

theorem hasSatGL_twist (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π : CuspSub E m)
    (χ : Formalism.L2.Host.HChar E) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) (hχ : χ.UnrAt w)
    (h : GlobalTheory.LFun.HasSatGL w (π.locRep w) B) :
    GlobalTheory.LFun.HasSatGL w ((π.twist χ).locRep w) (B.map (· * χ.val w)) := by
  refine hasSatGL_of_twist hχ (π.toTwist χ) (fun g x => ?_) h
  rw [CuspSub.locRep_eq, CuspSub.op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, CuspSub.chiDet_locGL]
  rfl

end GlobalTheory.SphGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerDifferentiableOnStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarPoincareDetRatioPower_differentiableOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ k : ℕ, DifferentiableOn ℂ (qS X x0 k) X.dom := by
  first | exact @GlobalTheory.ScalarPoin.Holo.qS_holomorphicOn | exact GlobalTheory.ScalarPoin.Holo.qS_holomorphicOn | (intros; apply GlobalTheory.ScalarPoin.Holo.qS_holomorphicOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarPoincareDetRatioPowerRmulBorelStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst GlobalTheory.ScalarPoin MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarPoincareDetRatioPower_rmul_borel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (k : ℕ) (x b : Frame X.Ψ r), b ∈ Bor X.Ψ r → qS X x0 k (rmul x b) = bchar (laS X k) b * qS X x0 k x := by
  first | exact @GlobalTheory.ScalarPoin.qS_rmul | exact GlobalTheory.ScalarPoin.qS_rmul | (intros; apply GlobalTheory.ScalarPoin.qS_rmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesCoeffUniformlyContinuousInCoeffsProof
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.CoeffCont

open MvPowerSeries

theorem coe_le_add {a b : WithTop ℝ} {x y : ℝ} (ha : (x : WithTop ℝ) ≤ a) (hb : (y : WithTop ℝ) ≤ b) :
    ((x + y : ℝ) : WithTop ℝ) ≤ a + b := by
  rw [WithTop.coe_add]; exact add_le_add ha hb

theorem poly_bound {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {κ : Type} (Q : MvPolynomial κ C) :
    ∃ K : ℝ, ∀ (N : ℝ) (s s' : κ → C), (∀ k, (0 : WithTop ℝ) ≤ v (s k)) → (∀ k, (0 : WithTop ℝ) ≤ v (s' k)) →
      (∀ k, ((N : ℝ) : WithTop ℝ) ≤ v (s k - s' k)) →
      ((N - K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval s Q - MvPolynomial.eval s' Q) ∧
      ((-K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval s Q) := by
  induction Q using MvPolynomial.induction_on
  · rename_i c
    by_cases ht : v c = ⊤
    · refine ⟨0, fun N s s' _ _ _ => ?_⟩
      simp only [MvPolynomial.eval_C, sub_self, AddValuation.map_zero, ht, le_top, and_self]
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ht
      refine ⟨-r, fun N s s' _ _ _ => ?_⟩
      simp only [MvPolynomial.eval_C, sub_self, AddValuation.map_zero, ← hr, le_top, neg_neg, le_refl, and_self]
  · rename_i p q hp hq
    obtain ⟨K₁, h₁⟩ := hp
    obtain ⟨K₂, h₂⟩ := hq
    refine ⟨max K₁ K₂, fun N s s' hs hs' hss => ?_⟩
    obtain ⟨a₁, b₁⟩ := h₁ N s s' hs hs' hss
    obtain ⟨a₂, b₂⟩ := h₂ N s s' hs hs' hss
    rw [map_add (MvPolynomial.eval s), map_add (MvPolynomial.eval s')]
    constructor
    · have e : MvPolynomial.eval s p + MvPolynomial.eval s q - (MvPolynomial.eval s' p + MvPolynomial.eval s' q) =
          (MvPolynomial.eval s p - MvPolynomial.eval s' p) + (MvPolynomial.eval s q - MvPolynomial.eval s' q) := by ring
      rw [e]
      refine le_trans (le_min ?_ ?_) (v.map_add _ _)
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_left K₁ K₂])) a₁
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_right K₁ K₂])) a₂
    · refine le_trans (le_min ?_ ?_) (v.map_add _ _)
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_left K₁ K₂])) b₁
      · exact le_trans (WithTop.coe_le_coe.mpr (by linarith [le_max_right K₁ K₂])) b₂
  · rename_i p k hp
    obtain ⟨K, h⟩ := hp
    refine ⟨K, fun N s s' hs hs' hss => ?_⟩
    obtain ⟨a, b⟩ := h N s s' hs hs' hss
    rw [map_mul (MvPolynomial.eval s), map_mul (MvPolynomial.eval s'), MvPolynomial.eval_X, MvPolynomial.eval_X]
    constructor
    · have e : MvPolynomial.eval s p * s k - MvPolynomial.eval s' p * s' k =
          (MvPolynomial.eval s p - MvPolynomial.eval s' p) * s k + MvPolynomial.eval s' p * (s k - s' k) := by ring
      rw [e]
      refine le_trans (le_min ?_ ?_) (v.map_add _ _)
      · rw [v.map_mul]
        have := coe_le_add (y := 0) a (hs k)
        rwa [add_zero] at this
      · rw [v.map_mul]
        have := coe_le_add (h N s' s' hs' hs' (fun k => by rw [sub_self, v.map_zero]; exact le_top)).2 (hss k)
        have e2 : (-K + N : ℝ) = N - K := by ring
        rw [e2] at this
        exact this
    · rw [v.map_mul]
      have := coe_le_add (y := 0) b (hs k)
      rwa [add_zero] at this

theorem coeff_subst_eq_eval {C : Type} [Field C] {τ σ ι : Type} [Fintype τ] [Fintype ι]
    (W : MvPowerSeries τ C) (g : ι → MvPowerSeries σ C) (hg : ∀ i, constantCoeff (g i) = 0) (α : σ →₀ ℕ) :
    ∃ Q : MvPolynomial (τ × ι) C, ∀ s : τ → ι → C,
      coeff α (subst (fun q => ∑ i, s q i • g i) W : MvPowerSeries σ C) =
        MvPolynomial.eval (fun x => s x.1 x.2) Q := by
  classical
  let G : ι → MvPowerSeries σ (MvPolynomial (τ × ι) C) := fun i => (g i).map MvPolynomial.C
  let a : τ → MvPowerSeries σ (MvPolynomial (τ × ι) C) :=
    fun q => ∑ i, (MvPolynomial.X (q, i) : MvPolynomial (τ × ι) C) • G i
  have hG : ∀ i, constantCoeff (G i) = 0 := fun i => by simp [G, hg]
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero (fun q => by simp [a, hG])
  refine ⟨coeff α (subst a (W.map (MvPolynomial.C : C →+* MvPolynomial (τ × ι) C)) :
    MvPowerSeries σ (MvPolynomial (τ × ι) C)), fun s => ?_⟩
  have h1 := congrArg (coeff α) (map_subst ha (h := MvPolynomial.eval (fun x : τ × ι => s x.1 x.2))
    (W.map (MvPolynomial.C : C →+* MvPolynomial (τ × ι) C)))
  rw [coeff_map] at h1
  have hW : (W.map (MvPolynomial.C : C →+* MvPolynomial (τ × ι) C)).map
      (MvPolynomial.eval (fun x : τ × ι => s x.1 x.2)) = W := by
    ext n; simp [coeff_map]
  have hA : (fun q => (a q).map (MvPolynomial.eval (fun x : τ × ι => s x.1 x.2))) =
      fun q => ∑ i, s q i • g i := by
    funext q; ext n; simp [a, G, coeff_map, map_sum]
  rw [h1, hW, hA]

end GlobalTheory.IsoTriv.CoeffCont

namespace GlobalTheory.IsoTriv

open MvPowerSeries

theorem contSt_holds : ContSt := by
  intro C _ v τ σ ι _ _ _ W g hg α
  obtain ⟨Q, hQ⟩ := CoeffCont.coeff_subst_eq_eval W g hg α
  obtain ⟨K, hK⟩ := CoeffCont.poly_bound v Q
  refine ⟨⌈K⌉₊, fun s s' hs hs' hss => ?_⟩
  rw [hQ, hQ]
  have h := (hK (⌈K⌉₊ : ℝ) (fun x => s x.1 x.2) (fun x => s' x.1 x.2) (fun x => hs _ _) (fun x => hs' _ _)
    (fun x => hss _ _)).1
  show (0 : WithTop ℝ) ≤ _
  refine le_trans ?_ h
  rw [← WithTop.coe_zero, WithTop.coe_le_coe]
  linarith [Nat.le_ceil K]

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineCurveTateTwistCohomologySubsingleton
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

namespace GlobalTheory.EtC.AffineCurve

theorem subsingleton_of_three_le : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ n i : ℤ, 3 ≤ n →
    Subsingleton (Ht q (sp B) n i) := by
  intro q _ k B _ _ _ _ _ _ hq n i hn
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  by_cases hB : IsField B
  · exact GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) B (GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed k B hB) (tw q i) n (by omega)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
    suffices h : ∀ x : Ht q (sp B) (m + 1) i, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
    intro x
    obtain ⟨_, _⟩ := GlobalTheory.T.exists_isAlgebraic_ratFunc_fractionRing_dedekind k B hB
    have hqK : IsUnit (q : FractionRing B) := by simpa using hqB.map (algebraMap B (FractionRing B))
    have h1 : pull _ (spMap (algebraMap B (FractionRing B))) _ _ x = 0 :=
      (GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc q k (FractionRing B) hqK (m + 1) i (by omega)).elim _ _
    obtain ⟨f, hf0, hfu, hxf⟩ := GlobalTheory.T.class_vanishes_away_nonzero_nonunit_domain q B hB hqB (m + 1) i x h1
    obtain ⟨A', _, _, _, hA', hxA'⟩ := GlobalTheory.T.etale_local_vanishing_cohomology q k B hq f hf0 hfu (m + 1) i (by omega) x
    obtain ⟨δ, hex, hkill⟩ := GlobalTheory.T.mayer_vietoris_exact_etale q B A' f hA' m i
    obtain ⟨z, rfl⟩ := (hex x).mp (by simp [hxf, hxA'])
    obtain ⟨A'', _, _, _, φ, hA'', hz⟩ := GlobalTheory.T.higherDegree_class_dies_on_finer_etaleNeighbourhood q k B hq f hf0 hfu A' hA' m i (by omega) z
    exact hkill A'' φ hA'' z hz

end GlobalTheory.EtC.AffineCurve
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryPairActionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticForm_unitaryPairAction : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (x y : WO S T), symplO S T (actO S T g h x) (actO S T g h y) = symplO S T x y := by
  first | exact @GlobalTheory.SymplOInv.symplO_actO | exact GlobalTheory.SymplOInv.symplO_actO | (intros; apply GlobalTheory.SymplOInv.symplO_actO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRingOfIntegersActionSumEmbeddingsEigenspaceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_ringOfIntegers_action_sum_embeddings_eigenspace : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (c : 𝓞 F), (φ c).trace = ∑ τ : F →+* ℂ, (Module.finrank ℂ (eigSp φ τ) : ℂ) * τ (c : F) := by
  first | (exact @GlobalTheory.UPel.HT.LieType.trace_eq_sum_finrank_eigSp) | (exact GlobalTheory.UPel.HT.LieType.trace_eq_sum_finrank_eigSp) | (intros; apply GlobalTheory.UPel.HT.LieType.trace_eq_sum_finrank_eigSp  <;> assumption)
end

