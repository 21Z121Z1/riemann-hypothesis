import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.CoefUb
section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.coefUb :
    UpperTheory.V.Z.Kato.Joint.CoefUb := by
  intro l _ c c' F hF
  obtain ⟨d, h1, h2⟩ := (UpperTheory.V.HV.coefSup l).1 c c'
  obtain ⟨d', h3, h4⟩ := (UpperTheory.V.Th.Nm.inOf d).1 {x // x ∈ F} (fun x => x.1) (fun x => hF x.1 x.2)
  exact ⟨d', h1.trans h3, h2.trans h3, fun x hx => h4 ⟨x, hx⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.DetIne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open UpperTheory.V.Z.Kato.Joint Polynomial

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem cont_of_apply [IsAlgClosure ℚ Ω] {Y : Type} [TopologicalSpace Y] (ζ : Ω) (f : G ℚ Ω → Y)
    (h : ∀ s t : G ℚ Ω, s ζ = t ζ → f s = f t) : Continuous f := by
  have hint : IsIntegral ℚ ζ :=
    ((IsAlgClosure.isAlgebraic (R := ℚ) (K := Ω)).isAlgebraic ζ).isIntegral
  haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hH : IsOpen (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
      Set (Ω ≃ₐ[ℚ] Ω)) := IntermediateField.fixingSubgroup_isOpen _
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hU : IsOpen ((fun s : Ω ≃ₐ[ℚ] Ω => t⁻¹ * s) ⁻¹'
      (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
        Set (Ω ≃ₐ[ℚ] Ω))) := hH.preimage (continuous_mul_left _)
  have ht : t ∈ (fun s : Ω ≃ₐ[ℚ] Ω => t⁻¹ * s) ⁻¹'
      (((IntermediateField.adjoin ℚ {ζ}).fixingSubgroup : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
        Set (Ω ≃ₐ[ℚ] Ω)) := by
    simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact Subgroup.one_mem _
  refine (continuousAt_const (y := f t)).congr ?_
  filter_upwards [hU.mem_nhds ht] with s hs
  have h1 : (t⁻¹ * s) ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs ζ
      (IntermediateField.mem_adjoin_simple_self ℚ ζ)
  have h2 : s ζ = t ζ := by
    have h3 := congrArg t h1
    rw [AlgEquiv.mul_apply] at h3
    simpa using h3
  exact (h s t h2).symm

private theorem root_pow {M n : ℕ} (hM : M ≠ 0) {B : ValuationSubring Ω} {v : Pl} (hB : IsPlaceOver B v)
    (hv : ((M : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {s : G ℚ Ω} {ζ : Ω} (hζ : ζ ^ M = 1)
    (hs : ∀ x, B.valuation x ≤ 1 → B.valuation (s x - x ^ n) < 1) : s ζ = ζ ^ n := by
  have hN : ¬ B.valuation (M : Ω) < 1 := fun h => hv ((hB _).1 (by simpa using h))
  refine eq_of_pow_eq_one B hN ?_ ?_ (hs ζ (valuation_eq_one_of_pow_eq_one B hM hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

private theorem expo_eq {M a b : ℕ} [NeZero M] {ζ : Ω} (hζ : IsPrimitiveRoot ζ M) (h : ζ ^ a = ζ ^ b) :
    (a : ZMod M) = b := by
  have hu := hζ.isUnit (NeZero.ne M)
  have h1 : IsPrimitiveRoot hu.unit M := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  have h2 : hu.unit ^ a = hu.unit ^ b := Units.ext (by simpa using h)
  rw [pow_eq_pow_iff_modEq, ← h1.eq_orderOf] at h2
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2

private theorem det_of_charpoly {K : Type} [Field K] (ι : K ≃+* ℂ) {A : Matrix (Fin 2) (Fin 2) K} {a d : ℂ}
    (h : A.charpoly.map ι.toRingHom = X ^ 2 - C a * X + C d) : ι A.det = d := by
  have h0 := congrArg (fun p => Polynomial.coeff p 0) h
  simp [Polynomial.coeff_map] at h0
  rw [Matrix.det_eq_sign_charpoly_coeff]
  simp [h0]

end

theorem UpperTheory.V.Z.Kato.Joint.detIne :
    UpperTheory.V.Z.Kato.Joint.DetIne := by
  intro l _ Ω _ _ _ ι e S A W g χ hN hK hl hAtt s hs
  have hM : g.M ≠ 0 := g.pos.ne'
  haveI : NeZero g.M := ⟨hM⟩
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero ((g.M : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hM⟩
  haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hl0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω g.M
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  let F : Ω → Qbar l := fun x =>
    ι.symm (g.χ ((Classical.epsilon (fun k : ℕ => ζ ^ k = x) : ℕ) : ZMod g.M))
  have hF : ∀ k : ℕ, F (ζ ^ k) = ι.symm (g.χ k) := by
    intro k
    have h1 : ζ ^ (Classical.epsilon (fun j : ℕ => ζ ^ j = ζ ^ k)) = ζ ^ k :=
      Classical.epsilon_spec (p := fun j : ℕ => ζ ^ j = ζ ^ k) ⟨k, rfl⟩
    show ι.symm (g.χ _) = _
    rw [expo_eq hζ h1]
  let f : G ℚ Ω → Qbar l := fun t => ((dt W t * (χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l)
  have hf'c : Continuous (fun t : G ℚ Ω => F (t ζ)) :=
    cont_of_apply ζ _ (fun a b h => by simp only [h])
  have hcop : ∀ w : Pl, ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal → ((g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
    intro w hlw hmem
    obtain ⟨a, b, hab⟩ : IsCoprime (l : ℤ) (g.M : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hl)
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : (a : 𝓞 ℚ) * (l : 𝓞 ℚ) + (b : 𝓞 ℚ) * (g.M : 𝓞 ℚ) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 ℚ) hab
    rw [← h2]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlw) (Ideal.mul_mem_left _ _ hmem)
  have key : f = fun t => F (t ζ) := by
    have hχc : Continuous (fun t : G ℚ Ω => (((χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l)) := by
      refine cont_of_apply η _ (fun a b hab => ?_)
      have h0 : χ (b⁻¹ * a) = 1 := hK (b⁻¹ * a) (fun x hx => by
        obtain ⟨i, -, rfl⟩ := hη.eq_pow_of_pow_eq_one hx
        rw [map_pow]
        simp [AlgEquiv.mul_apply, hab])
      rw [map_mul, map_inv, inv_mul_eq_one] at h0
      rw [h0]
    have hdt : ∀ t, ((W t : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)).det =
        ((dt W t : (Qbar l)ˣ) : Qbar l) := fun t => rfl
    have hdc : Continuous (fun t : G ℚ Ω => ((dt W t : (Qbar l)ˣ) : Qbar l)) := by
      simp only [← hdt]
      exact (Units.continuous_val.comp hN.cont).matrix_det
    have hfc : Continuous f := by
      have h3 : f = fun t => ((dt W t : (Qbar l)ˣ) : Qbar l) *
          (((χ t)⁻¹ ^ 2 : (Qbar l)ˣ) : Qbar l) := by
        funext t
        simp only [f, Units.val_mul]
      rw [h3]
      exact hdc.mul hχc
    have hbad := Filter.eventually_cofinite.1 hAtt.2
    have hI : Ideal.span {((g.M * l : ℕ) : 𝓞 ℚ)} ≠ 0 := by
      rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (mul_ne_zero hM hl0)
    refine GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob GlobalTheory.Published.chebotarevDegreeOne'
      (hbad.union (Ideal.finite_factors hI)) hfc hf'c ?_
    intro w hw _ B hB σ hσ
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hw
    obtain ⟨hP, hdiv⟩ := hw
    have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
      intro h4
      apply hdiv
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ h4
    have hMw : ((g.M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
      intro h4
      apply hdiv
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ h4
    have hσζ : σ ζ = ζ ^ normV w := root_pow hM hB hMw hζ.pow_eq_one hσ.2
    show f σ = F (σ ζ)
    rw [hσζ, hF]
    have hch := (hP B hB).2 σ hσ
    rw [Newform.heckePoly] at hch
    have hdet := det_of_charpoly ι hch
    have hcyc : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : Qbar l) := by
      have h5 := cycZ_of_isFrob hlw hB hσ
      simp [cycBar, h5]
    rw [tw_val, Matrix.det_smul, Fintype.card_fin, hdt] at hdet
    simp [map_inv, hcyc] at hdet
    have hd0 : ι ((dt W σ : (Qbar l)ˣ) : Qbar l) ≠ 0 := (map_ne_zero ι).2 (Units.ne_zero _)
    have hx0 : ι ((χ σ : (Qbar l)ˣ) : Qbar l) ≠ 0 := (map_ne_zero ι).2 (Units.ne_zero _)
    have hn0 : (normV w : ℂ) ≠ 0 := by
      have h6 : (normV w : Qbar l) ≠ 0 := hcyc ▸ Units.ne_zero _
      exact_mod_cast (Nat.cast_ne_zero.1 h6)
    apply ι.injective
    rw [RingEquiv.apply_symm_apply]
    simp only [f]
    simp [map_inv]
    apply mul_right_cancel₀ (pow_ne_zero (2 * e) hn0)
    rw [← hdet]
    field_simp
    ring
  obtain ⟨v, hv, hlv⟩ := hN.atL
  have hs' : s ∈ Inertia A := hs
  have hsζ : s ζ = ζ ^ 1 :=
    root_pow hM hv (hcop v hlv) hζ.pow_eq_one (fun x hx => by simpa using hs'.2 x hx)
  have h1 := congrFun key s
  simp only [f, hsζ, hF, Nat.cast_one, map_one, Units.val_eq_one] at h1
  rw [inv_pow, mul_inv_eq_one] at h1
  exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.EulerSystemNorms
section
open UpperTheory.V.Z.Kato.Joint Topology Filter

private theorem mem_fixingSubgroup_of_fixes_finite_set (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E] :
    ∃ T : Finset Ω, ∀ g : Ω ≃ₐ[K] Ω, (∀ x ∈ T, g x = x) → g ∈ E.fixingSubgroup := by
  have h1 : (Subalgebra.toSubmodule E.toSubalgebra).FG :=
    Module.Finite.iff_fg.1 (inferInstanceAs (Module.Finite K E))
  obtain ⟨t, ht⟩ := h1
  refine ⟨t, fun g hg => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hle : Algebra.adjoin K (t : Set Ω) ≤ AlgHom.equalizer (g : Ω →ₐ[K] Ω) (AlgHom.id K Ω) :=
    Algebra.adjoin_le (fun y hy => by
      rw [SetLike.mem_coe, AlgHom.mem_equalizer]
      simpa using hg y hy)
  have hx1 : x ∈ Submodule.span K (t : Set Ω) := by
    rw [ht]
    exact hx
  have hx2 : x ∈ Algebra.adjoin K (t : Set Ω) := Algebra.span_le_adjoin K _ hx1
  have hx3 := hle hx2
  rw [AlgHom.mem_equalizer] at hx3
  simpa using hx3

private theorem uniform_continuity_galois_group (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] {X : Type} [NormedAddCommGroup X]
    (f : (Ω ≃ₐ[K] Ω) → X) (hf : Continuous f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[K] Ω, (∀ x ∈ E0, s' x = x) → ‖f (s * s') - f s‖ < δ := by
  classical
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have key : ∀ s : Ω ≃ₐ[K] Ω, ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ g ∈ E.fixingSubgroup, ‖f (s * g) - f s‖ < δ / 2 := by
    intro s
    have hc : Continuous fun g : Ω ≃ₐ[K] Ω => ‖f (s * g) - f s‖ :=
      ((hf.comp (continuous_const.mul continuous_id)).sub continuous_const).norm
    have hA : {g : Ω ≃ₐ[K] Ω | ‖f (s * g) - f s‖ < δ / 2} ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω) :=
      IsOpen.mem_nhds (isOpen_lt hc continuous_const) (by simp [hδ2])
    obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hA
    exact ⟨E, hE, fun g hg => hsub hg⟩
  choose E hEf hE using key
  let U : (Ω ≃ₐ[K] Ω) → Set (Ω ≃ₐ[K] Ω) := fun i => {h | i⁻¹ * h ∈ (E i).fixingSubgroup}
  have hUo : ∀ i, IsOpen (U i) := by
    intro i
    haveI := hEf i
    exact (IntermediateField.fixingSubgroup_isOpen (E i)).preimage (continuous_const.mul continuous_id)
  have hUc : Set.univ ⊆ ⋃ i, U i := by
    intro h _
    refine Set.mem_iUnion.2 ⟨h, ?_⟩
    show h⁻¹ * h ∈ (E h).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hUo hUc
  have hT : ∀ i, ∃ T : Finset Ω, ∀ g : Ω ≃ₐ[K] Ω, (∀ x ∈ T, g x = x) → g ∈ (E i).fixingSubgroup := by
    intro i
    haveI := hEf i
    exact mem_fixingSubgroup_of_fixes_finite_set K Ω (E i)
  choose T hT using hT
  refine ⟨S.biUnion T, fun s s' hs' => ?_⟩
  obtain ⟨i, hiS, hi⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ s))
  have hi' : i⁻¹ * s ∈ (E i).fixingSubgroup := hi
  have hs'i : s' ∈ (E i).fixingSubgroup :=
    hT i s' (fun x hx => hs' x (Finset.mem_biUnion.2 ⟨i, hiS, hx⟩))
  have h1 := hE i _ (mul_mem hi' hs'i)
  have h2 := hE i _ hi'
  rw [← mul_assoc, mul_inv_cancel_left] at h1
  rw [mul_inv_cancel_left] at h2
  have h3 : f (s * s') - f s = (f (s * s') - f i) - (f s - f i) := by abel
  rw [h3]
  have := norm_sub_le (f (s * s') - f i) (f s - f i)
  linarith

theorem UpperTheory.V.Z.Kato.Joint.unif :
    UpperTheory.V.Z.Kato.Joint.Unif := by
  intro l _ Ω _ _ _ f hf δ hδ
  haveI : IsGalois ℚ Ω := inferInstance
  exact uniform_continuity_galois_group ℚ Ω f hf δ hδ
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ExistsFiniteExtEisensteinUnitFunctionalMem
section
noncomputable section

open Formalism.ConjugateSelfDual UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.EisM

namespace UpperTheory.V.Z.Kato.Joint.M3

variable {l : ℕ} [Fact l.Prime]

omit [Fact l.Prime] in
theorem iter_uo (r : ℕ) (a : ℕ → ℂ) (n : ℕ) : (Uo l)^[r] a n = a (l ^ r * n) := by
  induction r generalizing a with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [Uo]
    rw [pow_succ', mul_assoc]

omit [Fact l.Prime] in
theorem mes_lin (k : ℕ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (m : ℕ) (a : ℂ) (f f' : ZMod (l ^ m) → ℂ) :
    mesMu k l u w α B c m (fun y => a * f y + f' y) = a * mesMu k l u w α B c m f + mesMu k l u w α B c m f' := by
  have h : ∀ n, Zm k l u w (fun A d => a * f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹) + f' ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n
      = a * Zm k l u w (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n +
        Zm k l u w (fun A d => f' ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n := by
    intro n
    simp only [Zm, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  simp only [mesMu, val, lam, iter_uo, h, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

omit [Fact l.Prime] in
theorem mes_smul (k : ℕ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (m : ℕ) (a : ℂ) (f : ZMod (l ^ m) → ℂ) :
    mesMu k l u w α B c m (fun y => a * f y) = a * mesMu k l u w α B c m f := by
  have key : ∀ n, Zm k l u w (fun A d => (fun y => a * f y) ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n =
      a * Zm k l u w (fun A d => f ((A : ZMod (l ^ m)) * (d : ZMod (l ^ m))⁻¹)) n := by
    intro n
    simp only [Zm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  simp only [mesMu, val, lam, iter_uo]
  simp only [key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

open Classical in

def sym (ι : Qbar l ≃+* ℂ) (s : ℂ) {N : ℕ} (g : ZMod N → Qbar l) : ZMod N → ℂ :=
  fun y => if IsUnit y then (ι (g y⁻¹) + s * ι (g (-y)⁻¹)) / 2 else 0

def nu0 (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (M : ℕ) :
    (ZMod (l ^ M) → Qbar l) →ₗ[Qbar l] Qbar l where
  toFun g := ι.symm (mesMu (2 * e + 1) l u w α B c M (sym ι s g))
  map_add' g g' := by
    have : sym ι s (g + g') = fun y => 1 * sym ι s g y + sym ι s g' y := by
      funext y; simp only [sym, Pi.add_apply, map_add]; split_ifs <;> ring
    rw [this, mes_lin, one_mul, map_add]
  map_smul' a g := by
    have : sym ι s (a • g) = fun y => ι a * sym ι s g y := by
      funext y; simp only [sym, Pi.smul_apply, smul_eq_mul, map_mul]; split_ifs <;> ring
    rw [this, mes_smul, map_mul]; simp

theorem eisensteinUnitFunctional_apply (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (M : ℕ)
    (g : ZMod (l ^ M) → Qbar l) : nu0 ι e s u w α B c M g = ι.symm (mesMu (2 * e + 1) l u w α B c M (sym ι s g)) := rfl

theorem inv_unit {N : ℕ} {y : ZMod N} (h : IsUnit y) : IsUnit y⁻¹ := IsUnit.of_mul_eq_one y (ZMod.inv_mul_of_unit y h)

theorem neg_inv_unit {N : ℕ} {y : ZMod N} (h : IsUnit y) : (-y)⁻¹ = -y⁻¹ := by
  obtain ⟨u, rfl⟩ := h
  rw [← Units.val_neg, ZMod.inv_coe_unit, ZMod.inv_coe_unit, inv_neg, Units.val_neg]

theorem sym_par (ι : Qbar l ≃+* ℂ) {s : ℂ} (hs : s * s = 1) {N : ℕ} (g : ZMod N → Qbar l) (y : ZMod N) :
    sym ι s g (-y) = s * sym ι s g y := by
  by_cases hy : IsUnit y
  · simp only [sym, if_pos hy, if_pos hy.neg, neg_neg]
    linear_combination (-ι (g (-y)⁻¹) / 2) * hs
  · simp [sym, hy]

theorem eisensteinUnitFunctional_congr_on_units (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (M : ℕ)
    (g g' : ZMod (l ^ M) → Qbar l) (h : ∀ x, IsUnit x → g x = g' x) : nu0 ι e s u w α B c M g = nu0 ι e s u w α B c M g' := by
  have hs : sym ι s g = sym ι s g' := by
    funext y
    unfold sym
    split_ifs with hy
    · rw [h _ (inv_unit hy), h _ (inv_unit hy.neg)]
    · rfl
  rw [eisensteinUnitFunctional_apply, eisensteinUnitFunctional_apply, hs]

theorem unit_iff {M : ℕ} (hM : 1 ≤ M) (y : ℕ) : IsUnit (y : ZMod (l ^ M)) ↔ ¬ l ∣ y := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff hM, Nat.coprime_comm, (Fact.out : l.Prime).coprime_iff_not_dvd]

theorem eisensteinUnitFunctional_compat_succ {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ} {v : ℂ}
    (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) (M : ℕ) (hM : 1 ≤ M) (g : ZMod (l ^ M) → Qbar l)
    (g' : ZMod (l ^ (M + 1)) → Qbar l) (h : ∀ y : ℕ, g' y = g y) :
    nu0 ι e s u w α B c (M + 1) g' = nu0 ι e s u w α B c M g := by
  have hdvd : l ^ M ∣ l ^ (M + 1) := pow_dvd_pow l (Nat.le_succ M)
  haveI : NeZero (l ^ (M + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set φ := ZMod.castHom hdvd (ZMod (l ^ M))
  have hg : ∀ x, g' x = g (φ x) := by
    intro x
    rw [← ZMod.natCast_zmod_val x, h, map_natCast]
  have hinv : ∀ x : ZMod (l ^ (M + 1)), IsUnit x → φ x⁻¹ = (φ x)⁻¹ := by
    intro x hx
    symm
    apply ZMod.inv_eq_of_mul_eq_one
    rw [← map_mul, ZMod.mul_inv_of_unit x hx, map_one]
  have hsym : ∀ y : ℕ, sym ι s g' (y : ZMod (l ^ (M + 1))) = sym ι s g y := by
    intro y
    unfold sym
    by_cases hy : l ∣ y
    · rw [if_neg (by rw [unit_iff (M := M + 1) (by omega)]; exact not_not.2 hy),
        if_neg (by rw [unit_iff hM]; exact not_not.2 hy)]
    · have h1 : IsUnit (y : ZMod (l ^ (M + 1))) := (unit_iff (M := M + 1) (by omega) y).2 hy
      rw [if_pos h1, if_pos ((unit_iff hM y).2 hy), hg, hg, hinv _ h1, hinv _ h1.neg, map_neg, map_natCast]
  rw [eisensteinUnitFunctional_apply, eisensteinUnitFunctional_apply, H.compat M hM (sym ι s g) (sym ι s g') (sym_par ι hs g) hsym]

theorem norm_nat {a : ℕ} (ha : ¬ l ∣ a) : ‖(a : Qbar l)‖ = 1 := by
  have h1 : algebraMap ℚ_[l] (Qbar l) (a : ℚ_[l]) = (a : Qbar l) := map_natCast _ a
  have h2 : ((a : ℚ) : ℚ_[l]) = (a : ℚ_[l]) := by push_cast; rfl
  rw [← h1, PadicAlgCl.norm_extends l (a : ℚ_[l])]
  rw [← h2, Padic.eq_padicNorm, (padicNorm.nat_eq_one_iff a).2 ha]
  simp

theorem norm_half (hl : l ≠ 2) {a b : Qbar l} {δ : ℝ} (ha : ‖a‖ ≤ δ) (hb : ‖b‖ ≤ δ) : ‖(a + b) / 2‖ ≤ δ := by
  have h2 : ‖(2 : Qbar l)‖ = 1 := by
    simpa using norm_nat (l := l) (a := 2) fun h => hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  rw [norm_div, h2, div_one]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

theorem sgn_cases {s : ℂ} (hs : s * s = 1) : s = 1 ∨ s = -1 := mul_self_eq_one_iff.1 hs

theorem symm_sym (ι : Qbar l ≃+* ℂ) (s : ℂ) {N : ℕ} (g : ZMod N → Qbar l) {y : ZMod N} (hy : IsUnit y) :
    ι.symm (sym ι s g y) = (g y⁻¹ + ι.symm s * g (-y⁻¹)) / 2 := by
  unfold sym
  rw [if_pos hy, neg_inv_unit hy, map_div₀, map_add, map_mul, RingEquiv.symm_apply_apply,
    RingEquiv.symm_apply_apply, map_ofNat]

theorem eisensteinUnitFunctional_bounded {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ} {v : ℂ}
    (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) (hl : l ≠ 2) :
    ∃ C : ℝ, ∀ (M : ℕ) (g : ZMod (l ^ M) → Qbar l), (∀ y, ‖g y‖ ≤ 1) → ‖nu0 ι e s u w α B c M g‖ ≤ C := by
  obtain ⟨C, hC⟩ := H.bound
  refine ⟨C * 1, fun M g hg => ?_⟩
  rw [eisensteinUnitFunctional_apply]
  apply hC M _ 1 zero_le_one
  intro y
  by_cases hy : IsUnit y
  · rw [symm_sym ι s g hy]
    apply norm_half hl (hg _)
    rw [norm_mul]
    have hn : ‖ι.symm s‖ = 1 := by
      rcases sgn_cases hs with rfl | rfl <;> simp
    rw [hn, one_mul]
    exact hg _
  · simp [sym, hy]

theorem exists_finiteExt_eisensteinUnitFunctional_mem {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ} {v : ℂ}
    (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) :
    ∃ E : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] E ∧
      ∀ (M : ℕ) (g : ZMod (l ^ M) → Qbar l), (∀ y, g y ∈ E) → nu0 ι e s u w α B c M g ∈ E := by
  obtain ⟨E, hE, hf⟩ := H.field
  refine ⟨E, hE, fun M g hg => ?_⟩
  rw [eisensteinUnitFunctional_apply]
  apply hf M _ E le_rfl
  intro y
  by_cases hy : IsUnit y
  · rw [symm_sym ι s g hy]
    have hs' : ι.symm s ∈ E := by
      rcases sgn_cases hs with rfl | rfl
      · rw [map_one]
        exact E.one_mem
      · rw [map_neg, map_one]
        exact E.neg_mem E.one_mem
    have h2 : (2 : Qbar l) ∈ E := by
      rw [← one_add_one_eq_two]
      exact E.add_mem E.one_mem E.one_mem
    exact E.div_mem (E.add_mem (hg _) (E.mul_mem hs' (hg _))) h2
  · simp only [sym, if_neg hy, map_zero]
    exact E.zero_mem

theorem sym_char (ι : Qbar l ≃+* ℂ) (s : ℂ) {N : ℕ} (χ : DirichletCharacter (Qbar l) N) (y : ZMod N) :
    sym ι s (fun x => χ⁻¹ x) y = (1 + s * ι (χ (-1))) / 2 * ι (χ y) := by
  unfold sym
  split_ifs with hy
  · have key : ∀ z : ZMod N, IsUnit z → χ⁻¹ z⁻¹ = χ z := by
      intro z hz
      rw [MulChar.inv_apply_eq_inv']
      have hm : χ z⁻¹ * χ z = 1 := by rw [← map_mul, ZMod.inv_mul_of_unit z hz, map_one]
      exact inv_eq_of_mul_eq_one_right hm
    dsimp only
    rw [key y hy, key (-y) hy.neg]
    have hn : χ (-y) = χ (-1) * χ y := by rw [← map_mul, neg_one_mul]
    rw [hn, map_mul ι]
    ring
  · rw [MulChar.map_nonunit χ hy, map_zero, mul_zero]

theorem eisensteinUnitFunctional_dirichletChar (ι : Qbar l ≃+* ℂ) (e : ℕ) (s : ℂ) (u w : ℤ → ℂ) (α : ℂ) (B : ℕ) (c : ℕ → ℂ) (M : ℕ)
    (χ : DirichletCharacter (Qbar l) (l ^ M)) :
    nu0 ι e s u w α B c M (fun x => χ⁻¹ x) =
      (1 + ι.symm s * χ (-1)) / 2 * ι.symm (mesMu (2 * e + 1) l u w α B c M (fun y => ι (χ y))) := by
  rw [eisensteinUnitFunctional_apply]
  have hs : sym ι s (fun x => χ⁻¹ x) = fun y => (1 + s * ι (χ (-1))) / 2 * ι (χ y) := funext (sym_char ι s χ)
  rw [hs, mes_smul, map_mul]
  congr 1
  rw [map_div₀, map_add, map_one, map_mul, RingEquiv.symm_apply_apply, map_ofNat]

theorem eisensteinUnitFunctional_interpolation {ι : Qbar l ≃+* ℂ} {e : ℕ} {s : ℂ} {u w : ℤ → ℂ} {ψ : DirichletCharacter ℂ l} {α : ℂ} {B : ℕ} {c : ℕ → ℂ} {v : ℂ}
    (H : MeasMu ι e s u w ψ α B c v) (hs : s * s = 1) (hl : l ≠ 2) :
    ∃ C : ℝ, ∀ (M : ℕ), 1 ≤ M → ∀ (g : ZMod (l ^ M) → Qbar l) (δ : ℝ), 0 ≤ δ →
      (∀ a d : ℕ, ¬ l ∣ a → ¬ l ∣ d → ∀ y : ZMod (l ^ M), y * a = d →
        ‖g y - ι.symm (ψ a * ψ⁻¹ d * ((d : ℂ) / a) ^ e)‖ ≤ δ ∧ ‖ι.symm s * g (-y) - ι.symm (ψ a * ψ⁻¹ d * ((d : ℂ) / a) ^ e)‖ ≤ δ) →
      ‖nu0 ι e s u w α B c M g - ι.symm v‖ ≤ C * δ := by
  obtain ⟨C, hC⟩ := H.interp
  refine ⟨C, fun M hM g δ hδ hg => ?_⟩
  rw [eisensteinUnitFunctional_apply, ← map_sub]
  apply hC M hM _ δ hδ (sym_par ι hs g)
  intro a d ha hd
  have hua : IsUnit (a : ZMod (l ^ M)) := (unit_iff hM a).2 ha
  have hud : IsUnit (d : ZMod (l ^ M)) := (unit_iff hM d).2 hd
  set x : ZMod (l ^ M) := (a : ZMod (l ^ M)) * (d : ZMod (l ^ M))⁻¹ with hxdef
  have hx : IsUnit x := hua.mul (inv_unit hud)
  have hxd : x * d = a := by rw [hxdef, mul_assoc, ZMod.inv_mul_of_unit _ hud, mul_one]
  have hy : x⁻¹ * a = d := by rw [← hxd, ← mul_assoc, ZMod.inv_mul_of_unit _ hx, one_mul]
  obtain ⟨h1, h2⟩ := hg a d ha hd x⁻¹ hy
  rw [map_sub, symm_sym ι s g hx]
  set T := ι.symm (ψ a * ψ⁻¹ d * ((d : ℂ) / a) ^ e)
  have hT : (g x⁻¹ + ι.symm s * g (-x⁻¹)) / 2 - T = ((g x⁻¹ - T) + (ι.symm s * g (-x⁻¹) - T)) / 2 := by ring
  rw [hT]
  exact norm_half hl h1 h2

end UpperTheory.V.Z.Kato.Joint.M3

end
end

