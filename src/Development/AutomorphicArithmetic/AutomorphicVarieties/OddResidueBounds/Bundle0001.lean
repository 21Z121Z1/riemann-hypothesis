import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.AlgebraMapSignedInvolutionQuotientDetMemSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.compsup
import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Detint
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem conj_cycLift {Ω : Type} [Field Ω] (N : ℕ) [NeZero N] {σ : Ω ≃+* Ω} (h : IsConjOm σ) :
    CycLift N (-1) σ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos N)).symm⟩
  obtain ⟨j, hj⟩ := h
  intro x hx
  apply j.injective
  rw [hj, map_pow, Units.val_neg, Units.val_one, ZMod.val_neg_one]
  have hz : (j x) ^ (n + 1) = 1 := by rw [← map_pow, hx, map_one]
  have hnorm : ‖j x‖ = 1 := by
    have : ‖j x‖ ^ (n + 1) = 1 := by rw [← norm_pow, hz, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.succ_ne_zero n)).1 this
  have hne : j x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have h1 : j x * (starRingEnd ℂ) (j x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  have h2 : j x * (j x) ^ n = 1 := by rw [← pow_succ', hz]
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem UpperTheory.V.Odd.actConj :
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), IsCycAct Ω N ρ → (ρ (-1)).toRingEquiv = cE E ∧ piQ ρ (-1) ≠ 1 := by
  intro E Ω _ _ _ _ _ _ N _ ρ hρ
  obtain ⟨σ, hσ⟩ := exists_isConjOm (E := E) (Ω := Ω)
  have hL1 : IsLift (cE E) σ := hσ.isLift
  have hL2 : IsLift (ρ (-1)).toRingEquiv σ := hρ (-1) σ (conj_cycLift N hσ)
  have heq : (ρ (-1)).toRingEquiv = cE E := by
    ext x
    apply (algebraMap E Ω).injective
    rw [← hL2 x, hL1 x]
  refine ⟨heq, ?_⟩
  intro hone
  have hker : ρ (-1) = 1 := by
    have := (QuotientGroup.eq_one_iff (N := ρ.ker) (-1 : (ZMod N)ˣ)).1 hone
    exact this
  apply IsCMField.complexConj_ne_one (K := E)
  ext x
  have := congrArg (fun f : E ≃+* E => f x) heq
  simp only [hker] at this
  exact this.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ActEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.actEx :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (N : ℕ) [NeZero N], Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∃ ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E), IsCycAct Ω N ρ := by
  intro E Ω _ _ _ _ _ N _ hf
  obtain ⟨f⟩ := hf
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast NeZero.ne N⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  letI : Algebra E (CyclotomicField N ℚ) := f.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ E (CyclotomicField N ℚ) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  haveI : IsAbelianGalois ℚ (CyclotomicField N ℚ) :=
    IsCyclotomicExtension.isAbelianGalois {N} ℚ (CyclotomicField N ℚ)
  haveI : IsAbelianGalois ℚ E := IsAbelianGalois.tower_bot ℚ E (CyclotomicField N ℚ)
  haveI : Algebra.IsAlgebraic E (CyclotomicField N ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  let g : CyclotomicField N ℚ →ₐ[E] Ω := IsAlgClosed.lift
  refine ⟨(AlgEquiv.restrictNormalHom E).comp
    (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm.toMonoidHom, ?_⟩
  intro b σ hσ x
  set τ := (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).symm b with hτ
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)
  have key : ∀ y : CyclotomicField N ℚ, σ (g y) = g (τ y) := by
    have hcomp : (σ.toRingHom.comp (g : CyclotomicField N ℚ →+* Ω)).toRatAlgHom =
        ((g : CyclotomicField N ℚ →+* Ω).comp (τ : CyclotomicField N ℚ →+* CyclotomicField N ℚ)).toRatAlgHom := by
      apply (hζ.powerBasis ℚ).algHom_ext
      simp only [IsPrimitiveRoot.powerBasis_gen, RingHom.toRatAlgHom_apply, RingHom.coe_comp,
        Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, AlgHom.coe_toRingHom]
      have h1 : (g (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ))) ^ N = 1 := by
        rw [← map_pow, hζ.pow_eq_one, map_one]
      change σ (g (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ))) =
        g (τ (IsCyclotomicExtension.zeta N ℚ (CyclotomicField N ℚ)))
      rw [hσ _ h1, IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one, map_pow, hτ,
        MulEquiv.apply_symm_apply]
    intro y
    exact congrArg (fun φ => φ y) hcomp
  change σ (algebraMap E Ω x) = algebraMap E Ω ((AlgEquiv.restrictNormal τ E) x)
  rw [← g.commutes x, ← g.commutes, AlgEquiv.restrictNormal_commutes, key]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.AdjKill
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.adjKill :
    ∀ (A Γ X : Type) [CommRing A] [CommGroup Γ] [Finite Γ] [AddCommGroup X] [Module A X] (π : Representation A Γ X) (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ (z : MonoidAlgebra A Γ) (x : X), π c x = (ε : A) • x → π.asAlgebraHom z x = 0 → detR c ε z • x = 0 := by
  intro A Γ X _ _ _ _ _ π c ε hc hc1 hε z x hx hz
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (algebraMap_signedInvolutionQuotientDet_mem_span (A := A) c ε hc hc1 hε z)
  have hrel : π.asAlgebraHom (rel A c ε) x = 0 := by
    simp [rel, hx, Int.cast_smul_eq_zsmul]
  have key := congrArg (fun w => π.asAlgebraHom w x) hab
  simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, hrel, hz, map_zero,
    add_zero] at key
  rw [AlgHom.commutes, Module.algebraMap_end_apply] at key
  exact key.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.BdxLog
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem bdX_mul_le (M a k T : ℕ) (hT : 2 ≤ T) (hM : M ≤ T) (ha : a ≤ T ^ 3) (hk : k ≤ T) (hk2 : 2 ≤ k) :
    bdX M a k * M ≤ T ^ (10 * k) := by
  have hk1 : k + 1 ≤ T ^ 2 := by nlinarith
  have f1 : (k + 1).factorial ≤ (T ^ 2) ^ (k + 1) :=
    (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left hk1 _)
  have f2 : k.factorial ≤ T ^ k := (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left hk _)
  calc bdX M a k * M = M * k * (k + 1).factorial * (2 * a ^ k * M ^ k * k.factorial) * M := rfl
    _ ≤ T * T * (T ^ 2) ^ (k + 1) * (T * (T ^ 3) ^ k * T ^ k * T ^ k) * T := by gcongr
    _ = T ^ (7 * k + 6) := by ring
    _ ≤ T ^ (10 * k) := Nat.pow_le_pow_right (by omega) (by omega)

theorem UpperTheory.V.Odd.bdxLog :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N l e : ℕ, 1 ≤ N → 2 ≤ l → 1 ≤ e → Real.log (bdX (N * l) (2 * (N * l) + 1) (e + 1)) + Real.log ((N : ℝ) * l) ≤ C * (e + 1) * Real.log ((e : ℝ) * l * N) := by
  refine ⟨30, by norm_num, ?_⟩
  intro N l e hN hl he
  have h2 : e * 2 ≤ e * l := Nat.mul_le_mul_left e hl
  have h3 : e * l ≤ e * l * N := Nat.le_mul_of_pos_right _ hN
  have h4 : 1 * l * N ≤ e * l * N := by gcongr
  have h5 : N * l ≤ e * l * N := by nlinarith
  have hX2 : 2 ≤ e * l * N := by nlinarith
  have hT : 2 ≤ 3 * (e * l * N) := by omega
  have hM : N * l ≤ 3 * (e * l * N) := by omega
  have ha : 2 * (N * l) + 1 ≤ (3 * (e * l * N)) ^ 3 :=
    le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
  have hk : e + 1 ≤ 3 * (e * l * N) := by nlinarith
  have key := bdX_mul_le (N * l) (2 * (N * l) + 1) (e + 1) (3 * (e * l * N)) hT hM ha hk (by omega)
  have hNl : 0 < N * l := by positivity
  have hb : 0 < bdX (N * l) (2 * (N * l) + 1) (e + 1) := by
    unfold bdX denY sizeY
    positivity
  have hbpos : (0 : ℝ) < (bdX (N * l) (2 * (N * l) + 1) (e + 1) : ℝ) := by exact_mod_cast hb
  have hMpos : (0 : ℝ) < (N : ℝ) * l := by exact_mod_cast hNl
  rw [← Real.log_mul hbpos.ne' hMpos.ne']
  have hcast : (bdX (N * l) (2 * (N * l) + 1) (e + 1) : ℝ) * ((N : ℝ) * l)
      = ((bdX (N * l) (2 * (N * l) + 1) (e + 1) * (N * l) : ℕ) : ℝ) := by
    push_cast; ring
  rw [hcast]
  have hXr : (2 : ℝ) ≤ (e : ℝ) * l * N := by exact_mod_cast hX2
  have hlog2 : Real.log 2 ≤ Real.log ((e : ℝ) * l * N) := Real.log_le_log (by norm_num) hXr
  have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT : Real.log (((3 * (e * l * N) : ℕ) : ℝ)) ≤ 3 * Real.log ((e : ℝ) * l * N) := by
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hpos : (0 : ℝ) < ((bdX (N * l) (2 * (N * l) + 1) (e + 1) * (N * l) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hb hNl
  calc Real.log ((bdX (N * l) (2 * (N * l) + 1) (e + 1) * (N * l) : ℕ) : ℝ)
      ≤ Real.log (((3 * (e * l * N)) ^ (10 * (e + 1)) : ℕ) : ℝ) :=
        Real.log_le_log hpos (by exact_mod_cast key)
    _ = (10 * (e + 1) : ℕ) * Real.log (((3 * (e * l * N) : ℕ) : ℝ)) := by
        rw [Nat.cast_pow, Real.log_pow]
    _ ≤ (10 * (e + 1) : ℕ) * (3 * Real.log ((e : ℝ) * l * N)) :=
        mul_le_mul_of_nonneg_left hlogT (by positivity)
    _ = 30 * ((e : ℝ) + 1) * Real.log ((e : ℝ) * l * N) := by push_cast; ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ChiFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

theorem UpperTheory.V.Odd.chiFacts :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N] (ρ : (ZMod N)ˣ →* (E ≃ₐ[ℚ] E)), Function.Surjective ρ → ∀ (l : ℕ) [Fact l.Prime] (O : Subalgebra ℤ_[l] (PadicAlgCl l)), Function.Injective (fun ψ : (E ≃ₐ[ℚ] E) →* Oˣ => chiOf ρ ψ) ∧ ∀ (ψ : (E ≃ₐ[ℚ] E) →* Oˣ) (k : ℕ), (chiOf ρ ψ (-1) = (-1) ^ k → chiOf ρ ψ ∈ charSet (PadicAlgCl l) (parE ρ k)) ∧ ∃ a : O, (a : PadicAlgCl l) = alN k (chiOf ρ ψ) := by
  intro E _ _ N _ ρ hρ l _ O
  refine ⟨fun ψ ψ' h => ?_, fun ψ k => ⟨fun hk => ?_, ?_⟩⟩
  · refine MonoidHom.ext fun g => ?_
    obtain ⟨b, rfl⟩ := hρ g
    have hb := congrArg (fun χ : DirichletCharacter (PadicAlgCl l) N => χ (b : ZMod N)) h
    simp only [chiOf_unit] at hb
    exact Units.ext (Subtype.ext hb)
  · simp only [charSet, parE, Set.mem_setOf_eq, Set.mem_inter_iff]
    refine ⟨?_, (b_parity k _).1.2 hk⟩
    intro b hb
    rw [MonoidHom.mem_ker] at hb ⊢
    apply Units.ext
    rw [MulChar.coe_toUnitHom, chiOf_unit, hb]
    simp
  · have h := (b_primmem k (chiOf ρ ψ)).2.1 O.toSubring (fun u => by
      rw [chiOf_unit]
      exact (ψ (ρ u) : O).2)
    exact ⟨⟨_, h⟩, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ContinuousToTorsionBounded
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem continuous_to_torsion_bounded {G : Type} [TopologicalSpace G] [CompactSpace G] (l : ℕ) [Fact l.Prime]
    (f : G → QZ l) (hf : Continuous f) : ∃ r : ℕ, ∀ g, (l : ℤ_[l]) ^ r • f g = 0 := by
  have hfin : (Set.range f).Finite := (isCompact_range hf).finite_of_discrete
  choose k hk using (UpperTheory.V.Kum.qzBasic l).2.1
  obtain ⟨r, hr⟩ := (hfin.image k).bddAbove
  refine ⟨r, fun g => ?_⟩
  have h1 : k (f g) ≤ r := hr ⟨f g, ⟨g, rfl⟩, rfl⟩
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le' h1
  have h2 : (l : ℤ_[l]) ^ k (f g) • f g = 0 := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact hk _
  rw [pow_add, mul_smul, h2, smul_zero]

theorem UpperTheory.V.Odd.Z1_H1_qz_twist_l_power_torsion :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ), (∀ z : Z1 (qzTw D e), ∃ r : ℕ, ∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0) ∧ ∀ x : H1 (qzTw D e), ∃ r : ℕ, (l : ℤ_[l]) ^ r • x = 0 := by
  intro E Ω _ _ _ _ _ l _ D e
  have h : ∀ z : Z1 (qzTw D e), ∃ r : ℕ, ∀ g, (l : ℤ_[l]) ^ r • z.1 g = 0 := fun z =>
    continuous_to_torsion_bounded l z.1 z.2.1
  refine ⟨h, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨r, hr⟩ := h z
  refine ⟨r, ?_⟩
  have hz : (l : ℤ_[l]) ^ r • z = 0 := Subtype.ext (funext hr)
  rw [← Submodule.Quotient.mk_smul, hz, Submodule.Quotient.mk_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.DegExistsLift
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem deg_jac {a p n : ℕ} (h : a.Coprime p) : jacobiSym ((a ^ (2 * n) : ℕ) : ℤ) p = 1 := by
  have hc : Int.gcd ((a ^ n : ℕ) : ℤ) (p : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact Nat.Coprime.pow_left n h
  have he : ((a ^ (2 * n) : ℕ) : ℤ) = ((a ^ n : ℕ) : ℤ) ^ 2 := by
    push_cast
    ring
  rw [he]
  exact jacobiSym.sq_one' hc

private theorem deg_ker (A : AbF) {a : ℕ} (n : ℕ) (h : a.Coprime A.m) : A.ker (a ^ (A.deg * n)) := by
  haveI : NeZero A.m := ⟨A.pos.ne'⟩
  let u : (ZMod A.m)ˣ := ZMod.unitOfCoprime a h
  refine ⟨u ^ (A.deg * n), ?_, ?_⟩
  · rw [pow_mul]
    exact Subgroup.pow_mem _ (Subgroup.pow_index_mem A.H u) n
  · push_cast
    simp [u, ZMod.coe_unitOfCoprime]

private theorem deg_two {a e : ℕ} (n : ℕ) (h : a.Coprime (2 ^ (e + 2))) :
    a ^ (2 ^ (e + 1) * n) ≡ 1 [MOD 2 ^ (e + 2)] := by
  have ht := Nat.ModEq.pow_totient h
  rw [Nat.totient_prime_pow Nat.prime_two (by omega)] at ht
  simp only [Nat.add_sub_cancel, show (2 : ℕ) - 1 = 1 from rfl, mul_one] at ht
  rw [pow_mul]
  simpa using ht.pow n

theorem UpperTheory.V.Odd.deg :
    ∀ (M : AbF) (e q d : ℕ), PrimePair M.m q d → ∀ (E : Type) [Field E] [NumberField E], IsCompField M e q d E → ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ Module.finrank ℚ E → l ∣ M.deg := by
  intro M e q d _ E _ _ hE l hl hl2 hldvd
  obtain ⟨N, hN, j, ζ, h1, h2, h3, h4, hζ, hfix⟩ := hE
  haveI : NeZero (N : ℚ) := ⟨by exact_mod_cast hN.ne⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  haveI : IsGalois ℚ (CyclotomicField N ℚ) := IsCyclotomicExtension.isGalois {N} ℚ _
  have hpowζ : ∀ (τ : Gal(CyclotomicField N ℚ/ℚ)) (a n : ℕ), τ ζ = ζ ^ a → (τ ^ n) ζ = ζ ^ (a ^ n) := by
    intro τ a n hτ
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ τ n, AlgEquiv.mul_apply, hτ, map_pow, ih, ← pow_mul, pow_succ a n]
  have hmem : ∀ (τ : Gal(CyclotomicField N ℚ/ℚ)) (x : E),
      (τ ^ (2 ^ (e + 1) * M.deg)) (j x) = j x := by
    intro τ
    have hτ : τ ζ = ζ ^ ((hζ.autToPow ℚ τ : (ZMod N)ˣ) : ZMod N).val := (hζ.autToPow_spec ℚ τ).symm
    have hcop : (((hζ.autToPow ℚ τ : (ZMod N)ˣ) : ZMod N).val).Coprime N := ZMod.val_coe_unit_coprime _
    refine (hfix _ _ (hpowζ τ _ (2 ^ (e + 1) * M.deg) hτ)).mpr ⟨Or.inl ?_, ?_, ?_, ?_⟩
    · exact deg_two M.deg (hcop.coprime_dvd_right h1)
    · have hk := deg_ker M (2 ^ (e + 1)) (hcop.coprime_dvd_right h2)
      rwa [mul_comm M.deg] at hk
    · have hk := deg_jac (n := 2 ^ e * M.deg) (hcop.coprime_dvd_right h3)
      rwa [show 2 * (2 ^ e * M.deg) = 2 ^ (e + 1) * M.deg by ring] at hk
    · have hk := deg_jac (n := 2 ^ e * M.deg) (hcop.coprime_dvd_right h4)
      rwa [show 2 * (2 ^ e * M.deg) = 2 ^ (e + 1) * M.deg by ring] at hk
  obtain ⟨F, hF⟩ : ∃ F : IntermediateField ℚ (CyclotomicField N ℚ), F = j.fieldRange := ⟨_, rfl⟩
  have hcomm : ∀ σ τ : Gal(CyclotomicField N ℚ/ℚ), σ * τ = τ * σ := by
    intro σ τ
    apply IsPrimitiveRoot.autToPow_injective ℚ hζ
    rw [map_mul, map_mul, mul_comm]
  haveI hKn : F.fixingSubgroup.Normal :=
    ⟨fun n hn g => by rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
  have hKmem : ∀ τ : Gal(CyclotomicField N ℚ/ℚ), τ ^ (2 ^ (e + 1) * M.deg) ∈ F.fixingSubgroup := by
    intro τ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hF] at hx
    obtain ⟨y, rfl⟩ := AlgHom.mem_fieldRange.mp hx
    exact hmem τ y
  have hindex : F.fixingSubgroup.index = Module.finrank ℚ E := by
    have e1 : Module.finrank ℚ E = Module.finrank ℚ F := by
      rw [hF]
      exact (AlgEquiv.ofInjectiveField j).toLinearEquiv.finrank_eq
    have e2 := Module.finrank_mul_finrank ℚ F (CyclotomicField N ℚ)
    have e3 := IsGalois.card_fixingSubgroup_eq_finrank F
    have e4 := IsGalois.card_aut_eq_finrank ℚ (CyclotomicField N ℚ)
    have e5 := F.fixingSubgroup.card_mul_index
    have hpos : 0 < Module.finrank F (CyclotomicField N ℚ) := Module.finrank_pos
    rw [e1]
    rw [e3, e4, ← e2, mul_comm (Module.finrank ℚ F)] at e5
    exact Nat.eq_of_mul_eq_mul_left hpos e5
  haveI : Fact l.Prime := ⟨hl⟩
  have hcard : l ∣ Nat.card (Gal(CyclotomicField N ℚ/ℚ) ⧸ F.fixingSubgroup) := by
    show l ∣ F.fixingSubgroup.index
    rw [hindex]
    exact hldvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l hcard
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hxk : ((g : Gal(CyclotomicField N ℚ/ℚ) ⧸ F.fixingSubgroup)) ^ (2 ^ (e + 1) * M.deg) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hKmem g
  have hdk := orderOf_dvd_of_pow_eq_one hxk
  rw [hx] at hdk
  have hcop : l.Coprime (2 ^ (e + 1)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hl Nat.prime_two).mpr hl2)
  exact hcop.dvd_of_dvd_mul_left hdk
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.DetVal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem int_dvd_pow (l : ℕ) [hl : Fact l.Prime] (X : ℤ) (hX : X ≠ 0) :
    ∃ r : ℕ, l ^ r ≤ X.natAbs ∧ (X : ℤ_[l]) ∣ (l : ℤ_[l]) ^ r := by
  obtain ⟨e, n', hn', he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.mpr hX) l hl.out.one_lt.ne'
  have hn0 : n' ≠ 0 := by
    rintro rfl
    exact hn' (dvd_zero l)
  refine ⟨e, ?_, ?_⟩
  · rw [he]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn0)
  · have hu : IsUnit ((n' : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hn' ?_)
      exact_mod_cast (PadicInt.norm_int_lt_one_iff_dvd _).mp h
    rw [Int.cast_natCast] at hu
    have h1 : (X : ℤ_[l]) ∣ ((X.natAbs : ℤ) : ℤ_[l]) :=
      map_dvd (Int.castRingHom ℤ_[l]) (Int.dvd_natAbs.mpr dvd_rfl)
    refine h1.trans ?_
    rw [he]
    push_cast
    exact hu.mul_right_dvd.mpr dvd_rfl

theorem UpperTheory.V.Odd.detVal :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [CommGroup Γ] [Finite Γ] (N : ℕ) [NeZero N] (φ : (ZMod N)ˣ →* Γ) (e a : ℕ) (ha : a.Coprime N), Function.Surjective φ → φ (-1) ≠ 1 → 1 ≤ e → 1 < a → ∀ z : MonoidAlgebra ℤ_[l] Γ, IsInt l z (yEl (e + 1) a ha φ) → ∃ r : ℕ, (r : ℝ) * Real.log l ≤ Nat.card Γ * Real.log (bdX N a (e + 1)) ∧ detR (φ (-1)) ((-1) ^ (e + 1)) z ∣ (l : ℤ_[l]) ^ r := by
  intro l _ Γ _ _ N _ φ e a ha hs hφ he ha1 z hz
  obtain ⟨X, hX0, hXb, hXe⟩ := higherStickelberger_det_exists_int_bounded φ a ha (e + 1) ha1 (by omega) hφ
  obtain ⟨r, hr1, hr2⟩ := int_dvd_pow l X hX0
  refine ⟨r, ?_, ?_⟩
  · have h1 : ((l : ℝ) ^ r) ≤ (bdX N a (e + 1) : ℝ) ^ (Nat.card Γ / 2) := by
      exact_mod_cast hr1.trans hXb
    have hl0 : (0 : ℝ) < (l : ℝ) ^ r := by
      have := (Fact.out : l.Prime).pos
      positivity
    have h2 := Real.log_le_log hl0 h1
    rw [Real.log_pow, Real.log_pow] at h2
    have h3 : ((Nat.card Γ / 2 : ℕ) : ℝ) ≤ (Nat.card Γ : ℝ) := by
      exact_mod_cast Nat.div_le_self _ _
    calc (r : ℝ) * Real.log l ≤ ((Nat.card Γ / 2 : ℕ) : ℝ) * Real.log (bdX N a (e + 1)) := h2
      _ ≤ Nat.card Γ * Real.log (bdX N a (e + 1)) :=
        mul_le_mul_of_nonneg_right h3 (Real.log_natCast_nonneg _)
  · refine dvd_trans ?_ hr2
    have hmap : MonoidAlgebra.mapRingHom Γ PadicInt.Coe.ringHom z =
        MonoidAlgebra.mapRingHom Γ (Rat.castHom ℚ_[l]) (yEl (e + 1) a ha φ) := by
      ext g
      have h := hz g
      simp
      exact h
    have hd := congrArg (detR (φ (-1)) ((-1) ^ (e + 1))) hmap
    rw [detR_map, detR_map] at hd
    have hq := congrArg (Rat.castHom ℚ_[l]) hXe
    rw [map_mul, map_pow, ← hd] at hq
    have hX'' : (X : ℤ_[l]) =
        (denY N (e + 1) : ℤ_[l]) ^ (Nat.card Γ / 2) * detR (φ (-1)) ((-1) ^ (e + 1)) z := by
      apply PadicInt.ext
      push_cast
      simp at hq
      exact hq
    rw [hX'']
    exact dvd_mul_left _ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.FixLev
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

private theorem pow_cyc_char_iff_toZModPow_eq {Ω : Type} [Field Ω] (l : ℕ) [Fact l.Prime] [∀ i, HasEnoughRootsOfUnity Ω (l ^ i)]
    (g : Ω ≃+* Ω) (k : ℕ) (c : ZMod (l ^ k)) :
    (∀ t : Ω, t ^ (l ^ k) = 1 → g t = t ^ c.val) ↔
      PadicInt.toZModPow k ((cyclotomicCharacter Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = c := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  constructor
  · intro h
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ k)
    have h1 := cyclotomicCharacter.spec l g ζ hζ.pow_eq_one
    rw [h ζ hζ.pow_eq_one] at h1
    have h2 := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h1
    exact (ZMod.val_injective _ h2).symm
  · rintro h t ht
    rw [cyclotomicCharacter.spec l g t ht, h]

private theorem pow_mod_eq_pow_of_pow_eq_one {Ω : Type} [Field Ω] (t : Ω) (n a : ℕ) (ht : t ^ n = 1) :
    t ^ (a % n) = t ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a n, pow_add, pow_mul, ht, one_pow, mul_one]

theorem UpperTheory.V.Odd.fixLev :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (N m : ℕ) [NeZero N], fixMu E Ω (l ^ m) = Un E Ω l m ∧ Uinf E Ω l ⊓ fixMu E Ω N ≤ fixMu E Ω (N * l ^ m) ∧ ∀ (M : ℕ) [NeZero M] (b : (ZMod M)ˣ) (σ : Ω ≃+* Ω), l ^ m ∣ M → CycLift M b σ → (l : ℤ_[l]) ^ m ∣ ((cyclotomicCharacter Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) - (((b : ZMod M).val : ℕ) : ℤ_[l]) := by
  intro E Ω _ _ _ _ _ l _ N m _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero⟩
  have key : ∀ (g : G E Ω) (k : ℕ),
      PadicInt.toZModPow k ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G E Ω) Ω g) : ℤ_[l]ˣ) : ℤ_[l]) = 1 ↔
        ∀ t : Ω, t ^ (l ^ k) = 1 → g t = t := by
    intro g k
    rw [← pow_cyc_char_iff_toZModPow_eq l _ k 1]
    refine forall_congr' fun t => imp_congr_right fun ht => ?_
    rw [ZMod.val_one_eq_one_mod, pow_mod_eq_pow_of_pow_eq_one t _ 1 ht, pow_one]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · ext g
    simp only [Un, levU, Subgroup.mem_inf, Subgroup.mem_top, true_and, Subgroup.mem_comap, KStar.TotallyRealRoots.princ,
      cycZ, MonoidHom.mem_ker, KStar.TotallyRealRoots.redPow, MonoidHom.comp_apply, Units.ext_iff, Units.coe_map,
      MonoidHom.coe_coe, Units.val_one]
    change _ ↔ PadicInt.toZModPow m _ = 1
    rw [key]
    rfl
  · intro g hg
    rcases Subgroup.mem_inf.1 hg with ⟨h1, h2⟩
    have hχ : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G E Ω) Ω g) = 1 := by
      simpa only [Uinf, cycU, Subgroup.mem_inf, Subgroup.mem_top, true_and, MonoidHom.mem_ker, cycZ,
        MonoidHom.comp_apply] using h1
    have hl : ∀ k, ∀ t : Ω, t ^ (l ^ k) = 1 → g t = t := fun k => (key g k).1 (by rw [hχ, Units.val_one, map_one])
    have hN : ∀ t : Ω, t ^ N = 1 → g t = t := h2
    obtain ⟨e, N', hndvd, hNe⟩ :=
      Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne N) l (Fact.out : l.Prime).one_lt.ne'
    have hcop : Nat.Coprime (l ^ (e + m)) N' :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hndvd)
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero))] at hx
      exact zero_ne_one hx
    have hxA : x ^ (l ^ (e + m) * N') = 1 := by
      rw [← hx, hNe, pow_add]
      congr 1
      ring
    have h3 : g (x ^ N') = x ^ N' := hl (e + m) _ (by rw [← pow_mul, mul_comm, hxA])
    have h4 : g (x ^ (l ^ (e + m))) = x ^ (l ^ (e + m)) := by
      apply hN
      rw [hNe, ← pow_mul, show l ^ (e + m) * (l ^ e * N') = (l ^ (e + m) * N') * l ^ e by ring, pow_mul, hxA,
        one_pow]
    have hyA : (g x * x⁻¹) ^ (l ^ (e + m)) = 1 := by
      rw [mul_pow, inv_pow, ← map_pow, h4, mul_inv_cancel₀ (pow_ne_zero _ hx0)]
    have hyB : (g x * x⁻¹) ^ N' = 1 := by
      rw [mul_pow, inv_pow, ← map_pow, h3, mul_inv_cancel₀ (pow_ne_zero _ hx0)]
    have hy : (g x * x⁻¹) ^ (Nat.gcd (l ^ (e + m)) N') = 1 := pow_gcd_eq_one.2 ⟨hyA, hyB⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hy
    exact (mul_inv_eq_one₀ hx0).1 hy
  · intro M _ b σ hdvd hσ
    have hc := (pow_cyc_char_iff_toZModPow_eq l σ m (((b : ZMod M).val : ℕ) : ZMod (l ^ m))).1 (by
      intro t ht
      rw [ZMod.val_natCast, pow_mod_eq_pow_of_pow_eq_one t _ _ ht]
      apply hσ
      obtain ⟨q, rfl⟩ := hdvd
      rw [pow_mul, ht, one_pow])
    have hmem : ((cyclotomicCharacter Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) - (((b : ZMod M).val : ℕ) : ℤ_[l]) ∈
        RingHom.ker (PadicInt.toZModPow m) := by
      rw [RingHom.mem_ker, map_sub, hc, map_natCast, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
    exact hmem
end

