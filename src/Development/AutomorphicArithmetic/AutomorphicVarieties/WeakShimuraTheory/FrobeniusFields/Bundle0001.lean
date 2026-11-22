import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsResQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.ExistsDecompositionElementAtLXiPowFourNeOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open UpperTheory.V

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem dirG_pow {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) (k : ℕ) (g : G ℚ Ω) :
    Chr.dirG ℚ Ω (χ ^ k) g = Chr.dirG ℚ Ω χ g ^ k := Units.ext (MulChar.pow_apply_coe χ k _)

private theorem dirG_one {O : Type} [CommRing O] {N : ℕ} [NeZero N] (g : G ℚ Ω) :
    Chr.dirG ℚ Ω (1 : DirichletCharacter O N) g = 1 := Units.ext (MulChar.one_apply_coe _)

private theorem dirG_frob {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {A : ValuationSubring Ω} {v : ℕ}
    (hv : v.Prime) (hA : A.valuation (v : Ω) < 1) (hN : ¬ v ∣ N) {σ : G ℚ Ω} (h : IsFrob (F := ℚ) A v σ) :
    (Chr.dirG ℚ Ω χ σ : O) = χ v := by
  have h1 := (ML.placeBasic Ω).2.2.2.2.2.2.1 A v N σ h
    ((ML.placeBasic Ω).2.2.2.1 A v N ((Nat.Prime.coprime_iff_not_dvd hv).2 hN) hA)
  have h2 := (Chr.clsFacts ℚ Ω N).2.2.1 σ (ZMod.unitOfCoprime v ((Nat.Prime.coprime_iff_not_dvd hv).2 hN)) fun ζ hζ => by
    rw [h1 ζ hζ, ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod v hζ]
  rw [Chr.dirG, MonoidHom.comp_apply, h2, MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime]

private theorem pow_cond {O : Type} [CommRing O] {N : ℕ} [NeZero N] (χ : DirichletCharacter O N) {k : ℕ}
    (h : χ.conductor = 2 ^ k) : χ ^ 2 ^ k = 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h1 : χ.primitiveCharacter ^ Nat.totient χ.conductor = 1 := by
    ext u
    rw [MulChar.pow_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one,
      MulChar.one_apply_coe]
  have h2 : Nat.totient χ.conductor ∣ 2 ^ k := by
    rw [h]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Nat.totient_prime_pow Nat.prime_two hk]
      simpa using pow_dvd_pow 2 (Nat.sub_le k 1)
  obtain ⟨j, hj⟩ := h2
  rw [← χ.changeLevel_primitiveCharacter, ← map_pow, hj, pow_mul, h1, one_pow, map_one]

private theorem psi_exp (h : Host) {O : Type} [CommRing O] [IsDomain O] (ψ : DirichletCharacter O h.N) (hψ : h.IsChar ψ)
    {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) :
    ∃ a u : ℕ, Odd u ∧ ψ ^ (2 ^ a * u) = 1 ∧ l ^ 2 * 2 ^ (a + 2) ≤ 2 ^ h.nII l ψ := by
  have hq : 0 < h.q := NeZero.pos _
  have ho : 0 < h.o := orderOf_pos _
  obtain ⟨tψ, ⟨s, hs⟩, -⟩ := X.th1Facts O h.N ψ l hl hl2
  obtain ⟨-, -, t3, -⟩ := hostTh1 h O ψ hψ l hl hl2
  obtain ⟨-, b2⟩ := max_le_iff.1 (Nat.le_pow_clog one_lt_two _ : _ ≤ 2 ^ h.nII l ψ)
  refine ⟨c2 ψ + 1 + h.o.factorization 2, ordCompl[2] h.o * l ^ s, ?_, ?_, ?_⟩
  · exact (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (Nat.not_dvd_ordCompl Nat.prime_two ho.ne'))).mul (hl.odd_of_ne_two hl2).pow
  · have e1 : 2 ^ (c2 ψ + 1 + h.o.factorization 2) * (ordCompl[2] h.o * l ^ s) = 2 ^ c2 ψ * (2 * h.o) * l ^ s := by
      conv_rhs => rw [← Nat.ordProj_mul_ordCompl_eq_self h.o 2]
      ring
    have p1 := pow_cond (psi2 ψ) (compCond O h.N ψ 2 Nat.prime_two).2.2.2.1.symm
    have p2 := orderOf_dvd_iff_pow_eq_one.1 t3
    rw [e1]
    generalize c2 ψ = k at p1 ⊢
    have p3 : (psi2 ψ * th1 l ψ * kap l ψ) ^ (2 ^ k * (2 * h.o) * l ^ s) = 1 := by
      rw [mul_pow, mul_pow, mul_assoc (2 ^ k), pow_mul, p1, one_pow, one_mul, mul_left_comm, pow_mul, p2, one_pow, one_mul,
        ← mul_assoc, mul_comm, pow_mul, hs, one_pow]
    rwa [← tψ] at p3
  · have v2 : 2 ^ h.o.factorization 2 ≤ h.o := Nat.ordProj_le 2 ho.ne'
    refine le_trans ?_ b2
    calc l ^ 2 * 2 ^ (c2 ψ + 1 + h.o.factorization 2 + 2) = 2 ^ (c2 ψ + 3) * 2 ^ h.o.factorization 2 * l ^ 2 * 1 := by ring
      _ ≤ 2 ^ (c2 ψ + 6) * h.o * l ^ 3 * h.q ^ 2 := by
        gcongr
        · norm_num
        · omega
        · exact hl.one_le
        · omega
        · exact Nat.one_le_pow _ _ hq

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.exists_decomposition_element_at_l_xi_pow_four_ne_one :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ (κ : G ℚ Ω →* c.Oˣ) (j : ℕ), κ ^ l ^ j = 1 → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ g ∈ Dec (F := ℚ) A, Raw.bar D.Psi g = 1 ∧ κ g = 1 ∧ Raw.bar D.ξ g ^ 4 ≠ 1 := by
  intro Ω _ _ _ l hl c D ⟨hD, h, t, e, ψ, _, _, _, hmem, _, hO⟩ κ j hκ A hA
  have hlp : l.Prime := hl.out
  have hl2 := hD.l_odd
  obtain ⟨a, u, hu, hψ, hb⟩ := psi_exp h ψ (h.mem_X.1 hmem).1 hlp hl2
  obtain ⟨_, ξ, ξ₀, hξ, -, h0, dξ⟩ := hO.xi
  rw [orderOf_eq_one_iff] at h0
  have hT : l ∈ D.T := Finset.mem_insert_self _ _
  have hfr := hD.sg_frob l hT
  obtain ⟨w, hw, -⟩ := (Chr.placesQ Ω).2.2 l _ A hlp (hD.pl_over l hlp) hA
  have conj : ∀ (γ : G ℚ Ω →* c.Oˣ) (x : G ℚ Ω) (k : ℕ), γ (w⁻¹ * x ^ k * w) = γ x ^ k := fun γ x k => by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul, map_pow]
  generalize h.nII l ψ = n at hb ξ hξ dξ
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : 0 < l ^ 2 * 2 ^ a := by have := hlp.pos; positivity
      rw [pow_add, ← mul_assoc] at hb
      omega
    · exact hn
  have h2 : ¬ l ∣ 2 := fun hd => hl2 ((Nat.prime_dvd_prime_iff_eq hlp Nat.prime_two).1 hd)
  refine ⟨_, hw _ (pow_mem hfr.1 (2 ^ a * u * l ^ j)), ?_, ?_, fun hx => ?_⟩
  · have : D.Psi (D.sg l) = Chr.dirG ℚ Ω ψ (D.sg l) := by
      rw [Raw.Psi, Chr.Psi, zpow_natCast, MonoidHom.mul_apply, MonoidHom.pow_apply, chiO, MonoidHom.comp_apply, hD.sg_cyc,
        map_one, one_pow, one_mul, hO.psi]
    rw [Raw.bar, conj, this, pow_mul, ← dirG_pow, hψ, dirG_one, one_pow, Units.val_one, map_one]
  · rw [conj, mul_comm, pow_mul, ← MonoidHom.pow_apply, hκ, MonoidHom.one_apply, one_pow]
  · have e1 : 2 ^ a * u * l ^ j * 4 = 2 ^ (a + 2) * (u * l ^ j) := by ring
    rw [Raw.bar, conj, ← map_pow, ← Units.val_pow_eq_pow_val, ← pow_mul, e1, dξ, MonoidHom.mul_apply, h0, dirG_one,
      one_mul] at hx
    have r4 : Chr.dirG ℚ Ω ξ (D.sg l) ^ (2 ^ (a + 2) * (u * l ^ j)) = 1 := by
      refine (congrFacts Ω l c).2.2.2.1 _ _ (Nat.totient (2 ^ n)) ?_ ?_ (one_pow _)
        (Ideal.Quotient.eq.1 (hx.trans (map_one (residue c.O)).symm))
      · rw [Nat.totient_prime_pow Nat.prime_two hn]
        exact fun hd => h2 (hlp.dvd_of_dvd_pow (by simpa using hd))
      · rw [← pow_mul, mul_comm, pow_mul, Chr.dirG, MonoidHom.comp_apply, ← map_pow, ZMod.pow_totient, map_one, one_pow]
    have r5 := congrArg Units.val r4
    rw [Units.val_pow_eq_pow_val, dirG_frob ξ hlp (hD.pl_over l hlp) (fun hd => h2 (hlp.dvd_of_dvd_pow hd)) hfr] at r5
    exact (UpperTheory.two_pow_lt_sq_mul_of_primitive_char_pow_eq_one c.O n ξ hξ l (a + 2) _ (hlp.odd_of_ne_two hl2) hlp.one_lt
      (hu.mul (hlp.odd_of_ne_two hl2).pow) r5).not_ge hb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.FixAb
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.fixAb :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (H : Subgroup (G ℚ Ω)), IsOpen (H : Set (G ℚ Ω)) → commutator (G ℚ Ω) ≤ H → ∃ (F : IntermediateField ℚ Ω) (_ : NumberField F) (_ : IsAbelianGalois ℚ F), F.fixingSubgroup = H ∧ Module.finrank ℚ F = H.index := by
  intro Ω _ _ hc V hV hcomm
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hcl : IsClosed (V : Set (Ω ≃ₐ[ℚ] Ω)) := Subgroup.isClosed_of_isOpen V hV
  set L : IntermediateField ℚ Ω := IntermediateField.fixedField (V : Subgroup (Ω ≃ₐ[ℚ] Ω)) with hL
  have hfix : L.fixingSubgroup = V := InfiniteGalois.fixingSubgroup_fixedField ⟨V, hcl⟩
  have hnorm : V.Normal := ⟨fun n hn g => by
    have h : g * n * g⁻¹ * n⁻¹ ∈ V :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have := mul_mem h hn
    rwa [inv_mul_cancel_right] at this⟩
  haveI hfin : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).1 (by rw [hfix]; exact hV)
  haveI hgal : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hfix]; exact hnorm)
  have hsurj : Function.Surjective (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L) :=
    AlgEquiv.restrictNormalHom_surjective Ω
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Ω) L).ker = V :=
    (@IntermediateField.restrictNormalHom_ker ℚ Ω _ _ _ L hgal.to_normal).trans hfix
  have hab : IsAbelianGalois ℚ L :=
    { is_comm := ⟨fun a b => by
        obtain ⟨a, rfl⟩ := hsurj a
        obtain ⟨b, rfl⟩ := hsurj b
        have h : a * b * a⁻¹ * b⁻¹ ∈ V :=
          hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
        rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
          mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
        exact h⟩ }
  have hnf : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := hfin }
  refine ⟨L, hnf, hab, hfix, ?_⟩
  exact (IntermediateField.finrank_eq_fixingSubgroup_index Ω L).trans (congrArg Subgroup.index hfix)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.FixInf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem ext_cc {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω)
    (φ : F →+* ℂ) :
    ∃ (σ : G ℚ Ω) (j : Ω →+* ℂ), (∀ x, j (σ x) = starRingEnd ℂ (j x)) ∧ ∀ x : F, j x = φ x := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  haveI : Module.IsTorsionFree F Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨j, hj⟩ : ∃ j : Ω →+* ℂ, ∀ x : F, j x = φ x := by
    letI : Algebra F ℂ := φ.toAlgebra
    let j : Ω →ₐ[F] ℂ := IsAlgClosed.lift
    exact ⟨j.toRingHom, fun x => j.commutes x⟩
  letI : Algebra Ω ℂ := j.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.toRatAlgHom.commutes x).symm
  let cj : Ω →ₐ[ℚ] ℂ := ((starRingEnd ℂ).comp j).toRatAlgHom
  exact ⟨cj.restrictNormal' Ω, j, fun x => AlgHom.restrictNormal_commutes cj Ω x, hj⟩

theorem UpperTheory.V.Ws.fixInf :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (F : IntermediateField ℚ Ω) [NumberField F], ((∀ σ : G ℚ Ω, IsCC σ → σ ∈ F.fixingSubgroup) → IsTotallyReal F) ∧ ((∀ σ : G ℚ Ω, IsCC σ → σ ∉ F.fixingSubgroup) → Module.finrank ℚ F = 2 → IsCMField F) := by
  intro Ω _ _ _ F _
  refine ⟨fun h => ⟨fun w => ?_⟩, fun h h2 => ?_⟩
  · obtain ⟨σ, j, hσ, hj⟩ := ext_cc F w.embedding
    have hm := (F.mem_fixingSubgroup_iff σ).1 (h σ ⟨j, hσ⟩)
    refine InfinitePlace.isReal_iff.2 (RingHom.ext fun x => ?_)
    show starRingEnd ℂ (w.embedding x) = w.embedding x
    rw [← hj, ← hσ, hm x.1 x.2]
  · haveI : IsTotallyComplex F := ⟨fun w => by
      rw [← InfinitePlace.not_isReal_iff_isComplex]
      intro hw
      obtain ⟨σ, j, hσ, hj⟩ := ext_cc F w.embedding
      refine h σ ⟨j, hσ⟩ ((F.mem_fixingSubgroup_iff σ).2 fun x hx => j.injective ?_)
      have e : starRingEnd ℂ (w.embedding ⟨x, hx⟩) = w.embedding ⟨x, hx⟩ :=
        RingHom.congr_fun (InfinitePlace.isReal_iff.1 hw) ⟨x, hx⟩
      rw [← hj] at e
      rw [hσ]; exact e⟩
    haveI : Algebra.IsQuadraticExtension ℚ F := ⟨h2⟩
    exact IsCMField.ofCMExtension ℚ F
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.KxKapL
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open UpperTheory.V

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]

private theorem kx_cls (n : ℕ) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1) : Chr.cls ℚ Ω (l ^ n) s = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  refine (Chr.clsFacts ℚ Ω (l ^ n)).2.2.1 s _ fun ζ hζ => ?_
  have h1 := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω s) ζ hζ
  have h2 : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω s) = 1 := h
  rw [h2, Units.val_one, map_one] at h1
  exact h1

variable {O : Type} [CommRing O] [IsDomain O] {N : ℕ} [NeZero N]

private theorem kx_kapL (ψ : DirichletCharacter O N) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1) :
    kapL l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := by
  haveI : NeZero (ordProj[l] N) := ⟨(Nat.ordProj_pos N l).ne'⟩
  have h3 : proj l N (Chr.cls ℚ Ω N s) = 1 := by
    rw [← MonoidHom.mem_ker, (projFacts N l hl.out).2.2.2.2.2.2.1, MonoidHom.mem_ker, ← MonoidHom.comp_apply,
      (Chr.clsFacts ℚ Ω N).2.1]
    exact kx_cls _ h
  have h4 : (kapL l ψ).toUnitHom (Chr.cls ℚ Ω N s) = 1 := by rw [kapL, (compAlg O N l hl.out).1, h3, map_one]
  exact congrArg Units.val h4

private theorem kx_pow (ψ : DirichletCharacter O N) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1)
    (hk : Chr.dirG ℚ Ω (kapB l ψ) s = 1) : Chr.dirG ℚ Ω ψ s ^ orderOf (th0 l ψ) = 1 := by
  ext1
  show ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) ^ _ = 1
  have a1 : kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := congrArg Units.val hk
  have a3 : ψ = th0 l ψ * (kapB l ψ * kapL l ψ) := by rw [kapB, inv_mul_cancel_right, dirichletPrimeToLPart_mul_lPowerPart]
  have a4 : ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = th0 l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) := by
    conv_lhs => rw [a3]
    rw [MulChar.mul_apply, MulChar.mul_apply, a1, kx_kapL ψ h, one_mul, mul_one]
  rw [a4, ← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]

private theorem kx_unr (ψ : DirichletCharacter O N) {s : G ℚ Ω} (h : cycZ ℚ Ω l s = 1)
    (hψ : Chr.dirG ℚ Ω ψ s = 1) : Chr.dirG ℚ Ω (kapB l ψ) s = 1 := by
  ext1
  show kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1
  have a1 : ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := congrArg Units.val hψ
  have a2 : kap l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) = 1 := by
    rw [kap, lPart, MulChar.pow_apply_coe, a1, one_pow]
  have a3 : kap l ψ = kapB l ψ * kapL l ψ := by rw [kapB, inv_mul_cancel_right]
  rwa [a3, MulChar.mul_apply, kx_kapL ψ h, mul_one] at a2

private theorem kx_ord (ψ : DirichletCharacter O N) :
    Chr.dirG ℚ Ω (kapB l ψ) ^ l ^ (orderOf ψ).factorization l = 1 := by
  have h1 : kap l ψ ^ l ^ (orderOf ψ).factorization l = 1 := by
    rw [← (partOrd _ l hl.out ψ ψ.orderOf_pos).1]
    exact pow_orderOf_eq_one _
  obtain ⟨-, -, hone, -, hpow, -⟩ := compAlg O N l hl.out
  have h2 : kapB l ψ ^ l ^ (orderOf ψ).factorization l = 1 := by
    rw [kapB, kapL, mul_pow, inv_pow, ← hpow, h1, hone, inv_one, one_mul]
  refine MonoidHom.ext fun s => Units.ext ?_
  show kapB l ψ ((Chr.cls ℚ Ω N s : (ZMod N)ˣ) : ZMod N) ^ _ = 1
  rw [← MulChar.pow_apply_coe, h2, MulChar.one_apply_coe]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Ws.kapEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (N : ℕ) [NeZero N] (ψ : DirichletCharacter c.O N), D.ψ = Chr.dirG ℚ Ω ψ → ∃ κ, Kap D κ := by
  intro Ω _ _ _ l hl c D hD N _ ψ hψ
  have hnd : ¬ l ∣ orderOf (th0 l ψ) := (partOrd _ l hl.out ψ ψ.orderOf_pos).2.2.1
  refine ⟨Chr.dirG ℚ Ω (kapB l ψ), ?_, ⟨_, kx_ord ψ⟩, fun A hA g hg => ?_, fun A hA => ?_, fun A hA g hg hb hk => ?_,
    orderOf (th0 l ψ), (Nat.Prime.coprime_iff_not_dvd hl.out).2 hnd, fun g hg hk => hψ ▸ kx_pow ψ hg hk⟩
  · refine Subgroup.isOpen_mono (fun s hs => ?_) (Chr.clsFacts ℚ Ω N).1
    rw [MonoidHom.mem_ker] at hs ⊢
    rw [Chr.dirG, MonoidHom.comp_apply, hs, map_one]
  · exact kx_unr ψ ((places ℚ Ω l A).2.2.2 (hA l hD.l_mem) hg) (hψ ▸ hD.psi_unr A hA hg)
  · refine ((compIne Ω N l hl.out A hA).2 c.O _).2.2 ?_
    obtain ⟨-, hmul, -, hinv, -, h6, -⟩ := compAlg c.O N l hl.out
    rw [kapB, kapL, hmul, hinv, (h6 _).1, mul_inv_cancel]
  · have h1 : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 (hA l (Finset.mem_singleton_self l)) hg
    have h2 : chiO ℚ Ω l c.O g = 1 := by rw [chiO, MonoidHom.comp_apply, h1, map_one]
    have h3 : D.Psi g = D.ψ g := by
      rw [Raw.Psi, Chr.Psi, MonoidHom.mul_apply, zpow_natCast, MonoidHom.pow_apply, h2, one_pow, one_mul]
    refine (congrFacts Ω l c).2.2.2.1 _ 1 _ hnd (hψ ▸ kx_pow ψ h1 hk) (one_pow _) ?_
    rw [← residue_eq_zero_iff, map_sub, Units.val_one, map_one, sub_eq_zero, ← h3]
    exact hb
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.NegVal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem neg_val {Γ O : Type} [Group Γ] [CommRing O] [IsDomain O] (χ : Γ →* Oˣ) (h0 : 0 < orderOf χ)
    (h : Even (orderOf χ)) : ∃ σ, χ σ = -1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : χ ^ k ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by omega)
  obtain ⟨σ, hσ⟩ : ∃ σ, χ σ ^ k ≠ 1 := by
    by_contra hn
    push Not at hn
    exact h1 (MonoidHom.ext hn)
  have h2 : (χ σ ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_two, ← hk, ← MonoidHom.pow_apply, pow_orderOf_eq_one, MonoidHom.one_apply]
  have h3 : ((χ σ ^ k : Oˣ) : O) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  refine ⟨σ ^ k, ?_⟩
  rw [map_pow]
  rcases sq_eq_one_iff.1 h3 with h4 | h4
  · exact absurd (Units.ext h4) hσ
  · exact Units.ext h4

theorem UpperTheory.V.Ws.ev2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → ∀ (κ : G ℚ Ω →* c.Oˣ) (j : ℕ), κ ^ l ^ j = 1 → ∃ t, D.om t = 1 ∧ κ t = 1 ∧ Raw.bar D.Psi t = -1 := by
  intro Ω _ _ _ l hl c D ⟨hG, h, t, e, ψ, _, _, _, _, ⟨_, hev, _⟩, hO⟩ κ j hκ
  have lp : l.Prime := hl.out
  have hT : IsOmT c D.om := ⟨hG.om_pow, fun σ => by
    have := hG.om_bar σ
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
    exact sub_eq_zero.2 this⟩
  have hk := ((omT Ω l c).2 D.om hT).2.1
  obtain ⟨b, -, -, hb⟩ := (psiBar Ω l c D.om hT h.N ψ).1
  have ho := (psiBar Ω l c D.om hT h.N (chiP l ψ)).2.2.1
  obtain ⟨σ, hσ⟩ := neg_val (Chr.dirG ℚ Ω (chiP l ψ)) (ho ▸ (chiP l ψ).orderOf_pos) (ho ▸ hev)
  obtain ⟨-, hmul, -, hinv, -, h6, -⟩ := compAlg c.O h.N l lp
  have h1 : comp l (chiP l ψ) = 1 := by rw [chiP, hmul, hinv, (h6 _).1, mul_inv_cancel]
  have hA := hG.pl_over l lp
  have hI := ((compIne Ω h.N l lp _ hA).2 c.O (chiP l ψ)).2.2 h1
  obtain ⟨τ, hτ, hc⟩ : Chr.cls ℚ Ω l σ ∈ (Ine (F := ℚ) (D.pl l)).map (Chr.cls ℚ Ω l) := by
    rw [(compIne Ω l l lp _ hA).1, (projFacts l l lp).2.2.2.2.2.1, MonoidHom.mem_ker]
    have : Subsingleton (ZMod (ordCompl[l] l)) := by
      rw [lp.factorization_self, pow_one, Nat.div_self lp.pos]
      infer_instance
    exact Subsingleton.elim _ _
  have e1 : D.om (σ * τ⁻¹) = 1 := by
    rw [← MonoidHom.mem_ker, hk, MonoidHom.mem_ker, map_mul, map_inv, hc, mul_inv_cancel]
  have e2 : Chr.dirG ℚ Ω (chiP l ψ) (σ * τ⁻¹) = -1 := by
    rw [map_mul, map_inv, hσ, MonoidHom.mem_ker.1 (hI hτ), inv_one, mul_one]
  have e3 : D.om ((σ * τ⁻¹) ^ l ^ j) = 1 := by rw [map_pow, e1, one_pow]
  have e4 : Chr.dirG ℚ Ω (chiP l ψ) ((σ * τ⁻¹) ^ l ^ j) = -1 := by
    rw [map_pow, e2, ((lp.odd_of_ne_two hG.l_odd).pow).neg_one_pow]
  refine ⟨(σ * τ⁻¹) ^ l ^ j, e3, ?_, ?_⟩
  · rw [map_pow, ← MonoidHom.pow_apply, hκ, MonoidHom.one_apply]
  · have e5 := hb D.e ((σ * τ⁻¹) ^ l ^ j)
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, e3, e4, one_pow, one_mul, ← hO.psi,
      ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at e5
    refine e5.trans ?_
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.PrimeEq
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem prime_eq {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h1 : A.valuation (p : Ω) < 1) (h2 : A.valuation (q : Ω) < 1) : p = q := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  have hi : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n => (A.valuation_le_one_iff _).2 (intCast_mem A n)
  have h3 : A.valuation ((a : Ω) * (p : Ω) + (b : Ω) * (q : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hi a)) h1
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hi b)) h2
  have h4 : (a : Ω) * (p : Ω) + (b : Ω) * (q : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h4, map_one] at h3
  exact lt_irrefl _ h3

theorem UpperTheory.V.Ws.away :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → (∀ (A : ValuationSubring Ω) (p q : ℕ), p.Prime → q.Prime → A.valuation (p : Ω) < 1 → A.valuation (q : Ω) < 1 → p = q) ∧ (∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, D.om g = 1 ∧ D.Psi g = D.ψ g) ∧ (∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → Ine (F := ℚ) A ≤ D.ξ.ker) ∧ (∀ σ : G ℚ Ω, IsCC σ → D.om σ = -1) ∧ ∀ (A : ValuationSubring Ω) (p : ℕ), p.Prime → p ∉ D.S → A.valuation (p : Ω) < 1 → Raw.Away D.S A ∧ ∀ g ∈ Ine (F := ℚ) A, D.Psi g = 1 ∧ D.ξ g = 1 ∧ D.om g = 1 := by
  intro Ω _ _ _ l hl c D hD
  have hom : IsOmT c D.om := ⟨hD.om_pow, fun σ => by
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact hD.om_bar σ⟩
  obtain ⟨-, -, -, -, hcc, hunr, -, -⟩ := (omT Ω l c).2 D.om hom
  have h2 : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A,
      D.om g = 1 ∧ D.Psi g = D.ψ g := fun A hA g hg => by
    refine ⟨hunr A hA hg, ?_⟩
    have h1 : cycZ ℚ Ω l g = 1 := (places ℚ Ω l A).2.2.2 hA hg
    have h3 : chiO ℚ Ω l c.O g = 1 := by rw [chiO, MonoidHom.comp_apply, h1, map_one]
    show chiO ℚ Ω l c.O g ^ (D.e : ℤ) * D.ψ g = D.ψ g
    rw [h3, one_zpow, one_mul]
  refine ⟨prime_eq, h2, fun A hA g hg => ?_, fun σ hσ => hcc σ hσ hD.l_odd, fun A p hp hS hA => ?_⟩
  · obtain ⟨u, -, hu⟩ := (UpperTheory.V.Chr.placesQ Ω).2.2 l A (D.pl l) hl.out hA (hD.pl_over l hl.out)
    have h1 := hD.xi_unrT l (Finset.mem_insert_self _ _) (hu g hg)
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, inv_mul_cancel_comm] at h1
    exact h1
  · have ha : Raw.Away D.S A := fun q hq h => hS (prime_eq A p q hp (hD.S_prime q hq) hA h ▸ hq)
    refine ⟨ha, fun g hg => ?_⟩
    obtain ⟨e1, e2⟩ := h2 A (ha l hD.l_mem) g hg
    exact ⟨e2.trans (hD.psi_unr A ha hg), hD.xi_unr A ha hg, e1⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.PsiCc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws
open Formalism.GaloisCohomology UpperTheory.V UpperTheory.Top

private theorem psi_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] {N : ℕ} [NeZero N] (ψ : DirichletCharacter O N) (e : ℕ) {σ : G ℚ Ω} (h : IsConjOm σ.toRingEquiv)
    (hψ : PsiEven e ψ) : Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ = 1 := by
  have h1 : cycZ ℚ Ω l σ = -1 := h.cyc (E := ℚ)
  have h2 : Chr.cls ℚ Ω N σ = -1 := (Chr.clsFacts ℚ Ω N).2.2.2.1 σ h
  have h3 : chiO ℚ Ω l O σ = -1 := by
    ext
    simp [chiO, h1]
  have h4 : ((Chr.Psi l e (Chr.dirG ℚ Ω ψ) σ : Oˣ) : O) = (-1) ^ e * ψ (-1) := by
    simp [Chr.Psi, Chr.dirG, h2, h3]
  have h5 : ((-1 : O) ^ e) * (-1) ^ e = 1 := by rw [← mul_pow]; simp
  rw [Units.ext_iff, h4, Units.val_one, hψ, h5]

theorem UpperTheory.V.Ws.xi2 :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx2 D → (∃ n : ℕ, D.ξ ^ 2 ^ n = 1) ∧ (∀ A, Raw.Away {2} A → Ine (F := ℚ) A ≤ D.ξ.ker) ∧ ∀ σ : G ℚ Ω, IsCC σ → D.Psi σ = 1 := by
  intro Ω _ _ _ l _ c D hD
  obtain ⟨-, h, t, e, ψ, -, -, -, hψ, -, hO⟩ := hD
  obtain ⟨he, hp, -, _, ξ', ξ₀, -, -, h0, hξ⟩ := hO
  generalize h.nII l ψ = n at ξ' hξ
  have h1 : ξ₀ = 1 := orderOf_eq_one_iff.1 h0
  have h2 : ∀ σ, D.ξ σ = ξ'.toUnitHom (Chr.cls ℚ Ω (2 ^ n) σ) := by
    intro σ
    rw [hξ, MonoidHom.mul_apply, h1]
    have : Chr.cls ℚ Ω 1 σ = 1 := Subsingleton.elim _ _
    simp [Chr.dirG, this]
  refine ⟨⟨n, ?_⟩, fun A hA σ hσ => ?_, fun σ hσ => ?_⟩
  · ext1 σ
    rw [MonoidHom.pow_apply, h2, ← map_pow, MonoidHom.one_apply]
    have h3 : Chr.cls ℚ Ω (2 ^ n) σ ^ 2 ^ n = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]
      refine orderOf_dvd_card.trans ?_
      rw [ZMod.card_units_eq_totient]
      rcases n with _ | n
      · simp
      · rw [Nat.totient_prime_pow_succ Nat.prime_two]
        simp [pow_succ]
    rw [h3, map_one]
  · have h3 : ¬ A.valuation ((2 ^ n : ℕ) : Ω) < 1 := by
      have h4 := hA 2 (Finset.mem_singleton_self 2)
      rw [Nat.cast_pow, map_pow]
      exact not_lt.2 (one_le_pow₀ (not_lt.1 h4))
    have h4 : Chr.cls ℚ Ω (2 ^ n) σ = 1 := (Chr.clsFacts ℚ Ω (2 ^ n)).2.2.2.2 A h3 hσ
    rw [MonoidHom.mem_ker, h2, h4, map_one]
  · rw [Raw.Psi, he, hp]
    exact psi_cc Ω l ψ e hσ (h.mem_X.1 hψ).2
end

