import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.QzBasic
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem qzB_smul_mk (l : ℕ) [Fact l.Prime] (x : ℤ_[l]) (q : ℚ_[l]) :
    x • QZ.mk l q = QZ.mk l ((x : ℚ_[l]) * q) := rfl

private theorem qzB_mk_eq_zero (l : ℕ) [Fact l.Prime] (q : ℚ_[l]) :
    QZ.mk l q = 0 ↔ ∃ z : ℤ_[l], (z : ℚ_[l]) = q :=
  Submodule.Quotient.mk_eq_zero (ZlSub l)

private theorem qzB_mk_surj (l : ℕ) [Fact l.Prime] (a : QZ l) : ∃ q, QZ.mk l q = a :=
  Submodule.Quotient.mk_surjective (ZlSub l) a

theorem UpperTheory.V.Kum.qzBasic :
    ∀ (l : ℕ) [Fact l.Prime], (∀ u : ℤ_[l], u ≠ 0 → Function.Surjective fun x : QZ l => u • x) ∧ (∀ x : QZ l, ∃ k : ℕ, l ^ k • x = 0) ∧ (l ≠ 2 → ∀ x : QZ l, 2 • x = 0 → x = 0) := by
  intro l _
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have tors : ∀ x : QZ l, ∃ k : ℕ, l ^ k • x = 0 := by
    intro x
    obtain ⟨q, rfl⟩ := qzB_mk_surj l x
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖q‖ hl1
    refine ⟨k, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], qzB_smul_mk, qzB_mk_eq_zero]
    have hpos : (0 : ℝ) < (l : ℝ) ^ k := pow_pos (by linarith) k
    refine ⟨⟨_, ?_⟩, rfl⟩
    push_cast
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast, inv_mul_le_iff₀ hpos, mul_one]
    exact hk.le
  refine ⟨?_, tors, ?_⟩
  · intro u hu a
    obtain ⟨q, rfl⟩ := qzB_mk_surj l a
    have hu' : (u : ℚ_[l]) ≠ 0 := PadicInt.coe_ne_zero.2 hu
    refine ⟨QZ.mk l (q / u), ?_⟩
    show u • QZ.mk l (q / u) = QZ.mk l q
    rw [qzB_smul_mk, mul_div_cancel₀ q hu']
  · intro h2 x hx
    obtain ⟨k, hk⟩ := tors x
    have hc : IsCoprime (2 : ℤ) ((l ^ k : ℕ) : ℤ) := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Nat.isCoprime_iff_coprime]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hl).2 (Ne.symm h2))
    obtain ⟨a, b, hab⟩ := hc
    calc x = (1 : ℤ) • x := (one_smul ℤ x).symm
      _ = (a * 2 + b * ((l ^ k : ℕ) : ℤ)) • x := by rw [hab]
      _ = a • ((2 : ℕ) • x) + b • ((l ^ k) • x) := by
        rw [add_smul, mul_smul, mul_smul]
        norm_cast
      _ = 0 := by rw [hx, hk, smul_zero, smul_zero, add_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ReflRoot
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem exp_tors (K : Type) [Field K] [NumberField K] :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ a : K, IsOfFinOrder a → a ^ m = 1 := by
  refine ⟨Units.torsionOrder K, Units.torsionOrder_ne_zero K, fun a ha => ?_⟩
  obtain ⟨k, hk, hak⟩ := isOfFinOrder_iff_pow_eq_one.1 ha
  have hi : IsIntegral ℤ a := IsIntegral.of_pow hk (by rw [hak]; exact isIntegral_one)
  let x : 𝓞 K := ⟨a, hi⟩
  have hx : x ^ k = 1 := by
    apply RingOfIntegers.coe_injective
    rw [map_pow, map_one]
    exact hak
  let y : (𝓞 K)ˣ := Units.ofPowEqOne x k hx hk.ne'
  have hy : y ∈ Units.torsion K :=
    (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, Units.ext (by simpa [y] using hx)⟩)
  rw [← Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hy
  have h2 := congrArg (fun z : (𝓞 K)ˣ => algebraMap (𝓞 K) K z) hy
  simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at h2
  exact h2

private theorem conj_root {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (g u : Ω ≃ₐ[F] Ω) (β : Ω)
    (hβ : IsOfFinOrder β) : g (u (g.symm β)) = u β := by
  have hp := IsPrimitiveRoot.orderOf β
  haveI : NeZero (orderOf β) := ⟨hβ.orderOf_pos.ne'⟩
  have key : ∀ s : Ω ≃ₐ[F] Ω, ∃ i : ℕ, β ^ i = s β := fun s => by
    obtain ⟨i, -, hi⟩ := hp.eq_pow_of_pow_eq_one (ξ := s β) (by rw [← map_pow, pow_orderOf_eq_one, map_one])
    exact ⟨i, hi⟩
  obtain ⟨i, hi⟩ := key g.symm
  obtain ⟨j, hj⟩ := key u
  rw [← hi, map_pow, ← hj, ← pow_mul, mul_comm, pow_mul, hi, map_pow, g.apply_symm_apply]

private theorem exists_gen (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (n : ℕ) [NeZero n] :
    ∃ (ξ : Ωˣ) (b : K), (ξ : Ω) ^ n = algebraMap K Ω b ∧
      ∀ (β : Ω) (a : Kˣ), β ^ n = algebraMap K Ω a → IsOfFinOrder β → ∃ j : ℤ, (ξ : Ω) ^ j = β := by
  obtain ⟨m, hm, hK⟩ := exp_tors K
  haveI : NeZero (n * m) := ⟨mul_ne_zero (NeZero.ne n) hm⟩
  let T : Subgroup Ωˣ := rootsOfUnity (n * m) Ω ⊓
    ((Units.map (algebraMap K Ω).toMonoidHom).range).comap (powMonoidHom n)
  haveI : Finite T := Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left : T ≤ _))
  obtain ⟨⟨ξ, hξ⟩, hg⟩ := (isCyclic_subgroup_units T).exists_generator
  obtain ⟨b, hb⟩ := hξ.2
  refine ⟨ξ, b, ?_, fun β a h hβ => ?_⟩
  · have := congrArg Units.val hb
    simpa using this.symm
  · have h0 : β ≠ 0 := by
      rintro rfl
      rw [zero_pow (NeZero.ne n)] at h
      exact a.ne_zero ((map_eq_zero _).1 h.symm)
    have ha : IsOfFinOrder (a : K) := by
      have := hβ.pow (n := n)
      rw [h] at this
      obtain ⟨k, hk, hak⟩ := isOfFinOrder_iff_pow_eq_one.1 this
      exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, (algebraMap K Ω).injective (by rw [map_pow, hak, map_one])⟩
    have hT : Units.mk0 β h0 ∈ T := by
      refine ⟨(mem_rootsOfUnity _ _).2 (Units.ext ?_), a, Units.ext (by simpa using h.symm)⟩
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      rw [pow_mul, h, ← map_pow, hK a ha, map_one]
    obtain ⟨j, hj⟩ := hg ⟨_, hT⟩
    refine ⟨j, ?_⟩
    have := congrArg (fun z : T => ((z : Ωˣ) : Ω)) hj
    simpa using this

private theorem exists_generator_kummer_cocycle {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (U : Subgroup (Ω ≃ₐ[F] Ω)) (n : ℕ) [NeZero n]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ n) (hU : ∀ u : U, u.1 ζ = ζ) (ξ : Ωˣ) (hξ : ∀ u : U, u.1 (ξ ^ n) = ξ ^ n) :
    ∃ u0 : U, ∀ u : U, ∃ k : ℤ, u.1 ξ / ξ = (u0.1 ξ / ξ) ^ k := by
  have h1 : ∀ u : U, (u.1 ξ / ξ) ^ n = 1 := fun u => by
    rw [div_pow, ← map_pow, hξ, div_self (pow_ne_zero _ ξ.ne_zero)]
  have h2 : ∀ u v : U, u.1 (v.1 ξ / ξ) = v.1 ξ / ξ := fun u v => by
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (h1 v)
    rw [← hi, map_pow, hU]
  have h3 : ∀ u : U, u.1 ξ ≠ 0 := fun u => (map_ne_zero _).2 ξ.ne_zero
  let f : U →* Ωˣ := MonoidHom.mk' (fun u => Units.mk0 (u.1 ξ / ξ) (div_ne_zero (h3 u) ξ.ne_zero)) fun u v => by
    apply Units.ext
    have := h2 u v
    rw [map_div₀, div_eq_iff (h3 u)] at this
    simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul, AlgEquiv.mul_apply, this]
    ring
  have hle : f.range ≤ rootsOfUnity n Ω := by
    rintro _ ⟨u, rfl⟩
    exact (mem_rootsOfUnity _ _).2 (Units.ext (by simpa [f] using h1 u))
  haveI : Finite f.range := Finite.of_injective _ (Subgroup.inclusion_injective hle)
  obtain ⟨⟨_, u0, rfl⟩, hg⟩ := (isCyclic_subgroup_units f.range).exists_generator
  refine ⟨u0, fun u => ?_⟩
  obtain ⟨k, hk⟩ := hg ⟨f u, u, rfl⟩
  refine ⟨k, ?_⟩
  have := congrArg (fun z : f.range => ((z : Ωˣ) : Ω)) hk
  simpa [f] using this.symm

theorem UpperTheory.V.Kum.reflRoot :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (n : ℕ) [NeZero n] (N : ℕ) (ζ : K) [Normal F K] (ψ : G F Ω →* (ZMod n)ˣ), U = galOf F K Ω → IsPrimitiveRoot ζ n →
    Nat.card {φ : U → ZMod n // φ ∈ EqHom N U (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β} ≤ Nat.card (scalRep (ZMod n) ψ).invariants ∧
    Finite {φ : U → ZMod n // φ ∈ EqHom N U (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ), IsRad (algebraMap K Ω ζ) U φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β} := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U n _ N ζ _ ψ hU hζ
  subst hU
  have hζ' : IsPrimitiveRoot (algebraMap K Ω ζ) n := hζ.map_of_injective (algebraMap K Ω).injective
  have hinj : ∀ x y : ZMod n, algebraMap K Ω ζ ^ x.val = algebraMap K Ω ζ ^ y.val → x = y := fun x y h =>
    ZMod.val_injective n (hζ'.pow_inj (ZMod.val_lt x) (ZMod.val_lt y) h)
  obtain ⟨ξ, b, hb, hξ⟩ := exists_gen K Ω n
  obtain ⟨u0, hu0⟩ := exists_generator_kummer_cocycle (galOf F K Ω) n _ hζ' (fun u => u.2 ζ) ξ (fun u => by rw [hb]; exact u.2 b)
  have hinv : ∀ φ : galOf F K Ω → ZMod n, φ ∈ EqHom N (galOf F K Ω) (scalRep (ZMod n) ψ) → ∀ β : Ω,
      IsRad (algebraMap K Ω ζ) _ φ β → IsOfFinOrder β → φ u0 ∈ (scalRep (ZMod n) ψ).invariants := by
    intro φ hφ β hr hβ g
    let u' : galOf F K Ω := ⟨g * u0.1 * g⁻¹, (galOf_normal F K Ω).conj_mem _ u0.2 g⟩
    have h1 : φ u' = scalRep (ZMod n) ψ g (φ u0) :=
      (Submodule.mem_iInf _).1 hφ.2 g u0 u' fun x => by
        show g (u0.1 (g.symm (g x))) = g (u0.1 x)
        rw [g.symm_apply_apply]
    rw [← h1]
    apply hinj
    have h2 : u'.1 β = u0.1 β := conj_root g u0.1 β hβ
    rw [hr.2, hr.2] at h2
    exact mul_right_cancel₀ hr.1 h2
  have hval : ∀ (φ : galOf F K Ω → ZMod n) (j : ℤ), IsRad (algebraMap K Ω ζ) _ φ ((ξ : Ω) ^ j) →
      ∀ u, algebraMap K Ω ζ ^ (φ u).val = (u.1 ξ / ξ) ^ j := fun φ j hr u => by
    rw [div_zpow, ← map_zpow₀, hr.2, mul_div_cancel_right₀ _ hr.1]
  let e : {φ : galOf F K Ω → ZMod n // φ ∈ EqHom N _ (scalRep (ZMod n) ψ) ∧ ∃ (β : Ω) (a : Kˣ),
      IsRad (algebraMap K Ω ζ) _ φ β ∧ β ^ n = algebraMap K Ω a ∧ IsOfFinOrder β} →
      (scalRep (ZMod n) ψ).invariants := fun φ => ⟨φ.1 u0, by
    obtain ⟨h, β, a, hr, -, hβ⟩ := φ.2
    exact hinv _ h β hr hβ⟩
  have he : Function.Injective e := by
    rintro ⟨φ, hφ, β, a, hr, ha, hβ⟩ ⟨φ', hφ', β', a', hr', ha', hβ'⟩ h
    have h0 : φ u0 = φ' u0 := congrArg Subtype.val h
    obtain ⟨j, rfl⟩ := hξ β a ha hβ
    obtain ⟨j', rfl⟩ := hξ β' a' ha' hβ'
    refine Subtype.ext (funext fun u => hinj _ _ ?_)
    obtain ⟨k, hk⟩ := hu0 u
    show algebraMap K Ω ζ ^ (φ u).val = algebraMap K Ω ζ ^ (φ' u).val
    rw [hval φ j hr, hval φ' j' hr', hk, ← zpow_mul, ← zpow_mul, mul_comm k, mul_comm k, zpow_mul, zpow_mul,
      ← hval φ j hr, ← hval φ' j' hr', h0]
  exact ⟨Nat.card_le_card_of_injective e he, Finite.of_injective e he⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RestrMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.restrMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (N : ℕ) (U V : Subgroup (G F Ω)) (h : U ≤ V) (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] (ρ : Representation R (G F Ω) M), (XDual N V R M).map (restr R M h) ≤ XDual N U R M ∧ (EqHom N V ρ).map (restr R M h) ≤ EqHom N U ρ ∧ ∀ (σ : Ω ≃+* Ω) (s : R), (EqEig N V ρ σ s).map (restr R M h) ≤ EqEig N U ρ σ s := by
  intro F Ω _ _ _ _ _ N U V h R M _ _ _ ρ
  have hX : ∀ φ ∈ XDual N V R M, restr R M h φ ∈ XDual N U R M := by
    intro φ hφ
    obtain ⟨h1, h2, h3, h4⟩ := hφ
    refine ⟨h1.comp_continuous (f := Subgroup.inclusion h) (continuous_inclusion h), fun a b => ?_, fun A u hu => ?_,
      fun A hA u hu => ?_⟩
    · exact h2 (Subgroup.inclusion h a) (Subgroup.inclusion h b)
    · exact h3 A (Subgroup.inclusion h u) hu
    · exact h4 A hA (Subgroup.inclusion h u) hu
  have hC : ∀ (σ : Ω ≃+* Ω) (T : M →ₗ[R] M), ∀ φ ∈ conjCond V σ T, restr R M h φ ∈ conjCond U σ T := by
    intro σ T φ hφ u u' hu
    exact hφ (Subgroup.inclusion h u) (Subgroup.inclusion h u') hu
  have hE : ∀ φ ∈ EqHom N V ρ, restr R M h φ ∈ EqHom N U ρ := by
    intro φ hφ
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hφ
    refine Submodule.mem_inf.2 ⟨hX φ h1, (Submodule.mem_iInf _).2 fun g => ?_⟩
    exact hC _ _ φ ((Submodule.mem_iInf _).1 h2 g)
  refine ⟨?_, ?_, fun σ s => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact hX φ hφ
  · rintro _ ⟨φ, hφ, rfl⟩
    exact hE φ hφ
  · rintro _ ⟨φ, hφ, rfl⟩
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hφ
    exact Submodule.mem_inf.2 ⟨hE φ h1, hC _ _ φ h2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ToGalDict
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open scoped Pointwise

theorem UpperTheory.V.Kum.toGalDict :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω),
    (∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Dec (F := K) A ↔ u.1 ∈ Dec (F := F) A) ∧
    (∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Ine (F := K) A ↔ u.1 ∈ Ine (F := F) A) ∧
    Continuous (toGal K hU) ∧ (galOf F K Ω ≤ U → IsHomeomorph (toGal K hU) ∧ IsOpen (U : Set (G F Ω))) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U hU
  obtain ⟨hE, hO, -⟩ := galEmbTop F K Ω
  have hD : ∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Dec (F := K) A ↔ u.1 ∈ Dec (F := F) A := by
    intro A u
    rw [mem_Dec, mem_Dec]
    have e : toGal K hU u • A = u.1 • A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact Iff.rfl
    rw [e]
  have hcomp : galEmb F K Ω ∘ toGal K hU = Subtype.val := funext fun u => AlgEquiv.ext fun x => rfl
  have hc : Continuous (toGal K hU) := by
    rw [hE.isInducing.continuous_iff, hcomp]
    exact continuous_subtype_val
  refine ⟨hD, fun A u => ?_, hc, fun h => ⟨?_, ?_⟩⟩
  · exact ⟨fun h => ⟨(hD A u).1 h.1, h.2⟩, fun h => ⟨(hD A u).2 h.1, h.2⟩⟩
  · rw [isHomeomorph_iff_exists_inverse]
    refine ⟨hc, fun σ => ⟨galEmb F K Ω σ, h (galEmb_mem F K Ω σ)⟩, fun u => Subtype.ext (AlgEquiv.ext fun x => rfl),
      fun σ => AlgEquiv.ext fun x => rfl, hE.continuous.subtype_mk _⟩
  · rw [le_antisymm hU h]
    exact hO
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.UnitMinus
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.unitMinus :
    ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ) (a : Kˣ), a ∈ (∅ : Set (HeightOneSpectrum (𝓞 K))).unit K → a * Units.map (cE K).toMonoidHom a ∈ powK K n → a ^ 2 ∈ CommGroup.torsion Kˣ ⊔ powK K n ∧ (Odd n → a ∈ CommGroup.torsion Kˣ ⊔ powK K n) := by
  intro K _ _ _ n a ha hc
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (a : K)
    (fun v => (ha v (Set.notMem_empty v)).le)
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K ((a⁻¹ : Kˣ) : K)
    (fun v => ((Subgroup.inv_mem _ ha) v (Set.notMem_empty v)).le)
  have hxy : x * y = 1 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [map_mul, hx, hy, map_one, Units.mul_inv]
  let u : (𝓞 K)ˣ := Units.mkOfMulEqOne x y hxy
  let f : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K).toMonoidHom
  have hu : f u = a := Units.ext hx
  have hcu : f (IsCMField.unitsComplexConj K u) = Units.map (cE K).toMonoidHom a := by
    rw [← hu]
    exact Units.ext rfl
  have hfin : IsOfFinOrder (u * (IsCMField.unitsComplexConj K u)⁻¹) :=
    (IsCMField.unitsMulComplexConjInv K u).2
  have htor : a * (Units.map (cE K).toMonoidHom a)⁻¹ ∈ CommGroup.torsion Kˣ := by
    have := f.isOfFinOrder hfin
    rw [map_mul, map_inv, hu, hcu] at this
    exact this
  have h2 : a ^ 2 ∈ CommGroup.torsion Kˣ ⊔ powK K n := by
    have e : a ^ 2 = (a * (Units.map (cE K).toMonoidHom a)⁻¹) * (a * Units.map (cE K).toMonoidHom a) := by
      rw [mul_mul_mul_comm, inv_mul_cancel, mul_one, pow_two]
    rw [e]
    exact Subgroup.mul_mem_sup htor hc
  refine ⟨h2, ?_⟩
  rintro ⟨k, rfl⟩
  have hn : a ^ (2 * k + 1) ∈ CommGroup.torsion Kˣ ⊔ powK K (2 * k + 1) :=
    Subgroup.mem_sup_right ⟨a, rfl⟩
  rw [pow_succ, pow_mul] at hn
  exact (Subgroup.mul_mem_cancel_left _ (Subgroup.pow_mem _ h2 k)).1 hn
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.VanishCyc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem exists_level_pow_dvd_of_not_finOrder (l : ℕ) [hl : Fact l.Prime] (u : ℤ_[l]ˣ) (hu : ¬ IsOfFinOrder u) (a : ℕ) :
    ∃ j : ℕ, ∀ m : ℤ, PadicInt.toZModPow j ((u ^ m : ℤ_[l]ˣ) : ℤ_[l]) = 1 → (l : ℤ) ^ (a + 1) ∣ m := by
  by_contra h
  push_neg at h
  apply hu
  have hK : 0 < l ^ a * (l - 1) :=
    Nat.mul_pos (pow_pos hl.out.pos a) (Nat.sub_pos_of_lt hl.out.one_lt)
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨l ^ a * (l - 1), hK, ?_⟩
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro j
  obtain ⟨m, hm, hnd⟩ := h j
  obtain ⟨w, hwdef⟩ : ∃ w : (ZMod (l ^ j))ˣ, w = Units.map (PadicInt.toZModPow j).toMonoidHom u :=
    ⟨_, rfl⟩
  have hw : ∀ n : ℤ, ((w ^ n : (ZMod (l ^ j))ˣ) : ZMod (l ^ j)) =
      PadicInt.toZModPow j ((u ^ n : ℤ_[l]ˣ) : ℤ_[l]) := by
    intro n
    rw [hwdef, ← map_zpow]
    rfl
  have hwm : w ^ m = 1 := by
    apply Units.ext
    rw [hw, hm, Units.val_one]
  have hom : (orderOf w : ℤ) ∣ m := orderOf_dvd_iff_zpow_eq_one.mpr hwm
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have hcard : orderOf w ∣ (l ^ j).totient := by
    rw [← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  have hdiv : orderOf w ∣ l ^ a * (l - 1) := by
    rcases j with _ | i
    · simp only [pow_zero, Nat.totient_one, Nat.dvd_one] at hcard
      rw [hcard]
      exact one_dvd _
    · rw [Nat.totient_prime_pow_succ hl.out] at hcard
      rw [← Nat.dvd_gcd_mul_iff_dvd_mul] at hcard
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hl.out).mp (Nat.gcd_dvd_right (orderOf w) (l ^ i))
      have hba : b ≤ a := by
        by_contra hba
        push_neg at hba
        apply hnd
        have h1 : (l : ℤ) ^ b ∣ m := by
          have : l ^ b ∣ orderOf w := hb ▸ Nat.gcd_dvd_left _ _
          exact dvd_trans (by exact_mod_cast this) hom
        exact dvd_trans (pow_dvd_pow _ hba) h1
      rw [hb] at hcard
      exact hcard.trans (Nat.mul_dvd_mul_right (pow_dvd_pow l hba) _)
  have hwK : w ^ (l ^ a * (l - 1)) = 1 := orderOf_dvd_iff_pow_eq_one.mp hdiv
  have := hw ((l ^ a * (l - 1) : ℕ) : ℤ)
  rw [zpow_natCast, zpow_natCast, hwK, Units.val_one] at this
  rw [← this, Units.val_one, map_one]

private theorem exists_open_subgroup_cycZ_trivial_mod_pow (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [hl : Fact l.Prime] (j : ℕ) :
    ∃ H : Subgroup (G F Ω), IsOpen (H : Set (G F Ω)) ∧
      ∀ g ∈ H, PadicInt.toZModPow j ((cycZ F Ω l g : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ j)
  haveI : FiniteDimensional F (IntermediateField.adjoin F ({ζ} : Set Ω)) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  refine ⟨(IntermediateField.adjoin F ({ζ} : Set Ω)).fixingSubgroup,
    IntermediateField.fixingSubgroup_isOpen _, fun g hg => ?_⟩
  have hgζ : g ζ = ζ :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg ζ (IntermediateField.mem_adjoin_simple_self F ζ)
  have hspec := cyclotomicCharacter.spec l (n := j) (MulSemiringAction.toRingAut (G F Ω) Ω g) ζ hζ.pow_eq_one
  change PadicInt.toZModPow j ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω g) : ℤ_[l]ˣ) : ℤ_[l]) = 1
  generalize PadicInt.toZModPow j ((cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω g) : ℤ_[l]ˣ) : ℤ_[l]) = z at hspec ⊢
  have h1 : ζ ^ 1 = ζ ^ z.val := by
    rw [pow_one, ← hspec]
    exact hgζ.symm
  have hu := hζ.isUnit_unit (NeZero.ne (l ^ j))
  have h1' : (hζ.isUnit (NeZero.ne (l ^ j))).unit ^ 1 = (hζ.isUnit (NeZero.ne (l ^ j))).unit ^ z.val := by
    apply Units.ext
    simpa using h1
  rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at h1'
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1'.symm
  rw [ZMod.natCast_val, ZMod.cast_id', id, Nat.cast_one] at h2
  exact h2

theorem UpperTheory.V.Kum.vanishCyc :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] (φ : Uinf F Ω l → M) (γ : G F Ω), IsLocallyConstant φ → (∀ a b, φ (a * b) = φ a + φ b) → (∀ m : M, ∃ k : ℕ, l ^ k • m = 0) → ¬ IsOfFinOrder (cycZ F Ω l γ) →
    ∀ x : Uinf F Ω l, x.1 ∈ (Subgroup.zpowers γ).topologicalClosure → φ x = 0 := by
  intro F Ω _ _ _ _ _ l hl M _ φ γ hφ hmul htor hγ x hx
  have h1 : φ 1 = 0 := by simpa using hmul 1 1
  have hpow : ∀ y : Uinf F Ω l, ∀ n : ℕ, φ (y ^ n) = n • φ y := by
    intro y n
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hmul, ih, succ_nsmul]
  obtain ⟨W, hWo, hWeq⟩ := isOpen_induced_iff.mp (hφ.isOpen_fiber 0)
  have hW1 : (1 : G F Ω) ∈ W := by
    have : (1 : Uinf F Ω l) ∈ Subtype.val ⁻¹' W := by
      rw [hWeq]
      exact h1
    exact this
  obtain ⟨E, hE, hEW⟩ := (krullTopology_mem_nhds_one_iff F Ω W).mp (hWo.mem_nhds hW1)
  haveI := hE
  have hN : IsOpen (E.fixingSubgroup : Set (G F Ω)) := IntermediateField.fixingSubgroup_isOpen E
  have hNφ : ∀ y : Uinf F Ω l, y.1 ∈ E.fixingSubgroup → φ y = 0 := by
    intro y hy
    have : y ∈ Subtype.val ⁻¹' W := hEW hy
    rw [hWeq] at this
    exact this
  haveI : Finite (G F Ω ⧸ E.fixingSubgroup) := Subgroup.quotient_finite_of_isOpen _ hN
  obtain ⟨d, hd0, -, hdN⟩ := Subgroup.exists_pow_mem_of_index_ne_zero (Subgroup.index_ne_zero_of_finite (H := E.fixingSubgroup)) γ
  obtain ⟨a, d', hd'l, hdd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0.ne' l hl.out.ne_one
  obtain ⟨j, hj⟩ := exists_level_pow_dvd_of_not_finOrder l (cycZ F Ω l γ) hγ a
  obtain ⟨H, hHo, hH⟩ := exists_open_subgroup_cycZ_trivial_mod_pow F Ω l j
  have ho : IsOpen ((fun g => x.1⁻¹ * g) ⁻¹' ((E.fixingSubgroup : Set (G F Ω)) ∩ (H : Set (G F Ω)))) :=
    (hN.inter hHo).preimage (continuous_const.mul continuous_id)
  have hxo : x.1 ∈ (fun g => x.1⁻¹ * g) ⁻¹' ((E.fixingSubgroup : Set (G F Ω)) ∩ (H : Set (G F Ω))) := by
    simp only [Set.mem_preimage, inv_mul_cancel, Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨one_mem _, one_mem _⟩
  have hx' : x.1 ∈ closure ((Subgroup.zpowers γ : Subgroup (G F Ω)) : Set (G F Ω)) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact hx
  obtain ⟨g, hgo, hgz⟩ := mem_closure_iff.mp hx' _ ho hxo
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgz
  obtain ⟨hνN, hνH⟩ := hgo
  have hcx : cycZ F Ω l x.1 = 1 := (Subgroup.mem_inf.mp x.2).2
  have hcyc : PadicInt.toZModPow j ((cycZ F Ω l γ ^ m : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    have := hH _ hνH
    rwa [map_mul, map_inv, hcx, inv_one, one_mul, map_zpow] at this
  have hma : (l : ℤ) ^ a ∣ m := (pow_dvd_pow _ (Nat.le_succ a)).trans (hj m hcyc)
  have hcl : closure ((Subgroup.zpowers γ : Subgroup (G F Ω)) : Set (G F Ω)) ⊆ {y | y * γ = γ * y} := by
    apply closure_minimal
    · intro y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.self_zpow γ i).symm.eq
    · exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  have hxγ : Commute x.1 γ := hcl hx'
  have hxν : Commute x.1 (x.1⁻¹ * γ ^ m) := (Commute.refl x.1).inv_right.mul_right (hxγ.zpow_right m)
  have hexp : (γ ^ m) ^ d' = x.1 ^ d' * (x.1⁻¹ * γ ^ m) ^ d' := by
    rw [← hxν.mul_pow, mul_inv_cancel_left]
  have hγN : (γ ^ m) ^ d' ∈ E.fixingSubgroup := by
    obtain ⟨t, ht⟩ := hma
    have : (γ ^ m) ^ d' = (γ ^ d) ^ t := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, ht, hdd]
      congr 1
      push_cast
      ring
    rw [this]
    exact zpow_mem hdN t
  have hxN : (x ^ d').1 ∈ E.fixingSubgroup := by
    have : (x ^ d').1 = (γ ^ m) ^ d' * ((x.1⁻¹ * γ ^ m) ^ d')⁻¹ := by
      rw [hexp, mul_inv_cancel_right]
      rfl
    rw [this]
    exact mul_mem hγN (inv_mem (pow_mem hνN d'))
  have h0 : d' • φ x = 0 := by
    rw [← hpow]
    exact hNφ _ hxN
  obtain ⟨k, hk⟩ := htor (φ x)
  have ho1 : addOrderOf (φ x) ∣ d' := addOrderOf_dvd_of_nsmul_eq_zero h0
  have ho2 : addOrderOf (φ x) ∣ l ^ k := addOrderOf_dvd_of_nsmul_eq_zero hk
  have hcop : Nat.Coprime d' (l ^ k) :=
    Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hl.out).mpr hd'l))
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one (by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd ho1 ho2))
end

