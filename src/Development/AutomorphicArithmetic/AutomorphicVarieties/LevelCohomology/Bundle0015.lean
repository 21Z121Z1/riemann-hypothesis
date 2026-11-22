import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0014
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.DirGPowOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.HcXvan
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Module UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.X

private theorem xvan_of_van {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
    (D : Raw Ω c) (γ : G ℚ Ω →* c.Oˣ) (γ' : G ℚ Ω →* (ResidueField c.O)ˣ)
    (h : ∀ g, Raw.bar γ g = (γ' g : ResidueField c.O)) (hv : Van D.T D.pl D.rbar.ker γ') : D.XVan γ := by
  intro z hzlc hzc hzU hzD
  obtain ⟨m, hm⟩ := hv z hzlc (fun g k => by rw [hzc, h])
    (fun A hA g hgA hgK => hzU A hA g hgA (MonoidHom.mem_ker.mp hgK))
    (fun v hvT => by
      obtain ⟨m, hm⟩ := hzD v hvT
      exact ⟨m, fun g hg => by rw [hm g hg, h]⟩)
  exact ⟨m, fun g => by rw [hm g, h]⟩

theorem UpperTheory.V.X.xvan :
    CorX → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), (∀ p ∈ D.T, p.Prime ∧ (D.pl p).valuation (p : Ω) < 1) → ∀ (d f n : ℕ) [NeZero (f * 2 ^ n)] (φ : DirichletCharacter c.O f) (ξ : DirichletCharacter c.O (2 ^ n)), XData l d φ ξ → ∀ γ : G ℚ Ω →* c.Oˣ, (∀ g, Raw.bar γ g = (redChar Ω (residue c.O) (prodX φ ξ) g : ResidueField c.O)) → D.XVan γ ∧ D.XVan γ⁻¹ := by
  intro hCor Ω _ _ _ l _ c D hT d f n _ φ ξ hX γ hγ
  haveI : CharP (ResidueField c.O) l := by
    obtain ⟨-, -, hloc, -⟩ := dvrFacts l c.O
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
    rw [← map_natCast (residue c.O), residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [← map_natCast (algebraMap ℤ_[l] c.O)] at hu
    exact PadicInt.p_nonunit (isUnit_of_map_unit (algebraMap ℤ_[l] c.O) _ hu)
  set γ' : G ℚ Ω →* (ResidueField c.O)ˣ := redChar Ω (residue c.O) (prodX φ ξ) with hγ'
  obtain ⟨hKn, hKi, -⟩ := spKer D
  have hv : ∀ γ'' : G ℚ Ω →* (ResidueField c.O)ˣ, (γ'' = γ' ∨ γ'' = γ'⁻¹) →
      Van D.T D.pl D.rbar.ker γ'' := by
    intro γ'' hor
    exact vanOf Ω l (ResidueField c.O) γ''
      (hCor Ω l c (ResidueField c.O) (residue c.O) d f n φ ξ hX γ'' hor) D.T D.pl D.rbar.ker hT hKn hKi
  refine ⟨xvan_of_van D γ γ' hγ (hv γ' (Or.inl rfl)), xvan_of_van D γ⁻¹ γ'⁻¹ ?_ (hv γ'⁻¹ (Or.inr rfl))⟩
  intro g
  have h1 := hγ g
  simp only [Raw.bar, MonoidHom.inv_apply] at h1 ⊢
  rw [map_units_inv, Units.val_inv_eq_inv_val, h1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.Xpp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.X

theorem UpperTheory.V.X.xpp :
    CorX → UnitaryThreeInertia.HostXpp := by
  intro hX Ω _ _ _ l hlp c N _ e ψ o₁ hD q hq S A F hF
  obtain ⟨d, f, n, _, φ, ξ, hx, hγ⟩ := dir Ω l c N e ψ o₁ hD q hq
  haveI : Finite (ResidueField c.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hlp.out).2 (by
    have h := (dvrFacts l c.O).2.2.1
    have h1 : (l : c.O) ∈ maximalIdeal c.O := by
      have : ¬ IsUnit (algebraMap ℤ_[l] c.O l) := fun h2 => PadicInt.irreducible_p.not_isUnit (h.map_nonunit _ h2)
      rw [map_natCast] at this
      exact this
    have := (residue_eq_zero_iff _).2 h1
    rwa [map_natCast] at this)
  set γ : G ℚ Ω →* (ResidueField c.O)ˣ := (redChar Ω (residue c.O) (prodX φ ξ))⁻¹ with hγd
  let κ : G ℚ Ω →* ℤˣ × (ResidueField c.O)ˣ := (F.η.prod F.Ψbar).comp F.π
  have hidx : ¬ l ∣ κ.ker.index := by
    rw [Subgroup.index_ker]
    intro h
    have h1 := h.trans (Subgroup.card_subgroup_dvd_card κ.range)
    rw [Nat.card_prod, Nat.card_units, Nat.card_eq_fintype_card, Fintype.card_units_int] at h1
    haveI := Fintype.ofFinite (ResidueField c.O)
    obtain ⟨r, -, hr⟩ := FiniteField.card (ResidueField c.O) l
    rcases hlp.out.dvd_mul.1 h1 with h2 | h2
    · exact hD.l_odd ((Nat.prime_dvd_prime_iff_eq hlp.out Nat.prime_two).1 h2)
    · rw [Nat.card_eq_fintype_card, hr] at h2
      have h3 : l ∣ l ^ (r : ℕ) := dvd_pow_self l r.ne_zero
      have h4 := Nat.dvd_sub h3 h2
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hlp.out.pos)] at h4
      exact hlp.out.one_lt.ne' (Nat.dvd_one.1 h4)
  have hπ : F.π = toGS Ω _ := hF.π
  let γ' : UnitaryThreeInertia.Gam Ω S → ResidueField c.O := fun g =>
    (((F.Ψbar g)⁻¹ : (ResidueField c.O)ˣ) : ResidueField c.O) ^ 2 * ((F.η g : ℤ) : ResidueField c.O)
  have hred : ∀ g, (redChar Ω (residue c.O) (prodX φ ξ) g : ResidueField c.O) =
      (F.Ψbar (F.π g) : ResidueField c.O) ^ 2 * ((F.η (F.π g) : ℤ) : ResidueField c.O) := fun g => by
    rw [hγ, ← hF.Ψ, ← hF.η]; rfl
  have hγ' : ∀ g, γ' (toGS Ω _ g) = γ g := fun g => by
    rw [← hπ, hγd, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, hred]
    simp only [γ', Units.val_inv_eq_inv_val, mul_inv, inv_pow]
    rcases Int.units_eq_one_or (F.η (F.π g)) with h | h <;> simp [h]
  have hK : κ.ker ≤ γ.ker := fun g hg => by
    have h1 : F.η (F.π g) = 1 := congrArg Prod.fst hg
    have h2 : F.Ψbar (F.π g) = 1 := congrArg Prod.snd hg
    refine Units.ext ?_
    rw [← hγ', ← hπ]
    simp [γ', h1, h2]
  have hl : (A F.vl).valuation (l : Ω) < 1 := by
    have h := (hF.isOver F.vl ((l : ℕ) : 𝓞 ℚ)).2 hF.vl
    simpa using h
  have hV := vanOf Ω l _ γ (hX Ω l c _ (residue c.O) d f n φ ξ hx γ (.inr rfl)) {l} (fun _ => A F.vl) κ.ker
    (by simpa using ⟨Fact.out, hl⟩) inferInstance hidx
  refine xppOf F γ' (fun g => by simp only [γ']; rw [mul_right_comm, ← mul_pow]; simp) fun z z1 z2 z3 z4 => ?_
  have hz : ∀ g h, z (toGS Ω _ (g * h)) = z (toGS Ω _ g) + (γ g : ResidueField c.O) * z (toGS Ω _ h) := fun g h => by
    rw [map_mul, z2, hγ']
  obtain ⟨m, hm⟩ := hV (fun g => z (toGS Ω _ g)) (z1.comp_continuous (continuous_toGS Ω _)) hz
    (unrOf Ω _ γ κ.ker hK _ {l} z hz fun v hv => by
      by_cases h : (⟨v, hv⟩ : S) = F.vl
      · exact .inl ⟨l, Finset.mem_singleton_self l, by have := hF.vl; rwa [← h] at this⟩
      · refine .inr ⟨A ⟨v, hv⟩, hF.isOver _, fun g hg hk => ?_⟩
        have hgD : g ∈ F.D ⟨v, hv⟩ := hF.D _ ▸ Ine_le_Dec _ hg
        have hgI : g ∈ F.I ⟨v, hv⟩ := hF.I _ ▸ hg
        rw [← hπ]
        exact z3 _ h ⟨g, hgD⟩ ⟨⟨hgI, congrArg Prod.fst hk⟩, congrArg Prod.snd hk⟩)
    (fun v _ => by
      obtain ⟨m, hm⟩ := z4
      refine ⟨m, fun g hg => ?_⟩
      have hgD : g ∈ F.D F.vl := hF.D _ ▸ hg
      rw [← hγ', ← hπ]
      exact hm ⟨g, hgD⟩)
  refine ⟨m, fun g => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  exact (hm g).trans (by rw [← hγ']; rfl)
end

