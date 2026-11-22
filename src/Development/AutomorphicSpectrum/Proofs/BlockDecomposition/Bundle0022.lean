import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableGenericFibreLocalization
section
namespace GlobalTheory.CompanionTheory.Semistable

open MvPolynomial

theorem smooth_away_core (O : Type) [CommRing O] (ϖ : O) (σ : Type) [Finite σ] [DecidableEq σ]
    (T : Finset σ) (i0 : σ) (hi0 : i0 ∈ T) (F : Type) [Field F] [Algebra O F]
    [IsLocalization.Away ϖ F] :
    (IsLocalization.Away.map F
      (Localization.Away (algebraMap O (MvPolynomial σ O ⧸
        Ideal.span {(∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ))
      (algebraMap O (MvPolynomial σ O ⧸
        Ideal.span {(∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ})) ϖ).Smooth := by
  classical
  let P := MvPolynomial σ O
  let I : Ideal P := Ideal.span {(∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ}
  let A := P ⧸ I
  let a : A := algebraMap O A ϖ
  let B := Localization.Away a
  let C := MvPolynomial {j : σ // j ≠ i0} O
  let y : σ → C := fun i => if hi : i = i0 then 0 else MvPolynomial.X ⟨i, hi⟩
  let g : C := ∏ i ∈ T.erase i0, y i
  let h : C := MvPolynomial.C ϖ * g
  let C' := Localization.Away h
  let u : C' := IsLocalization.Away.invSelf h
  have hu : algebraMap C C' h * u = 1 := IsLocalization.Away.mul_invSelf h
  have hh : IsUnit (algebraMap C C' h) := IsLocalization.Away.algebraMap_isUnit h
  have e1 : algebraMap C C' h = algebraMap O C' ϖ * algebraMap C C' g := by
    rw [IsScalarTower.algebraMap_apply O C C' ϖ, MvPolynomial.algebraMap_eq, ← map_mul]
  have hϖ' : IsUnit (algebraMap O C' ϖ) := by
    rw [e1] at hh
    exact isUnit_of_mul_isUnit_left hh
  let z : σ → C' := fun i => if i = i0 then algebraMap O C' ϖ ^ 2 * u else algebraMap C C' (y i)
  have hzg : ∏ i ∈ T.erase i0, z i = algebraMap C C' g := by
    rw [map_prod]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    simp only [z, if_neg (Finset.ne_of_mem_erase hi)]
  have hz : ∏ i ∈ T, z i = algebraMap O C' ϖ := by
    rw [← Finset.mul_prod_erase T z hi0, hzg]
    simp only [z, if_pos rfl]
    linear_combination (algebraMap O C' ϖ) * hu - (algebraMap O C' ϖ * u) * e1
  let ψP : P →ₐ[O] C' := MvPolynomial.aeval z
  have hψP : ∀ x ∈ I, ψP x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    have h3 : ∀ i, ψP (MvPolynomial.X i) = z i := fun i => MvPolynomial.aeval_X z i
    have h4 : ψP (MvPolynomial.C ϖ) = algebraMap O C' ϖ := MvPolynomial.aeval_C z ϖ
    have h5 : ψP ((∏ i ∈ T, MvPolynomial.X i) - MvPolynomial.C ϖ) = 0 := by
      rw [map_sub, map_prod, h4]
      simp only [h3, hz, sub_self]
    rw [map_mul, h5, mul_zero]
  let ψA : A →ₐ[O] C' := Ideal.Quotient.liftₐ I ψP hψP
  have hψA : ∀ p : P, ψA (Ideal.Quotient.mk I p) = ψP p := fun p => rfl
  have hunit1 : ∀ yy : Submonoid.powers a, IsUnit (ψA yy) := by
    rintro ⟨_, n, rfl⟩
    show IsUnit (ψA (algebraMap O A ϖ ^ n))
    rw [map_pow, AlgHom.commutes]
    exact hϖ'.pow n
  let ψ : B →ₐ[O] C' := IsLocalization.liftAlgHom (M := Submonoid.powers a) (S := B) (f := ψA) hunit1
  have hψ : ∀ x : A, ψ (algebraMap A B x) = ψA x := fun x => by
    first
    | exact IsLocalization.lift_eq (M := Submonoid.powers a) (S := B) _ x
    | simp [ψ, IsLocalization.liftAlgHom]
  let xB : σ → B := fun i => algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i))
  have hxB : ∏ i ∈ T, xB i = algebraMap O B ϖ := by
    have e : (Ideal.Quotient.mk I (∏ i ∈ T, MvPolynomial.X i)) =
        Ideal.Quotient.mk I (MvPolynomial.C ϖ) :=
      Ideal.Quotient.eq.mpr (Ideal.subset_span rfl)
    simp only [xB]
    rw [← map_prod, ← map_prod, e, IsScalarTower.algebraMap_apply O A B]
    rfl
  have hϖB : IsUnit (algebraMap O B ϖ) := by
    rw [IsScalarTower.algebraMap_apply O A B]
    exact IsLocalization.Away.algebraMap_isUnit a
  have hxB' : xB i0 * ∏ i ∈ T.erase i0, xB i = algebraMap O B ϖ := by
    rw [Finset.mul_prod_erase T xB hi0, hxB]
  have hpB : IsUnit (∏ i ∈ T.erase i0, xB i) := by
    rw [← hxB'] at hϖB
    exact isUnit_of_mul_isUnit_right hϖB
  let χC : C →ₐ[O] B := MvPolynomial.aeval (fun j => xB j.1)
  have hχX : ∀ j : {j : σ // j ≠ i0}, χC (MvPolynomial.X j) = xB j.1 := fun j =>
    MvPolynomial.aeval_X (fun j : {j : σ // j ≠ i0} => xB j.1) j
  have hχy : ∀ i ∈ T.erase i0, χC (y i) = xB i := by
    intro i hi
    have hne : i ≠ i0 := Finset.ne_of_mem_erase hi
    have hyi : y i = MvPolynomial.X ⟨i, hne⟩ := dif_neg hne
    rw [hyi, hχX ⟨i, hne⟩]
  have hχh : χC h = algebraMap O B ϖ * ∏ i ∈ T.erase i0, xB i := by
    show χC (MvPolynomial.C ϖ * ∏ i ∈ T.erase i0, y i) = _
    rw [map_mul, map_prod]
    have hC : χC (MvPolynomial.C ϖ) = algebraMap O B ϖ := MvPolynomial.aeval_C _ ϖ
    rw [hC, Finset.prod_congr rfl hχy]
  have hunit2 : ∀ yy : Submonoid.powers h, IsUnit (χC yy) := by
    rintro ⟨_, n, rfl⟩
    show IsUnit (χC (h ^ n))
    rw [map_pow, hχh]
    exact (hϖB.mul hpB).pow n
  let χ : C' →ₐ[O] B := IsLocalization.liftAlgHom (M := Submonoid.powers h) (S := C') (f := χC) hunit2
  have hχ : ∀ x : C, χ (algebraMap C C' x) = χC x := fun x => by
    first
    | exact IsLocalization.lift_eq (M := Submonoid.powers h) (S := C') _ x
    | simp [χ, IsLocalization.liftAlgHom]
  have hχu : χ (algebraMap C C' h) * χ u = 1 := by rw [← map_mul, hu, map_one]
  rw [hχ, hχh] at hχu
  have h1 : χ.comp ψ = AlgHom.id O B := by
    apply IsLocalization.algHom_ext (Submonoid.powers a)
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    show χ (ψ (algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i)))) =
      algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i))
    rw [hψ, hψA]
    have hXi : ψP (MvPolynomial.X i) = z i := MvPolynomial.aeval_X z i
    rw [hXi]
    show χ (z i) = xB i
    by_cases hi : i = i0
    · rw [hi]
      have hz0 : z i0 = algebraMap O C' ϖ ^ 2 * u := if_pos rfl
      rw [hz0, map_mul, map_pow, AlgHom.commutes]
      linear_combination (χ u * algebraMap O B ϖ) * hxB'.symm + xB i0 * hχu
    · have hzi : z i = algebraMap C C' (y i) := if_neg hi
      have hyi : y i = MvPolynomial.X ⟨i, hi⟩ := dif_neg hi
      rw [hzi, hχ, hyi, hχX ⟨i, hi⟩]
  have h2 : ψ.comp χ = AlgHom.id O C' := by
    apply IsLocalization.algHom_ext (Submonoid.powers h)
    apply MvPolynomial.algHom_ext
    intro j
    show ψ (χ (algebraMap C C' (MvPolynomial.X j))) = algebraMap C C' (MvPolynomial.X j)
    rw [hχ]
    rw [hχX j]
    show ψ (algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X j.1))) = _
    rw [hψ, hψA]
    have hXi : ψP (MvPolynomial.X j.1) = z j.1 := MvPolynomial.aeval_X z j.1
    have hzi : z j.1 = algebraMap C C' (y j.1) := if_neg j.2
    have hyi : y j.1 = MvPolynomial.X ⟨j.1, j.2⟩ := dif_neg j.2
    rw [hXi, hzi, hyi]
  let e : C' ≃ₐ[O] B := AlgEquiv.ofAlgHom χ ψ h1 h2
  haveI : Algebra.FormallySmooth C C' := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers h)
  haveI : Algebra.FormallySmooth O C' := Algebra.FormallySmooth.comp O C C'
  haveI : Algebra.FormallySmooth O B := Algebra.FormallySmooth.of_equiv e
  haveI : Algebra.FinitePresentation O A :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton _)
  haveI : Algebra.FinitePresentation A B := IsLocalization.Away.finitePresentation a
  haveI : Algebra.FinitePresentation O B := Algebra.FinitePresentation.trans O A B
  haveI : Algebra.FinitePresentation O F := IsLocalization.Away.finitePresentation ϖ
  let φ := IsLocalization.Away.map F B (algebraMap O A) ϖ
  letI : Algebra F B := φ.toAlgebra
  haveI : IsScalarTower O F B := IsScalarTower.of_algebraMap_eq (fun x => by
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply O A B]
    exact (IsLocalization.map_eq _ _).symm)
  haveI : Algebra.FormallySmooth F B := Algebra.FormallySmooth.localization_base (Submonoid.powers ϖ)
  haveI : Algebra.FinitePresentation F B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation O F B
  have hs : Algebra.Smooth F B := ⟨inferInstance, inferInstance⟩
  exact hs

theorem smooth_generic_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m → ∀ (F : Type) [Field F] [Algebra O F] [IsLocalization.Away ϖ F], (IsLocalization.Away.map F (Localization.Away (algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ)) (algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ})) ϖ).Smooth := by
  intro O _ _ _ ϖ _ m r hr1 hrm F _ _ _
  exact smooth_away_core O ϖ (Fin m) (Finset.univ.filter (fun i : Fin m => (i : ℕ) < r)) ⟨0, by omega⟩
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, show (0 : ℕ) < r by omega⟩) F

end GlobalTheory.CompanionTheory.Semistable
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableModelRingIsDomain
section
namespace GlobalTheory.CompanionTheory.SemistableLocal

open MvPolynomial in

theorem irreducible_prod_X_sub_C (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ) (m' r : ℕ) (hr : 1 ≤ r) :
    Irreducible ((∏ i ∈ Finset.univ.filter (fun i : Fin (m' + 1) => (i : ℕ) < r), X i) - C ϖ :
      MvPolynomial (Fin (m' + 1)) O) := by
  set g : MvPolynomial (Fin m') O :=
    ∏ j ∈ Finset.univ.filter (fun j : Fin m' => (j : ℕ) + 1 < r), MvPolynomial.X j with hgdef
  have hprod : (∏ i ∈ Finset.univ.filter (fun i : Fin (m' + 1) => (i : ℕ) < r),
      (MvPolynomial.X i : MvPolynomial (Fin (m' + 1)) O))
      = MvPolynomial.X 0 * ∏ j ∈ Finset.univ.filter (fun j : Fin m' => (j : ℕ) + 1 < r),
          (MvPolynomial.X (Fin.succ j) : MvPolynomial (Fin (m' + 1)) O) := by
    rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]
    have h0 : 0 < r := by omega
    simp [Fin.val_succ, h0]
  have hC : MvPolynomial.finSuccEquiv O m' (MvPolynomial.C ϖ) =
      Polynomial.C (MvPolynomial.C ϖ) := by
    have h := (MvPolynomial.finSuccEquiv O m').commutes ϖ
    rw [MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq] at h
    exact h
  have hϖ0 : (MvPolynomial.C ϖ : MvPolynomial (Fin m') O) ≠ 0 := by
    rw [Ne, MvPolynomial.C_eq_zero]; exact hϖ.ne_zero
  have hg0 : g ≠ 0 := by
    intro h
    have h1 := congrArg (MvPolynomial.eval (fun _ : Fin m' => (1 : O))) h
    simp [hgdef] at h1
  have hcop : ∀ a : MvPolynomial (Fin m') O, a ∣ g → a ∣ MvPolynomial.C ϖ → IsUnit a := by
    intro a hag hac
    obtain ⟨s, hs⟩ := hac
    have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hs; exact hϖ0 hs
    have hs0 : s ≠ 0 := by rintro rfl; rw [mul_zero] at hs; exact hϖ0 hs
    have hdeg := MvPolynomial.totalDegree_mul_of_isDomain ha0 hs0
    rw [← hs, MvPolynomial.totalDegree_C] at hdeg
    have hda : a.totalDegree = 0 := by omega
    rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at hda
    rw [hda] at hag ⊢
    refine IsUnit.map MvPolynomial.C (isUnit_of_dvd_one ?_)
    have h1 := map_dvd (MvPolynomial.eval (fun _ : Fin m' => (1 : O))) hag
    simpa [hgdef] using h1
  have hirr : Irreducible (Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) :
      Polynomial (MvPolynomial (Fin m') O)) := by
    have hdeg : (Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) :
        Polynomial (MvPolynomial (Fin m') O)).natDegree = 1 := Polynomial.natDegree_linear hg0
    have key2 : ∀ c d : Polynomial (MvPolynomial (Fin m') O),
        Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) = c * d →
          c.natDegree = 0 → IsUnit c := by
      intro c d hcd hc
      have hc' := Polynomial.eq_C_of_natDegree_eq_zero hc
      have hdvd : Polynomial.C (c.coeff 0) ∣
          Polynomial.C g * Polynomial.X + Polynomial.C (-MvPolynomial.C ϖ) := by
        rw [← hc']; exact ⟨d, hcd⟩
      rw [Polynomial.C_dvd_iff_dvd_coeff] at hdvd
      rw [hc']
      refine IsUnit.map Polynomial.C (hcop _ ?_ ?_)
      · simpa [Polynomial.coeff_C_mul_X, Polynomial.coeff_C] using hdvd 1
      · simpa [Polynomial.coeff_C_mul_X, Polynomial.coeff_C] using hdvd 0
    refine irreducible_iff.mpr ⟨?_, ?_⟩
    · intro hu
      have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      omega
    · intro a b hab
      have ha0 : a ≠ 0 := by
        rintro rfl; rw [zero_mul] at hab; rw [hab] at hdeg; simp at hdeg
      have hb0 : b ≠ 0 := by
        rintro rfl; rw [mul_zero] at hab; rw [hab] at hdeg; simp at hdeg
      have hsum := Polynomial.natDegree_mul ha0 hb0
      rw [← hab, hdeg] at hsum
      rcases Nat.eq_zero_or_pos a.natDegree with h | h
      · exact Or.inl (key2 a b hab h)
      · exact Or.inr (key2 b a (by rw [hab, mul_comm]) (by omega))
  refine (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv O m')).mp ?_
  rw [hprod, map_sub, map_mul, map_prod, MvPolynomial.finSuccEquiv_X_zero, hC]
  simp only [MvPolynomial.finSuccEquiv_X_succ]
  convert hirr using 1
  rw [hgdef, map_prod, map_neg]
  ring

theorem isDomain_quotient_prod_X_sub_C :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
      ∀ (m r : ℕ), 1 ≤ r → r ≤ m →
        IsDomain (MvPolynomial (Fin m) O ⧸ Ideal.span
          {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
            MvPolynomial.C ϖ}) := by
  intro O _ _ _ ϖ hϖ m r hr hrm
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hirr := irreducible_prod_X_sub_C O ϖ hϖ m' r hr
  haveI : UniqueFactorizationMonoid (MvPolynomial (Fin (m' + 1)) O) :=
    MvPolynomial.uniqueFactorizationMonoid _
  have hp := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  haveI := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  exact Ideal.Quotient.isDomain _

end GlobalTheory.CompanionTheory.SemistableLocal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SemistableSpecialFibreProperty
section
namespace GlobalTheory.CompanionTheory.SemistableSpecial

open MvPolynomial

theorem isRadical_prod_X {k σ : Type} [CommRing k] [IsDomain k] [UniqueFactorizationMonoid k]
    (s : Finset σ) : IsRadical (∏ i ∈ s, (X i : MvPolynomial σ k)) := by
  classical
  have key : ∀ (t : Finset σ) (y : MvPolynomial σ k),
      (∀ i ∈ t, (X i : MvPolynomial σ k) ∣ y) → (∏ i ∈ t, (X i : MvPolynomial σ k)) ∣ y := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro y _; simp
    | @insert a t ha ih =>
      intro y hy
      obtain ⟨z, rfl⟩ := hy a (Finset.mem_insert_self a t)
      rw [Finset.prod_insert ha]
      refine mul_dvd_mul_left _ (ih z ?_)
      intro i hi
      have hXi : Prime (X i : MvPolynomial σ k) := MvPolynomial.X_prime
      rcases hXi.dvd_or_dvd (hy i (Finset.mem_insert_of_mem hi)) with h | h
      · exfalso
        rw [MvPolynomial.X_dvd_X] at h
        exact ha (h ▸ hi)
      · exact h
  intro n y hy
  apply key
  intro i hi
  have hXi : Prime (X i : MvPolynomial σ k) := MvPolynomial.X_prime
  exact hXi.dvd_of_dvd_pow
    (dvd_trans (Finset.dvd_prod_of_mem (fun j => (X j : MvPolynomial σ k)) hi) hy)

theorem isRadical_span_sup {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {σ : Type} (s : Finset σ) :
    (Ideal.span {(∏ i ∈ s, (X i : MvPolynomial σ O)) - C ϖ} ⊔
      Ideal.span {(C ϖ : MvPolynomial σ O)}).IsRadical := by
  classical
  set P : MvPolynomial σ O := ∏ i ∈ s, X i with hP
  set φ : MvPolynomial σ O →+* MvPolynomial σ (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφ
  have hker : RingHom.ker φ = Ideal.span {C ϖ} := by
    rw [hφ, MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hφP : φ P = ∏ i ∈ s, (X i : MvPolynomial σ (IsLocalRing.ResidueField O)) := by
    rw [hP, hφ, map_prod]
    simp only [MvPolynomial.map_X]
  have hCϖ : φ (C ϖ) = 0 := by
    rw [← RingHom.mem_ker, hker]
    exact Ideal.mem_span_singleton_self _
  have hPmem : P ∈ Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)} := by
    have h := Ideal.add_mem (Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)})
      (Ideal.mem_sup_left (Ideal.mem_span_singleton_self (P - C ϖ)))
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self (C ϖ : MvPolynomial σ O)))
    rwa [sub_add_cancel] at h
  have hmem : ∀ x, x ∈ Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)} ↔
      φ P ∣ φ x := by
    intro x
    constructor
    · intro hx
      have hle : Ideal.span {P - C ϖ} ⊔ Ideal.span {(C ϖ : MvPolynomial σ O)} ≤
          Ideal.comap φ (Ideal.span {φ P}) := by
        refine sup_le ?_ ?_
        · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
            map_sub, hCϖ, sub_zero]
          exact Ideal.mem_span_singleton_self _
        · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hCϖ]
          exact Ideal.zero_mem _
      exact Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp (hle hx))
    · rintro ⟨g, hg⟩
      obtain ⟨g', rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective g
      have hdiff : x - P * g' ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, map_sub, map_mul, hg, hφ]
        exact sub_self _
      rw [hker] at hdiff
      have hx : x = (x - P * g') + P * g' := by ring
      rw [hx]
      exact Ideal.add_mem _ (Ideal.mem_sup_right hdiff) (Ideal.mul_mem_right _ _ hPmem)
  unfold Ideal.IsRadical
  intro x hx
  rw [Ideal.mem_radical_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [hmem] at hn
  rw [hmem]
  rw [map_pow, hφP] at hn
  rw [hφP]
  exact isRadical_prod_X s n (φ x) hn

theorem special_fibre_isReduced : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O), Irreducible ϖ → ∀ (m r : ℕ), 1 ≤ r → r ≤ m →
    IsReduced ((MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ⧸ Ideal.span {algebraMap O (MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ}) ϖ}) := by
  intro O _ _ _ ϖ hϖ m r _ _
  set J : Ideal (MvPolynomial (Fin m) O) := Ideal.span {(∏ i ∈ Finset.univ.filter
    (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) - MvPolynomial.C ϖ} with hJ
  have e : Ideal.span {algebraMap O (MvPolynomial (Fin m) O ⧸ J) ϖ} =
      Ideal.map (Ideal.Quotient.mk J) (Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin m) O)}) := by
    rw [Ideal.map_span, Set.image_singleton, ← Ideal.Quotient.mk_algebraMap,
      MvPolynomial.algebraMap_eq]
  rw [e]
  have : IsReduced (MvPolynomial (Fin m) O ⧸
      (J ⊔ Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin m) O)})) := by
    rw [← Ideal.isRadical_iff_quotient_reduced]
    exact isRadical_span_sup hϖ (Finset.univ.filter (fun i : Fin m => (i : ℕ) < r))
  exact isReduced_of_injective
    (DoubleQuot.quotQuotEquivQuotSup J (Ideal.span {(MvPolynomial.C ϖ : MvPolynomial (Fin m) O)}))
    (RingEquiv.injective _)

end GlobalTheory.CompanionTheory.SemistableSpecial
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SesquilinearEqZeroOfDiagZero
section
open Matrix

namespace GlobalTheory.CompanionTheory.Sesquilinear

theorem eq_zero_of_diag_eq_zero {V : Type} [AddCommGroup V] [Module ℂ V]
    (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (h : ∀ v, B v v = 0) : B = 0 := by
  ext v w
  have h1 := h (v + w)
  have h2 := h (v + Complex.I • w)
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    h v, h w, smul_eq_mul, zero_add, add_zero, Complex.conj_I, RingHom.id_apply,
    mul_zero] at h1 h2
  have h3 : B v w = B w v := by
    have : Complex.I * (B w v - B v w) = 0 := by linear_combination h2
    rcases mul_eq_zero.mp this with h4 | h4
    · exact absurd h4 Complex.I_ne_zero
    · exact (sub_eq_zero.mp h4).symm
  have h5 : (2 : ℂ) * B v w = 0 := by linear_combination h1 + h3
  simpa using h5

end GlobalTheory.CompanionTheory.Sesquilinear
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitHomeoApply
section
open MeasureTheory Topology
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SplitExtLat

variable {P G₁ : Type} [Group P] [Group G₁]

def splitMap (ι : G₁ →* P) (π : P →* G₁) : π.ker × G₁ → P := fun z => (z.1 : P) * ι z.2

def kerPart (ι : G₁ →* P) (π : P →* G₁) (h : ∀ u, π (ι u) = u) (p : P) : π.ker :=
  ⟨p * (ι (π p))⁻¹, by simp [MonoidHom.mem_ker, h]⟩

def splitEquiv (ι : G₁ →* P) (π : P →* G₁) (h : ∀ u, π (ι u) = u) : π.ker × G₁ ≃ P where
  toFun := splitMap ι π
  invFun p := (kerPart ι π h p, π p)
  left_inv z := by
    obtain ⟨⟨m, hm⟩, u⟩ := z
    have hm' : π m = 1 := hm
    ext <;> simp [splitMap, kerPart, hm', h]
  right_inv p := by simp [splitMap, kerPart]

def splitHomeo [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (h : ∀ u, π (ι u) = u) : π.ker × G₁ ≃ₜ P where
  toEquiv := splitEquiv ι π h
  continuous_toFun := by
    change Continuous fun z : π.ker × G₁ => (z.1 : P) * ι z.2
    fun_prop
  continuous_invFun := by
    change Continuous fun p => (kerPart ι π h p, π p)
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hπ
    fun_prop

@[simp] theorem splitHomeo_apply [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (h : ∀ u, π (ι u) = u) (z : π.ker × G₁) :
    splitHomeo ι π hι hπ h z = (z.1 : P) * ι z.2 := rfl

theorem mul_split (ι : G₁ →* P) (π : P →* G₁) (h : ∀ u, π (ι u) = u) (g : P) (m : π.ker) (u : G₁) :
    g * ((m : P) * ι u) =
      ((kerPart ι π h g * MulAut.conjNormal (ι (π g)) m : π.ker) : P) * ι (π g * u) := by
  simp only [kerPart, Subgroup.coe_mul, MulAut.conjNormal_apply, map_mul]
  group

theorem continuous_conj [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) :
    Continuous fun z : G₁ × π.ker => MulAut.conjNormal (ι z.1) z.2 := by
  refine Continuous.subtype_mk (f := fun z : G₁ × π.ker => ι z.1 * (z.2 : P) * (ι z.1)⁻¹) ?_ _
  fun_prop

end GlobalTheory.CompanionTheory.SplitExtLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictAntiOfTwoExceptions
section
namespace GlobalTheory.CompanionTheory.Segments

theorem shufcomb (l : ℕ) (hl : 3 ≤ l) (w : Fin l → ℕ) (hw : ∀ a, w a < l) (i j : Fin l)
    (hi : w i = 0) (hj : w j = l - 1)
    (h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a)
    (h2 : ∀ a b, a < b → a ≠ j → b ≠ j → w b < w a) : StrictAnti w := by
  have hij : i ≠ j := by
    intro h
    rw [h] at hi
    omega
  intro a b hab
  by_cases hbi : b = i
  · by_cases haj : a = j
    · rw [hbi, haj, hi, hj]
      omega
    · exact h2 a b hab haj (by rw [hbi]; exact hij)
  · by_cases hai : a = i
    · by_cases hbj : b = j
      · exfalso
        have hij' : i < j := by
          rw [← hai, ← hbj]
          exact hab
        obtain ⟨c, hci, hcj⟩ : ∃ c : Fin l, c ≠ i ∧ c ≠ j := by
          by_contra hc
          push_neg at hc
          have key : ∀ k : ℕ, ∀ hk : k < l, k = i.val ∨ k = j.val := by
            intro k hk
            by_cases h : (⟨k, hk⟩ : Fin l) = i
            · left
              exact congrArg Fin.val h
            · right
              exact congrArg Fin.val (hc ⟨k, hk⟩ h)
          have k0 := key 0 (by omega)
          have k1 := key 1 (by omega)
          have k2 := key 2 (by omega)
          omega
        rcases lt_or_gt_of_ne hci with hc | hc
        · have h3 := h1 c j (lt_trans hc hij') hci (Ne.symm hij)
          have h4 := hw c
          omega
        · have h3 := h2 i c hc hij hcj
          omega
      · exact h2 a b hab (by rw [hai]; exact hij) hbj
    · exact h1 a b hab hai hbi

end GlobalTheory.CompanionTheory.Segments
end

