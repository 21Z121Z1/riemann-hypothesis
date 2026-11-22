import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeActionAdelicLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsRationalEquivOfIsPlace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim
open UpperTheory.Gal.W2

private theorem exists_lattice_basis_of_rational {M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module.Free ℤ M] [Module.Finite ℤ M] [Module.Free ℤ N] [Module.Finite ℤ N]
    (j : N →+ ℚ ⊗[ℤ] M) (hj : Function.Injective j)
    (hs : ∀ w, ∃ (m : ℕ) (u : N), m ≠ 0 ∧ m • w = j u) :
    ∃ (ψ : N ≃+ M) (T : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] M)), ∀ u, T ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = j u := by
  classical
  let jL : N →ₗ[ℤ] ℚ ⊗[ℤ] M := j.toIntLinearMap
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) jL := by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      rw [Module.End.isUnit_iff]
      have hx : ((x : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr (nonZeroDivisors.ne_zero x.2)
      have hsm : ∀ v : ℚ ⊗[ℤ] M,
          (algebraMap ℤ (Module.End ℤ (ℚ ⊗[ℤ] M)) x) v = ((x : ℤ) : ℚ) • v := by
        intro v
        rw [Module.algebraMap_end_apply, Int.cast_smul_eq_zsmul]
      refine ⟨fun v w h => ?_, fun v => ⟨((x : ℤ) : ℚ)⁻¹ • v, ?_⟩⟩
      · rw [hsm, hsm] at h
        exact smul_right_injective _ hx h
      · rw [hsm, smul_smul, mul_inv_cancel₀ hx, one_smul]
    · intro w
      obtain ⟨m, u, hm, h⟩ := hs w
      refine ⟨⟨u, ⟨(m : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hm)⟩⟩, ?_⟩
      show (m : ℤ) • w = j u
      rw [natCast_zsmul]
      exact h
    · intro x1 x2 h
      exact ⟨1, by rw [one_smul, one_smul]; exact hj h⟩
  have hb : IsBaseChange ℚ jL := IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ jL
  have hrank : Module.finrank ℤ N = Module.finrank ℤ M := by
    rw [← Module.finrank_of_isLocalizedModule_of_free ℚ (nonZeroDivisors ℤ) jL,
      Module.finrank_baseChange]
  let e : N ≃ₗ[ℤ] M := LinearEquiv.ofFinrankEq N M hrank
  refine ⟨e.toAddEquiv, (LinearEquiv.baseChange ℤ ℚ N M e).symm.trans hb.equiv, fun u => ?_⟩
  have h1 : (LinearEquiv.baseChange ℤ ℚ N M e).symm ((1 : ℚ) ⊗ₜ[ℤ] e u) = (1 : ℚ) ⊗ₜ[ℤ] u := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  show hb.equiv ((LinearEquiv.baseChange ℤ ℚ N M e).symm ((1 : ℚ) ⊗ₜ[ℤ] e u)) = j u
  rw [h1, hb.equiv_tmul, one_smul]
  rfl

theorem UpperTheory.exists_rational_equiv_of_isPlace :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {β : G.Cˣ} {D' : PLat D.O D.inv} {j : D'.La →+ VQ D}, IsPlace L β D' j →
        ∃ (ψ : D'.La ≃+ D.La) (T : VQ D ≃ₗ[ℚ] VQ D), ∀ u, T ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = j u := by
  intro p _ D G L β D' j h
  haveI := D.freeLa
  haveI := D.finLa
  exact exists_lattice_basis_of_rational j h.1 h.2.2.1
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsUnitTrivOfSimilitudeFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

private theorem trivCore {A S : Type} [CommRing A] [Ring S] [Algebra A S] (σ : S → S)
    (hm : ∀ a b, σ (a * b) = σ b * σ a) (hs : ∀ x, σ (σ x) = x)
    (ha : ∀ r, σ (algebraMap A S r) = algebraMap A S r)
    (B b y y' : S) (hBb : B * b = 1) (h₁ : y' * y = 1) (h₂ : y * y' = 1) (u t : A) (hut : t * u = 1)
    (h : σ (B * y) * y = algebraMap A S u) : y' * b * σ y' = algebraMap A S t := by
  have s1 : σ 1 = 1 := by
    have h0 := ha 1
    rwa [map_one] at h0
  have hσ : σ y' * σ y = 1 := by rw [← hm, h₂, s1]
  have hσ' : σ y * σ y' = 1 := by rw [← hm, h₁, s1]
  have hU : σ y * B * y = algebraMap A S u := by
    have h3 := congrArg σ h
    rw [hm, hs, ha] at h3
    rw [_root_.mul_assoc]
    exact h3
  have hB : B = σ y' * algebraMap A S u * y' := by
    rw [← hU]
    calc B = (σ y' * σ y) * B * (y * y') := by rw [hσ, h₂, _root_.one_mul, _root_.mul_one]
      _ = σ y' * (σ y * B * y) * y' := by simp only [_root_.mul_assoc]
  have e1 : algebraMap A S u * (σ y' * y' * b) = 1 := by
    rw [← hBb, hB, (Algebra.commutes u (σ y')).symm]
    simp only [_root_.mul_assoc]
  have hX : σ y' * y' * b = algebraMap A S t := by
    calc σ y' * y' * b = (algebraMap A S t * algebraMap A S u) * (σ y' * y' * b) := by
          rw [← map_mul, hut, map_one, _root_.one_mul]
      _ = algebraMap A S t := by rw [_root_.mul_assoc, e1, _root_.mul_one]
  calc y' * b * σ y' = (σ y * σ y') * y' * b * σ y' := by rw [hσ', _root_.one_mul]
    _ = σ y * (σ y' * y' * b) * σ y' := by simp only [_root_.mul_assoc]
    _ = σ y * algebraMap A S t * σ y' := by rw [hX]
    _ = algebraMap A S t * (σ y * σ y') := by rw [← Algebra.commutes, _root_.mul_assoc]
    _ = algebraMap A S t := by rw [hσ', _root_.mul_one]

private theorem starT_invol {p : ℕ} [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R]
    (x : R ⊗[ℚ] G.C) : (starT G.star R (starT G.star R x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, MulOpposite.unop_add, ha, hb]
  | tmul r c => rw [starT_tmul, starT_tmul, G.star_star]

private theorem starT_alg {p : ℕ} [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R]
    (r : R) : (starT G.star R (algebraMap R (R ⊗[ℚ] G.C) r)).unop = algebraMap R (R ⊗[ℚ] G.C) r := by
  rw [Algebra.TensorProduct.algebraMap_apply, starT_tmul, map_one, MulOpposite.unop_one]

theorem UpperTheory.exists_unit_triv_of_similitude_factor :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y y' : AfP p ⊗[ℚ] G.C) (h₁ : y' * y = 1) (h₂ : y * y' = 1) (s : ℚ),
        0 < s → ∀ (c : (AfP p)ˣ),
        (∀ v w, algebraMap ℚ (AfP p) s * formAf D (actOn L.rep (AfP p) (inC G (AfP p) ((β⁻¹ : G.Cˣ) : G.C))
          (actOn L.rep (AfP p) y v)) (actOn L.rep (AfP p) y w) = (2 * (c : AfP p)) * formAf D v w) →
        ∃ t : (AfP p)ˣ, Triv G (AfP p) β ⟨y', y, h₁, h₂⟩ t := by
  intro p _ D G L β y y' h₁ h₂ s hs0 c hyp
  have hs : s ≠ 0 := ne_of_gt hs0
  set Bi := inC G (AfP p) ((β⁻¹ : G.Cˣ) : G.C) with hBi
  set b := inC G (AfP p) (β : G.C) with hb
  have hBb : Bi * b = 1 := by
    rw [hBi, hb, ← map_mul, Units.inv_mul, map_one]
  let u : AfP p := algebraMap ℚ (AfP p) (2 * s⁻¹) * (c : AfP p)
  let t : AfP p := algebraMap ℚ (AfP p) (s / 2) * ((c⁻¹ : (AfP p)ˣ) : AfP p)
  have hut : t * u = 1 := by
    have hq : s / 2 * (2 * s⁻¹) = 1 := by field_simp
    calc t * u = algebraMap ℚ (AfP p) (s / 2 * (2 * s⁻¹)) * (((c⁻¹ : (AfP p)ˣ) : AfP p) * c) := by
          simp only [t, u, map_mul]
          ring
      _ = 1 := by rw [hq, map_one, Units.inv_mul, _root_.one_mul]
  have htu : u * t = 1 := by rw [_root_.mul_comm]; exact hut
  let σ : AfP p ⊗[ℚ] G.C → AfP p ⊗[ℚ] G.C := fun x => (starT G.star (AfP p) x).unop
  have hkey : σ (Bi * y) * y = algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) u := by
    apply GlobalTheory.AdelicSim.inj L
    apply LinearMap.ext
    intro w
    rw [AlgHom.commutes, Module.algebraMap_end_apply, ← sub_eq_zero]
    apply nondeg D
    intro v
    rw [map_sub, map_smul, smul_eq_mul, map_mul, Module.End.mul_apply]
    simp only [σ]
    rw [← adjAf L, map_mul, Module.End.mul_apply]
    have hsinv : algebraMap ℚ (AfP p) s⁻¹ * algebraMap ℚ (AfP p) s = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hs, map_one]
    calc _ = algebraMap ℚ (AfP p) s⁻¹ * (algebraMap ℚ (AfP p) s *
            formAf D (actOn L.rep (AfP p) Bi (actOn L.rep (AfP p) y v)) (actOn L.rep (AfP p) y w))
            - u * formAf D v w := by
          rw [← _root_.mul_assoc, hsinv, _root_.one_mul]
      _ = 0 := by
          rw [hyp v w]
          simp only [u]
          rw [map_mul, map_ofNat]
          ring
  refine ⟨⟨t, u, hut, htu⟩, ?_⟩
  exact trivCore σ (fun a a' => by simp only [σ]; rw [map_mul, MulOpposite.unop_mul])
    (starT_invol G (AfP p)) (starT_alg G (AfP p)) Bi b y y' hBb h₁ h₂ u t hut hkey
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.FormScalarOfAdelicEndoPreservingLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

private theorem formIntegral {p : ℕ} [Fact p.Prime] {D : Datum p}
    (F : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D)) (e : D.La → D.La → ℤ)
    (hF : ∀ x y, F (inAf D x) (inAf D y) = (e x y : AfP p))
    {v w : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) (hw : w ∈ LaHat D) : IsIntAf (F v w) := by
  have ez : ∀ (a : AfP p) (x : D.La), a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x : VQ D) = a • inAf D x := by
    intro a x
    rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have hgen : ∀ (a : AfP p) (x : D.La), IsIntAf a → ∀ w ∈ LaHat D, IsIntAf (F (a • inAf D x) w) := by
    intro a x ha w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw' =>
      obtain ⟨a', y, ha', rfl⟩ := hw'
      rw [ez, map_smul, map_smul, LinearMap.smul_apply, hF, smul_eq_mul, smul_eq_mul]
      exact isInt_mul ha' (isInt_mul ha (isInt_intCast _))
    | zero => rw [map_zero]; exact isIntAf_zero
    | add w₁ w₂ _ _ h₁ h₂ => rw [map_add]; exact isIntAf_add h₁ h₂
    | neg w _ h => rw [map_neg]; exact isIntAf_neg h
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    rw [ez]
    exact hgen a x ha w hw
  | zero => rw [map_zero, LinearMap.zero_apply]; exact isIntAf_zero
  | add v₁ v₂ _ _ h₁ h₂ => rw [map_add, LinearMap.add_apply]; exact isIntAf_add h₁ h₂
  | neg v _ h => rw [map_neg, LinearMap.neg_apply]; exact isIntAf_neg h

theorem UpperTheory.form_scalar_of_adelic_endo_preserving_lattice :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} (F : LinearMap.BilinForm (AfP p) (AfP p ⊗[ℚ] VQ D)) (e : D.La → D.La → ℤ),
        (∀ x y, F (inAf D x) (inAf D y) = (e x y : AfP p)) →
        ∀ (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, A v ∈ LaHat D) → ∀ (gs : ℕ → D.La →+ D.La),
        (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, A (inAf D x) = inAf D (gs n x) + n • w) →
        ∀ (nu : ℕ → ℤ) (c : AfP p), (∀ n : ℕ, 0 < n → n.Coprime p → ∃ b : AfP p, IsIntAf b ∧ c = (nu n : AfP p) + n • b) →
        (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y, (n : ℤ) ∣ e (gs n x) (gs n y) - nu n * (2 * D.EF x y)) →
        ∀ v w, F (A v) (A w) = (2 * c) * formAf D v w := by
  intro p _ D F e hF A _ gs hA nu c hc hsim
  have key : ∀ x x', F (A (inAf D x)) (A (inAf D x')) = (2 * c) * formAf D (inAf D x) (inAf D x') := by
    intro x x'
    have := zero p (F (A (inAf D x)) (A (inAf D x')) - (2 * c) * formAf D (inAf D x) (inAf D x'))
      fun n hn hnp => by
      obtain ⟨w, hw, e₁⟩ := hA n hn hnp x
      obtain ⟨w', hw', e₂⟩ := hA n hn hnp x'
      obtain ⟨β, hβ, eβ⟩ := hc n hn hnp
      obtain ⟨k, hk⟩ := hsim n hn hnp x x'
      refine ⟨(k : AfP p) + F (inAf D (gs n x)) w' + F w (inAf D (gs n x')) +
        n • F w w' - (2 : ℤ) * β * (D.EF x x' : AfP p), ?_, ?_⟩
      · exact isInt_sub (isInt_add (isInt_add (isInt_add (isInt_intCast k)
          (formIntegral F e hF (inAf_mem D _) hw')) (formIntegral F e hF hw (inAf_mem D _)))
          (isInt_nsmul (formIntegral F e hF hw hw') n))
          (isInt_mul (isInt_mul (isInt_intCast 2) hβ) (isInt_intCast _))
      · have hk' := congrArg (Int.cast : ℤ → AfP p) hk
        push_cast at hk'
        rw [e₁, e₂, eβ]
        simp only [map_add, LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, form_inAf, hF, nsmul_eq_mul]
        push_cast
        linear_combination hk'
    exact sub_eq_zero.1 this
  have e2 := bilinear_ext_adelic_inclusion D (f := F.compl₁₂ A A) (g := (2 * c) • formAf D) fun x x' => by
    simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul]; exact key x x'
  intro v w
  have := LinearMap.congr_fun₂ e2 v w
  simpa using this
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.OneTmulMemCompletedLatticeIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

private theorem val_p_eq_one {p : ℕ} [Fact p.Prime] (v : AwayP p) :
    v.1.valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) = 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
  intro hp
  apply v.2
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible
  exact (hmax.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hp)).symm

private theorem isIntAf_of_pow_mul {p : ℕ} [Fact p.Prime] (q : ℚ) (r : ℕ) (c : ℤ)
    (h : ((p ^ r : ℕ) : ℚ) * q = c) : IsIntAf (algebraMap ℚ (AfP p) q) := by
  intro v
  rw [AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have hc : v.1.valuation ℚ (c : ℚ) ≤ 1 := by
    simpa using v.1.valuation_le_one (K := ℚ) c
  have hp : v.1.valuation ℚ ((p ^ r : ℕ) : ℚ) = 1 := by
    have h1 := val_p_eq_one v
    rw [eq_intCast] at h1
    push_cast at h1 ⊢
    rw [map_pow, h1, one_pow]
  have hq : v.1.valuation ℚ q ≤ 1 := by
    have h2 := congrArg (v.1.valuation ℚ) h
    rw [map_mul, hp, _root_.one_mul] at h2
    rw [h2]
    exact hc
  rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe]
  exact hq

theorem UpperTheory.one_tmul_mem_completedLattice_iff :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} (z : VQ D), (1 : AfP p) ⊗ₜ[ℚ] z ∈ LaHat D ↔ ∃ (r : ℕ) (x : D.La), p ^ r • z = (1 : ℚ) ⊗ₜ[ℤ] x := by
  intro p _ D z
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let bQ := Algebra.TensorProduct.basis ℚ b
  have key : ∀ i, (KNLevel.bA b).repr ((1 : AfP p) ⊗ₜ[ℚ] z) i = algebraMap ℚ (AfP p) (bQ.repr z i) := by
    intro i
    simp [KNLevel.bA, Algebra.TensorProduct.basis_repr_tmul, bQ]
  have hsm : ∀ (r : ℕ) i, bQ.repr (p ^ r • z) i = ((p ^ r : ℕ) : ℚ) * bQ.repr z i := by
    intro r i
    rw [← Nat.cast_smul_eq_nsmul ℚ, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul]
  have htm : ∀ (x : D.La) i, bQ.repr ((1 : ℚ) ⊗ₜ[ℤ] x) i = (b.repr x i : ℚ) := by
    intro x i
    simp [bQ, Algebra.TensorProduct.basis_repr_tmul]
  rw [KNLevel.mem_laHat_iff b]
  simp only [key]
  constructor
  · intro h
    choose k a hka using fun i => T.exists_primePow_mul_eq_int_of_integral_finiteAdeleAway p (bQ.repr z i) (h i)
    let r := ∑ i, k i
    let c : _ → ℤ := fun i => (p : ℤ) ^ (r - k i) * a i
    have hc : ∀ i, ((p ^ r : ℕ) : ℚ) * bQ.repr z i = (c i : ℚ) := by
      intro i
      have hk : k i ≤ r := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have hpow : (p : ℚ) ^ r = (p : ℚ) ^ (r - k i) * (p : ℚ) ^ (k i) := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      have ha := hka i
      push_cast at ha ⊢
      rw [hpow, _root_.mul_assoc, ha]
      simp [c]
    refine ⟨r, b.equivFun.symm c, ?_⟩
    apply bQ.ext_elem
    intro i
    have hb : b.repr (b.equivFun.symm c) i = c i := by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hsm, htm, hb]
    exact hc i
  · rintro ⟨r, x, hx⟩ i
    apply isIntAf_of_pow_mul _ r (b.repr x i)
    rw [← hsm, hx, htm]
end

-- bundled from Development.AutomorphicArithmetic.PAdicLatticeApproximation.PrimeToPIsogenyOfAdelicEndoPreservingLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open GlobalTheory.AdelicSim

theorem UpperTheory.primeToP_isogeny_of_adelic_endo_preserving_lattice :
    ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {D' : PLat D.O D.inv} (ψ : D'.La ≃+ D.La) (T : VQ D ≃ₗ[ℚ] VQ D) {j : D'.La →+ VQ D},
        (∀ u, T ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = j u) → (∀ (c : D.O) u, j (c • u) = actQ D c (j u)) →
        ∀ {f : ℕ → D.La →+ D'.La}, (∀ n : ℕ, 0 < n → n.Coprime p → ∀ (c : D.O) a, ∃ e, f n (c • a) = c • f n a + n • e) →
        ∀ (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), (∀ v ∈ LaHat D, A v ∈ LaHat D) →
        (∀ n : ℕ, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, A (inAf D x) = inAf D (ψ (f n x)) + n • w) → ∀ b : D.O,
        (T.toLinearMap.baseChange (AfP p)) * A * (actQ D b).baseChange (AfP p) =
          (actQ D b).baseChange (AfP p) * ((T.toLinearMap.baseChange (AfP p)) * A) := by
  intro p _ D D' ψ T j hj hjc f hf A hAL hA b
  let Cq : VQ D →ₗ[ℚ] VQ D := T.symm.toLinearMap ∘ₗ actQ D b ∘ₗ T.toLinearMap
  let Cc : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := Cq.baseChange (AfP p)
  have hC1 : ∀ u, Cq ((1 : ℚ) ⊗ₜ[ℤ] ψ u) = (1 : ℚ) ⊗ₜ[ℤ] ψ (b • u) := by
    intro u
    have h : T ((1 : ℚ) ⊗ₜ[ℤ] ψ (b • u)) = actQ D b (T ((1 : ℚ) ⊗ₜ[ℤ] ψ u)) := by
      rw [hj, hj, hjc]
    change T.symm (actQ D b (T ((1 : ℚ) ⊗ₜ[ℤ] ψ u))) = _
    rw [← h, T.symm_apply_apply]
  have hCt : ∀ (a : AfP p) (u : D'.La), Cc (a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] ψ u)) =
      a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] ψ (b • u)) := by
    intro a u
    change Cq.baseChange (AfP p) _ = _
    rw [LinearMap.baseChange_tmul, hC1]
  have hCin : ∀ u, Cc (inAf D (ψ u)) = inAf D (ψ (b • u)) := fun u => hCt 1 u
  have hCL : ∀ v ∈ LaHat D, Cc v ∈ LaHat D := by
    intro v hv
    induction hv using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, x, ha, rfl⟩ := hz
      obtain ⟨u, rfl⟩ := ψ.surjective x
      rw [hCt]
      exact AddSubgroup.subset_closure ⟨a, ψ (b • u), ha, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  have hAC : A * (actQ D b).baseChange (AfP p) = Cc * A := by
    refine ext_inAf D fun x => ?_
    have := modZero D ((A * (actQ D b).baseChange (AfP p)) (inAf D x) - (Cc * A) (inAf D x)) fun n hn hc => by
      obtain ⟨w, hw, e⟩ := hA n hn hc (b • x)
      obtain ⟨w', hw', e'⟩ := hA n hn hc x
      obtain ⟨z, hz⟩ := hf n hn hc b x
      refine ⟨inAf D (ψ z) + w - Cc w', sub_mem (add_mem (inAf_mem D _) hw) (hCL _ hw'), ?_⟩
      rw [Module.End.mul_apply, Module.End.mul_apply, bc_inAf, e, hz, e', map_add, map_add, hCin, map_nsmul,
        map_nsmul, inAf_add, inAf_nsmul]
      simp only [smul_add, smul_sub]; abel
    exact sub_eq_zero.1 this
  have hTC : (T.toLinearMap.baseChange (AfP p)) * Cc =
      (actQ D b).baseChange (AfP p) * (T.toLinearMap.baseChange (AfP p)) := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
      change T.toLinearMap.baseChange (AfP p) (Cq.baseChange (AfP p) (a ⊗ₜ[ℚ] m)) =
        (actQ D b).baseChange (AfP p) (T.toLinearMap.baseChange (AfP p) (a ⊗ₜ[ℚ] m))
      simp only [LinearMap.baseChange_tmul]
      congr 1
      change T (T.symm (actQ D b (T m))) = actQ D b (T m)
      exact T.apply_symm_apply _
  rw [_root_.mul_assoc, hAC, ← _root_.mul_assoc, hTC, _root_.mul_assoc]
end

