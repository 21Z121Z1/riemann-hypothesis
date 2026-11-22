import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0295
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0294
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0292
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0293
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFunctionsPeriodRingSeparation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrTeichProd
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.TestZar

theorem idem_unit {R : Type} [CommRing R] {u : R} (hu : IsIdempotentElem u) (h : IsUnit u) : u = 1 :=
  h.mul_left_cancel (by rw [mul_one]; exact hu)

theorem factor_one {R R' ι : Type} [CommRing R] [CommRing R'] (g : R →+* R') (b : ι → R) (hb : ∀ i, IsIdempotentElem (b i))
    (S : Finset ι) (h : g (∏ i ∈ S, b i) = 1) {i : ι} (hi : i ∈ S) : g (b i) = 1 :=
  idem_unit ((hb i).map g) (isUnit_of_dvd_unit (map_dvd g (Finset.dvd_prod_of_mem b hi)) (h ▸ isUnit_one))

theorem span_of_nil {R P ι : Type} [CommRing R] [CommRing P] (I : Ideal R) (hI : ∀ x ∈ I, IsNilpotent x) (g : ι → R)
    (π : P →+* R ⧸ I) (e : ι → P) (he : Ideal.span (Set.range e) = ⊤)
    (h : ∀ i, π (e i) = Ideal.Quotient.mk I (g i)) : Ideal.span (Set.range g) = ⊤ := by
  have h1 : Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range g)) = ⊤ := by
    have e1 : (Ideal.Quotient.mk I) ∘ g = π ∘ e := funext fun i => (h i).symm
    rw [Ideal.map_span, ← Set.range_comp, e1, Set.range_comp, ← Ideal.map_span, he, Ideal.map_top]
  have h2 : (1 : R ⧸ I) ∈ Ideal.map (Ideal.Quotient.mk I) (Ideal.span (Set.range g)) := by
    rw [h1]; trivial
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 h2
  have hj : a - 1 ∈ I := Ideal.Quotient.eq.1 (by rw [ha1, map_one])
  have hu : IsUnit a := by
    have := (hI _ hj).isUnit_add_one
    simpa using this
  exact Ideal.eq_top_of_isUnit_mem _ ha hu

section Gen

open GlobalTheory.CompanionTheory.ThickZar

variable {O : Type} [CommRing O] {F : Fn O} {b : Base} {ht : b.t = 1} {κ : O →+* b.R ⧸ b.I}
  {R₀ : Type} [CommRing R₀] (c : R₀ →+* b.R) (r : ℕ)
  {C : Type*} [Category C] (G : C ⥤ Thick (F.cr b ht κ))

def locModG {m : ℕ} (T' : C) (Lc : Finset (Fin m) → C) (lam : ∀ S, T' ⟶ Lc S)
    (f : Fin m → (G.obj T').B) (hf : Ideal.span (Set.range f) = ⊤)
    (h1 : ∀ S, ∀ k ∈ S, (G.map (lam S)).φ (f k) = 1)
    (hs : ∀ S, ∀ y ∈ (G.obj (Lc S)).pdPow r, ∃ x ∈ (G.obj T').pdPow r, (G.map (lam S)).φ x = y)
    (hk : ∀ S x, (G.map (lam S)).φ x = 0 → (∏ k ∈ S, f k) * x = 0) :
    LocMod (G ⋙ (pdS (F.cr b ht κ) c r).fn) T' Lc lam where
  Λ := (G.obj T').B
  f := f
  span := hf
  ρ₀ := mulR c r (G.obj T')
  ρ S := (mulR c r (G.obj (Lc S))).comp (G.map (lam S)).φ
  lam_ρ S a x := Subtype.ext (map_mul (G.map (lam S)).φ a (show (G.obj T').B from x.1))
  tr_ρ S S' t ht' a x := by
    have e : (G.map t).φ.comp (G.map (lam S)).φ = (G.map (lam S')).φ := by
      have := congrArg Thick.Hom.φ (congrArg G.map ht')
      rw [G.map_comp] at this
      exact this
    refine Subtype.ext ?_
    change (G.map t).φ ((G.map (lam S)).φ a * (show (G.obj (Lc S)).B from x.1)) =
      (G.map (lam S')).φ a * (G.map t).φ (show (G.obj (Lc S)).B from x.1)
    rw [map_mul, ← RingHom.comp_apply (G.map t).φ, e]
  unit S k hk' := by
    change Function.Bijective (mulR c r (G.obj (Lc S)) ((G.map (lam S)).φ (f k)))
    rw [h1 S k hk', map_one]
    exact Function.bijective_id
  surj S y := by
    obtain ⟨x, hx, e⟩ := hs S y.1 y.2
    refine ⟨0, ⟨x, hx⟩, ?_⟩
    rw [pow_zero, map_one]
    exact Subtype.ext e.symm
  ker S x hx := by
    have h0 : (G.map (lam S)).φ (show (G.obj T').B from x.1) = 0 := congrArg Subtype.val hx
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one]
    exact hk S _ h0

end Gen

variable {l : ℕ} [Fact l.Prime]

theorem step_onto {A B : PAlg l} (lam : A ⟶ B) (k : Bool) (n r : ℕ) (hs : Function.Surjective (mapAcr lam n))
    {y : B.Acr n} (hy : y ∈ fil (DD k B n) r) : ∃ x ∈ fil (DD k A n) r, mapAcr lam n x = y := by
  have hA := (GlobalTheory.T.period_ring_base_change_from_universal A n).2.2.2.2.1 k r
  have hB := (GlobalTheory.T.period_ring_base_change_from_universal B n).2.2.2.2.1 k r
  have e : (mapAcr lam n).comp (mapAcr A.fromBase n) = mapAcr B.fromBase n :=
    RingHom.ext fun x => mapAcr_fromBase lam n x
  rw [hB, ← e, ← Ideal.map_map, ← hA] at hy
  exact (Ideal.mem_map_iff_of_surjective _ hs).1 hy

theorem span_acr (A : PAlg l) (n : ℕ) {m : ℕ} (e : Fin m → A.A) (he : Ideal.span (Set.range e) = ⊤) :
    Ideal.span (Set.range fun i => A.toAcr n (WittVector.teichmuller l (e i))) = ⊤ := by
  obtain ⟨⟨π, hπ, -⟩, -, -, -, -, hnil, -⟩ := GlobalTheory.T.period_ring_base_change_from_universal A n
  exact span_of_nil (A.PFil n) (fun x hx => (hnil x hx).1) _ π e he fun i => hπ _

theorem acr_teich_one {A B : PAlg l} (f : A ⟶ B) (n : ℕ) {a : A.A} (h : Hom.f f a = 1) :
    mapAcr f n (A.toAcr n (WittVector.teichmuller l a)) = 1 := by
  rw [mapAcr_toAcr, mapW, WittVector.map_teichmuller, h, map_one, map_one]

theorem acr_teich_prod (A : PAlg l) (n : ℕ) {ι : Type} (S : Finset ι) (a : ι → A.A) :
    A.toAcr n (WittVector.teichmuller l (∏ i ∈ S, a i)) = ∏ i ∈ S, A.toAcr n (WittVector.teichmuller l (a i)) := by
  rw [map_prod, map_prod]

section Fac

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l)

def facObj (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) : El (F.pt κ) :=
  ⟨⟨A', h⟩, (F.pt κ).map lam T'.2⟩

def facHom (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) : T' ⟶ facObj F κ T' A' lam h :=
  ⟨ObjectProperty.homMk lam, rfl⟩

theorem facHom_hom (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) :
    (facHom F κ T' A' lam h).1.hom = lam := rfl

theorem fac_univ (T' : El (F.pt κ)) (A' : PAlg l) (lam : T'.1.obj ⟶ A') (h : A'.IsTest) (T'' : El (F.pt κ)) (ψ : T' ⟶ T'')
    (hu : ∃! χ : A' ⟶ T''.1.obj, lam ≫ χ = ψ.1.hom) :
    ∃! χ : facObj F κ T' A' lam h ⟶ T'', facHom F κ T' A' lam h ≫ χ = ψ := by
  obtain ⟨χ, hχ, huniq⟩ := hu
  refine ⟨⟨ObjectProperty.homMk χ, ?_⟩, Subtype.ext (ObjectProperty.hom_ext _ hχ), fun χ' h' =>
    Subtype.ext (ObjectProperty.hom_ext _ (huniq χ'.1.hom (congrArg (fun z => z.1.hom) h')))⟩
  change (F.pt κ).map χ ((F.pt κ).map lam T'.2) = T''.2
  rw [← Functor.map_comp_apply, hχ]
  exact ψ.2

theorem fac_loc (k : Bool) (n r : ℕ) (T' : El (F.pt κ)) {m : ℕ} (b : Fin m → T'.1.obj.A)
    (hspan : Ideal.span (Set.range b) = ⊤) (A' : Finset (Fin m) → PAlg l) (lam : ∀ S, T'.1.obj ⟶ A' S)
    (ht : ∀ S, (A' S).IsTest) (h1 : ∀ S, ∀ i ∈ S, Hom.f (lam S) (b i) = 1)
    (hs : ∀ S, Function.Surjective (mapAcr (lam S) n))
    (hk : ∀ S x, mapAcr (lam S) n x = 0 → T'.1.obj.toAcr n (WittVector.teichmuller l (∏ i ∈ S, b i)) * x = 0) :
    Nonempty (LocMod (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn) T'
      (fun S => facObj F κ T' (A' S) (lam S) (ht S)) fun S => facHom F κ T' (A' S) (lam S) (ht S)) := by
  have hf : Ideal.span (Set.range fun i => T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) = ⊤ := span_acr _ n b hspan
  have hk' : ∀ S x, mapAcr (lam S) n x = 0 →
      (∏ i ∈ S, T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) * x = 0 := fun S x hx => by
    have h := hk S x hx
    rw [acr_teich_prod] at h
    exact h
  exact ⟨locModG (F := F) (b := bs l k n) (ht := rfl) (κ := κb κ k n) ((base l).cris n) r (gT F κ k n) T'
    (fun S => facObj F κ T' (A' S) (lam S) (ht S)) (fun S => facHom F κ T' (A' S) (lam S) (ht S))
    (fun i => T'.1.obj.toAcr n (WittVector.teichmuller l (b i))) hf
    (fun S i hi => acr_teich_one (lam S) n (h1 S i hi))
    (fun S y hy => step_onto (lam S) k n r (hs S) hy) hk'⟩

theorem factors (k : Bool) (n r : ℕ) (T' : El (F.pt κ)) {m : ℕ}
    (b : Fin m → T'.1.obj.A) (hb : ∀ i, IsIdempotentElem (b i)) (hspan : Ideal.span (Set.range b) = ⊤) :
    ∃ (Lc' : Finset (Fin m) → El (F.pt κ)) (lamE : ∀ S, T' ⟶ Lc' S),
      (∀ S, ∀ i ∈ S, Hom.f (lamE S).1.hom (b i) = 1) ∧
      (∀ S (T'' : El (F.pt κ)) (ψ : T' ⟶ T''), (∀ i ∈ S, Hom.f ψ.1.hom (b i) = 1) → ∃! χ : Lc' S ⟶ T'', lamE S ≫ χ = ψ) ∧
      Nonempty (LocMod (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn) T' Lc' lamE) := by
  have ha : ∀ S : Finset (Fin m), IsIdempotentElem (∏ i ∈ S, b i) := fun S =>
    Finset.prod_induction _ IsIdempotentElem (fun _ _ h h' => h.mul h') IsIdempotentElem.one fun i _ => hb i
  choose A' lam htest hlam huniv hacr using fun S => GlobalTheory.T.idempotent_localization_universal T'.1.obj (∏ i ∈ S, b i) (ha S)
  have h1 : ∀ S, ∀ i ∈ S, Hom.f (lam S) (b i) = 1 := fun S i hi => factor_one (Hom.f (lam S)) b hb S (hlam S) hi
  have ht : ∀ S, (A' S).IsTest := fun S => htest S T'.1.property
  refine ⟨fun S => facObj F κ T' (A' S) (lam S) (ht S), fun S => facHom F κ T' (A' S) (lam S) (ht S), h1,
    fun S T'' ψ h => fac_univ F κ T' (A' S) (lam S) (ht S) T'' ψ (huniv S T''.1.obj ψ.1.hom ?_),
    fac_loc F κ k n r T' b hspan A' lam ht h1 (fun S => (hacr S n).1) fun S => (hacr S n).2⟩
  rw [map_prod]
  exact Finset.prod_eq_one fun i hi => h i hi

end Fac

theorem chart_of_one {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d) (k : Bool) (n : ℕ)
    {T T₁ : El (F.pt κ)} (ψ : T ⟶ T₁) (s : T.1.obj.U) (a : T.1.obj.A) (ha : T.1.obj.sharp a ∈ Ideal.span {s})
    (hcov : ∀ (B' : CommRingCat) (φ : CommRingCat.of T.1.obj.U ⟶ B'), IsUnit (φ.hom s) →
      ∃ α, (𝒜.V α).In (F.Pt.map φ T.2.1))
    (h : Hom.f ψ.1.hom a = 1) : ∃ α, (𝒜.V α).In ((gT F κ k n).obj T₁).y.1.2 := by
  have hu : IsUnit ((CommRingCat.ofHom (mapU ψ.1.hom)).hom s) := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
    have h2 := congrArg (mapU ψ.1.hom) hc
    rw [map_mul, mapU_sharp, h, map_one] at h2
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h2)
  obtain ⟨α, hα⟩ := hcov _ _ hu
  have hpt : F.Pt.map (CommRingCat.ofHom (mapU ψ.1.hom)) T.2.1 = T₁.2.1 := congrArg Subtype.val ψ.2
  rw [hpt] at hα
  exact ⟨α, (𝒜.V α).in_map (CommRingCat.ofHom (uJ k T₁.1.obj n)) hα⟩

theorem zarCov_test : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {d : ℕ} (𝒜 : F.Atlas d)
    (k : Bool) (n r : ℕ), ZarCov (gT F κ k n ⋙ (pdS (Lc F κ k n) ((base l).cris n) r).fn)
      fun T => ∃ α, (𝒜.V α).In ((gT F κ k n).obj T).y.1.2 := by
  intro l _ O _ F κ d 𝒜 k n r
  refine ⟨fun T T' φ h => (GlobalTheory.CompanionTheory.ThickZar.zarCov_pdS F (bs l k n) rfl (κb κ k n) ((base l).cris n) 𝒜
    (Fact.out : l.Prime).ne_zero r).1 ((gT F κ k n).map φ) h, fun T => ?_⟩
  obtain ⟨m, s, hs, hcov⟩ := 𝒜.cov (CommRingCat.of T.1.obj.U) T.2.1
  obtain ⟨e, hidem, hspan, hes⟩ := GlobalTheory.T.idempotent_refinement_of_unimodular T.1.obj T.1.property s hs
  refine ⟨m, fun i _ ψ => Hom.f ψ.1.hom (e i) = 1, fun i T₁ T₂ ψ χ h => ?_,
    fun i T₁ ψ h => chart_of_one F κ 𝒜 k n ψ (s i) (e i) (hes i) (hcov i) h, fun T' φ => ?_⟩
  · have h' : Hom.f ψ.1.hom (e i) = 1 := h
    have e1 : Hom.f (ψ ≫ χ).1.hom (e i) = Hom.f χ.1.hom (Hom.f ψ.1.hom (e i)) := rfl
    exact e1.trans (by rw [h', map_one])
  have hspan' : Ideal.span (Set.range fun i => Hom.f φ.1.hom (e i)) = ⊤ := by
    have h := congrArg (Ideal.map (Hom.f φ.1.hom)) hspan
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    exact h
  obtain ⟨Lc', lamE, h1, h2, h3⟩ := factors F κ k n r T' (fun i => Hom.f φ.1.hom (e i))
    (fun i => (hidem i).map (Hom.f φ.1.hom)) hspan'
  exact ⟨Lc', lamE, fun S i hi => h1 S i hi, fun S T'' ψ h => h2 S T'' ψ fun i hi => h i hi, h3⟩

end GlobalTheory.CompanionTheory.TestZar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActionEquivarianceStatement
section
noncomputable section

open Finset Matrix MeasureTheory

namespace GlobalTheory.CompanionTheory.ActEquivK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs.K

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

lemma jm_inv (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε :=
  Matrix.inv_eq_left_inv (signature_matrix_sq ε)

lemma hinvol (ε : Fin n → Bool) : AAInvW.HInvol (Formalism.REAL.Jm ε) := by
  refine ⟨?_, signature_matrix_sq ε⟩
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

lemma eabH_eq (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Formalism.QuantumDeterminants.EabH (Formalism.REAL.Jm ε) a b f = Formalism.REAL.Eab ε a b f := by
  funext g
  have h1 : Formalism.QuantumDeterminants.hpart1 (Formalism.REAL.Jm ε) (Matrix.single a b 1) = Formalism.REAL.cpart1 ε (Matrix.single a b 1) := by
    unfold Formalism.QuantumDeterminants.hpart1 Formalism.REAL.cpart1
    rw [jm_inv]
  have h2 : Formalism.QuantumDeterminants.hpart2 (Formalism.REAL.Jm ε) (Matrix.single a b 1) = Formalism.REAL.cpart2 ε (Matrix.single a b 1) := by
    unfold Formalism.QuantumDeterminants.hpart2 Formalism.REAL.cpart2
    rw [jm_inv]
  unfold Formalism.QuantumDeterminants.EabH
  rw [h1, h2]
  rfl

lemma inUJ_inv {k : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) : Formalism.REAL.inUJ ε k⁻¹ := by
  have hm : k * k⁻¹ = 1 := AAInvW.ana_mul_inv (hinvol ε) hk
  have h0 : kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε := hk
  show (k⁻¹)ᴴ * Formalism.REAL.Jm ε * k⁻¹ = Formalism.REAL.Jm ε
  calc (k⁻¹)ᴴ * Formalism.REAL.Jm ε * k⁻¹ = (k⁻¹)ᴴ * (kᴴ * Formalism.REAL.Jm ε * k) * k⁻¹ := by rw [h0]
    _ = (k * k⁻¹)ᴴ * Formalism.REAL.Jm ε * (k * k⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hm]; simp

lemma smooth_right {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) :
    Formalism.REAL.SmoothOnG ε (fun x => f (x * k)) :=
  AAInvW.smooth_right' n (Formalism.REAL.Jm ε) ℂ f k (hinvol ε) hk hf

lemma eab_local {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n)
    (h : ∀ x, Formalism.REAL.inUJ ε x → f x = f' x) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.Eab ε a b f g = Formalism.REAL.Eab ε a b f' g := by
  rw [← eabH_eq, ← eabH_eq]
  exact AAInvW.eab_h_local n (Formalism.REAL.Jm ε) ℂ f f' a b g (hinvol ε) h hg

lemma eab_zero (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Eab ε a b (fun _ => (0 : ℂ)) g = 0 := by
  simp [Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd]

lemma eab_lin {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ) (a b : Fin n)
    (hf : Formalism.REAL.SmoothOnG ε f) (hf' : Formalism.REAL.SmoothOnG ε f')
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => f x + c * f' x) g =
      Formalism.REAL.Eab ε a b f g + c * Formalism.REAL.Eab ε a b f' g := by
  have := AAInvW.eab_h_linear n (Formalism.REAL.Jm ε) ℂ f f' c a b g (hinvol ε) hf hf' hg
  simpa only [eabH_eq, smul_eq_mul] using this

lemma smooth_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, Formalism.REAL.SmoothOnG ε (F i)) :
    Formalism.REAL.SmoothOnG ε (fun x => ∑ i ∈ s, c i * F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Formalism.REAL.smooth_on_group_const_fun (ε := ε) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact Formalism.REAL.smooth_on_group_add (Formalism.REAL.smooth_on_group_const_mul (c i) (hF i)) ih

lemma eab_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, Formalism.REAL.SmoothOnG ε (F i)) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => ∑ i ∈ s, c i * F i x) g =
      ∑ i ∈ s, c i * Formalism.REAL.Eab ε a b (F i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using eab_zero (ε := ε) a b g
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have e : (fun x => c i * F i x + ∑ j ∈ s, c j * F j x) =
        fun x => (∑ j ∈ s, c j * F j x) + c i * F i x := funext fun x => add_comm _ _
    rw [e, eab_lin (c i) a b (smooth_sum s c F hF) (hF i) hg, ih, add_comm]

lemma eab_mul_right {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f) (a b : Fin n)
    {k g : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b f (g * k) =
      ∑ q : Fin n × Fin n, adC k (a, b) q * Formalism.REAL.Eab ε q.1 q.2 (fun x => f (x * k)) g := by
  have hJ := hinvol ε
  have hmi : k * k⁻¹ = 1 := AAInvW.ana_mul_inv hJ hk
  have him : k⁻¹ * k = 1 := AAInvW.ana_inv_mul hJ hk
  have hgk : Formalism.REAL.inUJ ε (g * k) := AAInvW.ana_mul hg hk
  have h := AAInvW.eab_h_right n (Formalism.REAL.Jm ε) ℂ (fun x => f (x * k)) a b k⁻¹ (g * k) hJ
    (smooth_right hf hk) (inUJ_inv hk) hgk
  have e1 : (fun x => (fun y => f (y * k)) (x * k⁻¹)) = f := by
    funext x
    show f (x * k⁻¹ * k) = f x
    rw [Matrix.mul_assoc, him, Matrix.mul_one]
  have e2 : g * k * k⁻¹ = g := by rw [Matrix.mul_assoc, hmi, Matrix.mul_one]
  have e3 : (k⁻¹)⁻¹ = k := Matrix.inv_eq_left_inv hmi
  rw [e1, e2, e3, eabH_eq] at h
  rw [h, Fintype.sum_prod_type]
  simp only [eabH_eq, smul_eq_mul]
  rfl

lemma eword_local (w : List (Fin n × Fin n)) {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ x, Formalism.REAL.inUJ ε x → f x = f' x) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.Eword ε w f g = Formalism.REAL.Eword ε w f' g := by
  induction w generalizing g with
  | nil => exact h g hg
  | cons p w ih => exact eab_local p.1 p.2 (fun x hx => ih hx) hg

lemma eword_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, Formalism.REAL.SmoothOnG ε (F i)) (w : List (Fin n × Fin n))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eword ε w (fun x => ∑ i ∈ s, c i * F i x) g =
      ∑ i ∈ s, c i * Formalism.REAL.Eword ε w (F i) g := by
  induction w generalizing g with
  | nil => rfl
  | cons p w ih =>
    show Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε w _) g =
      ∑ i ∈ s, c i * Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε w (F i)) g
    rw [eab_local p.1 p.2 (f' := fun x => ∑ i ∈ s, c i * Formalism.REAL.Eword ε w (F i) x)
      (fun x hx => ih hx) hg]
    exact eab_sum s c _ (fun i => Formalism.REAL.smooth_iterated_lie_derivative (hF i) w) p.1 p.2 hg

lemma sum_cons {α : Type*} [Fintype α] [DecidableEq α] {l : ℕ} (Φ : (Fin (l + 1) → α) → ℂ) :
    ∑ W, Φ W = ∑ q : α, ∑ w : Fin l → α, Φ (Fin.cons q w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => α)) _ _ (fun _ => rfl)).symm

lemma eword_mul_right {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) :
    ∀ (l : ℕ) (x : Fin l → Fin n × Fin n) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eword ε (List.ofFn x) f (g * k) =
        ∑ w : Fin l → Fin n × Fin n, (∏ i, adC k (x i) (w i)) *
          Formalism.REAL.Eword ε (List.ofFn w) (fun y => f (y * k)) g := by
  intro l
  induction l with
  | zero =>
    intro x g hg
    simp [Formalism.REAL.Eword]
  | succ l ih =>
    intro x g hg
    have hfk := smooth_right hf hk
    rw [sum_cons, List.ofFn_succ]
    show Formalism.REAL.Eab ε (x 0).1 (x 0).2 (Formalism.REAL.Eword ε (List.ofFn fun i => x i.succ) f) (g * k) = _
    rw [eab_mul_right (Formalism.REAL.smooth_iterated_lie_derivative hf _) _ _ hk hg]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [eab_local q.1 q.2 (f' := fun y => ∑ w : Fin l → Fin n × Fin n,
        (∏ i, adC k (x i.succ) (w i)) * Formalism.REAL.Eword ε (List.ofFn w) (fun y => f (y * k)) y)
      (fun y hy => ih _ y hy) hg,
      eab_sum _ _ _ (fun w => Formalism.REAL.smooth_iterated_lie_derivative hfk _) q.1 q.2 hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fin.prod_univ_succ, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    show _ = _ * Formalism.REAL.Eab ε q.1 q.2 (Formalism.REAL.Eword ε (List.ofFn w) _) g
    ring

theorem actEquiv : ActEquiv := by
  intro n ε lam T Ψ m hP k a
  have hk : Formalism.REAL.inUJ ε (toMK k) := (mir_inUJ_iff ε _).2 k.1.2
  have hJ : ∀ v, Formalism.REAL.SmoothOnG ε (jfun Ψ T.w v) := fun v =>
    pdA_smooth_clm (pdA_coef T.w v) (f := Ψ) hP.2.2.1
  have hJk : ∀ v y, Formalism.REAL.inUJ ε y →
      jfun Ψ T.w v (y * toMK k) = jfun Ψ T.w (T.op k v) y := by
    intro v y hy
    show inner ℂ T.w (Ψ (y * toMK k) v) = inner ℂ T.w (Ψ y (T.op k v))
    have h1 := hP.1 1 k y ((mir_inUJ_iff ε _).1 hy)
    rw [pdA_toMK_one, Matrix.one_mul, pdA_op_one, one_mul] at h1
    rw [h1]
    rfl
  unfold actL
  rw [rightRegular_toL2 ε _ (show toMK k ∈ UJset ε from k.1.2)]
  refine toL2_congr_of_forall_inUJ_eq fun g hg' => ?_
  have hg : Formalism.REAL.inUJ ε g := (mir_inUJ_iff ε _).2 hg'
  have hL : ∀ x : Wd n m, Formalism.REAL.Eword ε (ofW x) (fun y => inner ℂ T.w (Ψ y (a x))) (g * toMK k) =
      ∑ w : Fin x.1 → Fin n × Fin n, (∏ i, adC (toMK k) (x.2 i) (w i)) *
        Formalism.REAL.Eword ε (List.ofFn w) (jfun Ψ T.w (T.op k (a x))) g := by
    intro x
    refine (eword_mul_right (hJ (a x)) hk x.1 x.2 g hg).trans (Finset.sum_congr rfl fun w _ => ?_)
    rw [eword_local (List.ofFn w) (f' := jfun Ψ T.w (T.op k (a x))) (fun y hy => hJk _ y hy) hg]
  have hR : ∀ x : Wd n m, Formalism.REAL.Eword ε (ofW x)
        (fun y => inner ℂ T.w (Ψ y (rhoA T m k a x))) g =
      ∑ w : Fin x.1 → Fin n × Fin n, (∏ i, adC (toMK k) (w i) (x.2 i)) *
        Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (T.op k (a ⟨x.1, w⟩))) g := by
    intro x
    have e : (fun y => inner ℂ T.w (Ψ y (rhoA T m k a x))) = fun y =>
        ∑ w ∈ (Finset.univ : Finset (Fin x.1 → Fin n × Fin n)), (∏ i, adC (toMK k) (w i) (x.2 i)) *
          jfun Ψ T.w (T.op k (a ⟨x.1, w⟩)) y := by
      funext y
      simp only [rhoA, map_sum, map_smul, inner_sum, inner_smul_right, jfun]
    rw [e]
    exact eword_sum _ _ _ (fun w => hJ _) _ hg
  show actF T Ψ a (g * toMK k) = actF T Ψ (rhoA T m k a) g
  unfold actF
  rw [Finset.sum_apply, Finset.sum_apply]
  simp only [hL, hR]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Finset.sum_comm (s := (Finset.univ : Finset (Fin (l : ℕ) → Fin n × Fin n))) (t := Finset.univ)
    (f := fun y w => (∏ i, adC (toMK k) (y i) (w i)) *
      Formalism.REAL.Eword ε (List.ofFn w) (jfun Ψ T.w (T.op k (a ⟨l, y⟩))) g)

end GlobalTheory.CompanionTheory.ActEquivK
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropicQuaternionNormOneCompactStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anisotropic_quaternion_norm_one_compact : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (s : Pl F), (∀ x : Q d β (Kp s), qn x = 0 → x = 0) → IsCompact {x : Q d β (Kp s) | qn x = 1} := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.isCompact_qn_eq_one_at_place | exact GlobalTheory.CompanionTheory.PlaneSA.isCompact_qn_eq_one_at_place | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.isCompact_qn_eq_one_at_place <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystemStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artin_rees_closed_system : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsSeparated (X ↘ Spec (.of A))] [LocallyOfFiniteType (X ↘ Spec (.of A))] [QuasiCompact (X ↘ Spec (.of A))] {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → PropSupp A (S 0) → ∀ (D : Subobject E), (D : X.Modules).IsQuasicoherent → ∀ c : ℕ, (∀ e, S (e + c) ≤ D ⊔ powSub I E (e + 1)) → ∃ c' : ℕ, ClosedSys I (D : X.Modules) (restrictSys I D S c') ∧ PropSupp A (restrictSys I D S c' 0) ∧ (Alg I (D : X.Modules) (restrictSys I D S c') → PropSupp A D → Alg I E S) := by
  first | exact @GlobalTheory.CompanionTheory.GE.Comb.restrict_alg | exact GlobalTheory.CompanionTheory.GE.Comb.restrict_alg | (intros; apply GlobalTheory.CompanionTheory.GE.Comb.restrict_alg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartVanishingKillsFormMulPowStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_vanishing_kills_form_mul_pow : ∀ {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ] (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) (k : Fin (N + 1)),
    (φ.app (GlobalTheory.ProjSpace.chart R N k)).hom
      (GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf) = 0 →
    ∃ (m : ℕ) (h : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n)),
      KillsForm φ (m + n) (X k ^ m * f) h := by
  first | exact @GlobalTheory.CompanionTheory.GE.exists_killsForm_X_pow_mul | exact GlobalTheory.CompanionTheory.GE.exists_killsForm_X_pow_mul | (intros; apply GlobalTheory.CompanionTheory.GE.exists_killsForm_X_pow_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompatibleSectionsGlueHomogeneousStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_sections_glue_homogeneous : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (N : ℕ) (P : Ideal (MvPolynomial (Fin (N + 1)) B)), HomogIdeal P →
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ (k : ℕ) (f : Fin (N + 1) → MvPolynomial (Fin (N + 1)) B),
      (∀ i, (f i).IsHomogeneous (n + k)) →
      (∀ i j, ∃ m : ℕ, (X i * X j) ^ m * (X j ^ k * f i - X i ^ k * f j) ∈ P) →
      ∃ g : MvPolynomial (Fin (N + 1)) B, g.IsHomogeneous n ∧
        ∀ i, ∃ m : ℕ, X i ^ m * (X i ^ k * g - f i) ∈ P := by
  first | exact @GlobalTheory.CompanionTheory.GE.SerreVan.serre_vanishing | exact GlobalTheory.CompanionTheory.GE.SerreVan.serre_vanishing | (intros; apply GlobalTheory.CompanionTheory.GE.SerreVan.serre_vanishing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFunctionsPeriodRingSeparationStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_functions_period_ring_separation : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), (∀ x : (A.cont ℤ_[l]).Acr n, IsLocallyConstant fun z => mapAcr (A.evCont z) n x) ∧ (∀ x : (A.cont ℤ_[l]).Acr n, (∀ z, mapAcr (A.evCont z) n x = 0) → x = 0) ∧ ∀ (𝔞 : Ideal ((base l).Acr n)) (f : ℤ_[l] → A.Acr n), IsLocallyConstant f → (∀ z, f z ∈ 𝔞.map (mapAcr A.fromBase n)) → ∃ x ∈ 𝔞.map (mapAcr (A.cont ℤ_[l]).fromBase n), ∀ z, mapAcr (A.evCont z) n x = f z := by
  first | exact @GlobalTheory.CompanionTheory.ContAcr.acr_cont | exact GlobalTheory.CompanionTheory.ContAcr.acr_cont | (intros; apply GlobalTheory.CompanionTheory.ContAcr.acr_cont <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallinePointUniversalLiftStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_point_universal_lift : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (T : (F.pt κ).Elements), ∃ g : s.R →+* T.1.U, F.Pt.map (CommRingCat.ofHom g) s.y₀ = T.2.1 ∧ (∀ φ : 𝒯.obj ⟶ T, (mapU φ.1).comp 𝒯.g = g) ∧ ∀ u : Fin d → T.1.A, (∀ k, T.1.sharp (u k) = g (s.T k)) → ∃! φ : 𝒯.obj ⟶ T, ∀ k, PAlg.Hom.f φ.1 (𝒯.c k 0).val = u k := by
  first | exact @GlobalTheory.CompanionTheory.TowerHom.tower_hom | exact GlobalTheory.CompanionTheory.TowerHom.tower_hom | (intros; apply GlobalTheory.CompanionTheory.TowerHom.tower_hom <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobsonIdealFaithfulModuleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobson_ideal_faithful_module : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens) (hV : IsAffineOpen V) [IsNoetherianRing Γ(X, V)] (I : Ideal Γ(X, V)) {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R] {M : Type} [AddCommGroup M] [Module R M] [Module Γ(X, V) M] [IsScalarTower Γ(X, V) R M] [Module.Finite R M], I.map (algebraMap Γ(X, V) R) ≤ Ideal.jacobson ⊥ → (∀ a ∈ J.ideal ⟨V, hV⟩, ∀ m : M, a • m = 0) → ∀ f : Γ(X, V), IsIso (ψ ∣_ (J.subschemeι ⁻¹ᵁ X.basicOpen f)) → ∀ y : M, (∀ n, ChartIn (ψ ≫ J.subschemeι) V (I ^ (n + 1) • ⊤ : Submodule Γ(X, V) M) y) → ∃ k : ℕ, f ^ k • y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.GE.Krull.fPow_torsion_of_chartIn | exact GlobalTheory.CompanionTheory.GE.Krull.fPow_torsion_of_chartIn | (intros; apply GlobalTheory.CompanionTheory.GE.Krull.fPow_torsion_of_chartIn <;> assumption)
end

