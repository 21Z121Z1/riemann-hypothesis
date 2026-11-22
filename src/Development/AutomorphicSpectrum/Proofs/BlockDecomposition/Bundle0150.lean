import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0140
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyProjectorComplexBounded
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0142
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsoOfThickenings
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FormalAlgebraisation.GEClosedProj
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1CoboundaryMemBoundaries

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GreenbergWilesFormulaStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.greenberg_wiles_formula : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ (j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), μ.comp (toGS Ω _) = cycMod F Ω l r → Finite (TDual (ZMod (l ^ r)) M) → LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → NineTermExact S Av μ j ρ hρ → ShaDual S Av μ ρ → Finite (H0 ρ) ∧ Finite (H1 ρ) ∧ Finite (H2 ρ) ∧ Finite (H0 (twDual μ ρ)) ∧ Finite (H1 (twDual μ ρ)) := by
  first | exact @GlobalTheory.CompanionTheory.GaloisCoh.global_finite_of_poitouTate | exact GlobalTheory.CompanionTheory.GaloisCoh.global_finite_of_poitouTate | (intros; apply GlobalTheory.CompanionTheory.GaloisCoh.global_finite_of_poitouTate <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealComponentMemStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_ideal_component_mem : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ f ∈ homIdeal i, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ homIdeal i := by
  first | exact @GlobalTheory.CompanionTheory.Geo.homIdeal_homog | exact GlobalTheory.CompanionTheory.Geo.homIdeal_homog | (intros; apply GlobalTheory.CompanionTheory.Geo.homIdeal_homog <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealNeTopStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_ideal_ne_top : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), Nonempty X → homIdeal i ≠ ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.GeoNetop.homIdeal_ne_top | exact GlobalTheory.CompanionTheory.GeoNetop.homIdeal_ne_top | (intros; apply GlobalTheory.CompanionTheory.GeoNetop.homIdeal_ne_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIntegralExpressionStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneous_integral_expression : ∀ {K σ : Type} [Field K] {m : ℕ} (I : Ideal (MvPolynomial σ K)), (∀ f ∈ I, ∀ n : ℕ, MvPolynomial.homogeneousComponent n f ∈ I) → ∀ (e : ℕ), 0 < e → ∀ (y : Fin m → MvPolynomial σ K), (∀ k, (y k).IsHomogeneous e) → Module.Finite (Algebra.adjoin K (Set.range fun k => Ideal.Quotient.mk I (y k))) (MvPolynomial σ K ⧸ I) → ∀ (w : ℕ) (a : MvPolynomial σ K), a.IsHomogeneous (e * w) → ∃ (s : ℕ) (c : ℕ → MvPolynomial (Fin m) K), 0 < s ∧ (∀ l, (c l).IsHomogeneous ((s - l) * w)) ∧ a ^ s + ∑ l ∈ Finset.range s, MvPolynomial.aeval y (c l) * a ^ l ∈ I := by
  first | exact @GlobalTheory.CompanionTheory.Geo.exists_hom_relation | exact GlobalTheory.CompanionTheory.Geo.exists_hom_relation | (intros; apply GlobalTheory.CompanionTheory.Geo.exists_hom_relation <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomotopyProjectorComplexBoundedStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homotopy_projector_complex_bounded : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] (E : ℕ → Type) [∀ n, AddCommGroup (E n)]
    [∀ n, Module R (E n)] [∀ n, Module.Flat R (E n)] (d : ∀ n, E n →ₗ[R] E (n + 1))
    (_ : ∀ n, d (n + 1) ∘ₗ d n = 0) (e : ∀ n, E n →ₗ[R] E n) (h : ∀ n, E (n + 1) →ₗ[R] E n) (B : ℕ)
    (_ : ∀ n, e n ∘ₗ e n = e n) (_ : ∀ n, e (n + 1) ∘ₗ d n = d n ∘ₗ e n)
    (_ : e 0 = LinearMap.id + h 0 ∘ₗ d 0)
    (_ : ∀ n, e (n + 1) = LinearMap.id + d n ∘ₗ h n + h (n + 1) ∘ₗ d (n + 1))
    (_ : ∀ n, B < n → e n = 0)
    (_ : Module.Finite R (LinearMap.ker (d 0)))
    (_ : ∀ n, Module.Finite R (LinearMap.ker (d (n + 1)) ⧸
      (LinearMap.range (d n)).comap (LinearMap.ker (d (n + 1))).subtype)),
    ∃ (Q : CochainComplex (ModuleCat.{0} R) ℕ) (ψ : ∀ n, Q.X n →ₗ[R] E n),
      (∀ n, Module.Finite R (Q.X n)) ∧ (∀ n, Module.Projective R (Q.X n)) ∧
      (∀ n, ψ (n + 1) ∘ₗ (Q.d n (n + 1)).hom = d n ∘ₗ ψ n) ∧
      ∀ M : ModuleCat.{0} R,
        QIsoAt (0 : R →ₗ[R] M ⊗[R] Q.X 0) ((Q.d 0 1).hom.lTensor M) (0 : R →ₗ[R] M ⊗[R] E 0)
          ((d 0).lTensor M) ((ψ 0).lTensor M) ∧
        ∀ n, QIsoAt ((Q.d n (n + 1)).hom.lTensor M) ((Q.d (n + 1) (n + 2)).hom.lTensor M)
          ((d n).lTensor M) ((d (n + 1)).lTensor M) ((ψ (n + 1)).lTensor M) := by
  first | exact @GlobalTheory.CompanionTheory.PerfRetract.exists_finite_projective_model | exact GlobalTheory.CompanionTheory.PerfRetract.exists_finite_projective_model | (intros; apply GlobalTheory.CompanionTheory.PerfRetract.exists_finite_projective_model <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealSquareLeKernelOfSquareZeroMapStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_square_le_kernel_of_square_zero_map : ∀ (R Q B : Type) [CommRing R] [CommRing Q] [CommRing B] (U : Scheme.{0}) (e : Sp R ⟶ U) [IsClosedImmersion e] (q : Q →+* B) (ρ : R →+* B) (y : Sp Q ⟶ U), Function.Surjective q → (∀ a b : Q, q a = 0 → q b = 0 → a * b = 0) → spMap q ≫ y = spMap ρ ≫ e → e.ker ^ 2 ≤ y.ker := by
  first | exact @GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker | exact GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker | (intros; apply GlobalTheory.CompanionTheory.CotKer.ker_sq_le_ker <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InertiaQuotientTransport
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso

namespace GlobalTheory.CompanionTheory.PTIso

theorem map_mem_closedNormal {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] (Φ : A ≃ₜ* B) (X : Set A) (Y : Set B)
    (h : ∀ a ∈ X, Φ a ∈ Y) {a : A} (ha : a ∈ (Subgroup.normalClosure X).topologicalClosure) :
    Φ a ∈ (Subgroup.normalClosure Y).topologicalClosure := by
  let f : A →* B := (Φ : A ≃* B).toMonoidHom
  let K : Subgroup B := (Subgroup.normalClosure Y).topologicalClosure
  haveI : K.Normal := Subgroup.is_normal_topologicalClosure _
  haveI : (K.comap f).Normal := Subgroup.Normal.comap ‹_› f
  have hK : IsClosed (K : Set B) := Subgroup.isClosed_topologicalClosure _
  have hc : IsClosed ((K.comap f : Subgroup A) : Set A) := hK.preimage Φ.continuous
  have hle : Subgroup.normalClosure X ≤ K.comap f := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (h x hx))
  exact Subgroup.topologicalClosure_minimal _ hle hc ha

def quotientIso {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] (Φ : A ≃ₜ* B)
    (H : Subgroup A) (K : Subgroup B) [H.Normal] [K.Normal] (h : ∀ a, a ∈ H ↔ Φ a ∈ K) :
    A ⧸ H ≃ₜ* B ⧸ K where
  toMulEquiv := QuotientGroup.congr H K (Φ : A ≃* B) (by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (h a).1 ha
    · intro hb
      exact ⟨Φ.symm b, (h _).2 (by simpa using hb), Φ.apply_symm_apply b⟩)
  continuous_toFun := by
    exact (QuotientGroup.isQuotientMap_mk H).continuous_iff.2
      (QuotientGroup.continuous_mk.comp Φ.continuous)
  continuous_invFun := by
    exact (QuotientGroup.isQuotientMap_mk K).continuous_iff.2
      (QuotientGroup.continuous_mk.comp Φ.symm.continuous)

theorem exists_gsIso : ∀ (F Ω F' Ω' : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω'] (e : F ≃+* F') (E : Ω ≃+* Ω'), (∀ x : F, E (algebraMap F Ω x) = algebraMap F' Ω' (e x)) → ∀ (Φ : G F Ω ≃ₜ* G F' Ω'), (∀ (σ : G F Ω) (x : Ω), Φ σ (E x) = E (σ x)) → ∀ (eV : HeightOneSpectrum (𝓞 F) ≃ HeightOneSpectrum (𝓞 F')), (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v ↔ IsPlaceOver A' (eV v)) → (∀ (A : ValuationSubring Ω) (A' : ValuationSubring Ω'), (∀ x, E x ∈ A' ↔ x ∈ A) → ∀ σ : G F Ω, σ ∈ Inertia (F := F) A ↔ Φ σ ∈ Inertia (F := F') A') → ∀ (T : Set (HeightOneSpectrum (𝓞 F))) (T' : Set (HeightOneSpectrum (𝓞 F'))), (∀ v, v ∈ T ↔ eV v ∈ T') → ∃ Ψ : GS Ω T ≃ₜ* GS Ω' T', ∀ σ : G F Ω, Ψ (toGS Ω T σ) = toGS Ω' T' (Φ σ) := by
  intro F Ω F' Ω' _ _ _ _ _ _ _ _ _ _ e E _ Φ _ eV hP hI T T' hT
  have hfwd : ∀ σ, σ ∈ NS Ω T → Φ σ ∈ NS Ω' T' := by
    intro σ hσ
    refine map_mem_closedNormal Φ _ _ ?_ hσ
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ ⊢
    obtain ⟨v, hv, A, hA, hτ⟩ := hτ
    let A' : ValuationSubring Ω' := A.comap (E.symm : Ω' →+* Ω)
    have hAA : ∀ x, E x ∈ A' ↔ x ∈ A := by
      intro x
      show E.symm (E x) ∈ A ↔ x ∈ A
      simp
    exact ⟨eV v, fun h => hv ((hT v).2 h), A', (hP A A' hAA v).1 hA, (hI A A' hAA τ).1 hτ⟩
  have hbwd : ∀ σ', σ' ∈ NS Ω' T' → Φ.symm σ' ∈ NS Ω T := by
    intro σ' hσ'
    refine map_mem_closedNormal Φ.symm _ _ ?_ hσ'
    intro τ hτ
    simp only [Set.mem_iUnion] at hτ ⊢
    obtain ⟨v', hv', A', hA', hτ⟩ := hτ
    let A : ValuationSubring Ω := A'.comap (E : Ω →+* Ω')
    have hAA : ∀ x, E x ∈ A' ↔ x ∈ A := fun x => Iff.rfl
    refine ⟨eV.symm v', fun h => hv' ?_, A, ?_, ?_⟩
    · simpa using (hT _).1 h
    · refine (hP A A' hAA _).2 ?_
      simpa using hA'
    · refine (hI A A' hAA _).2 ?_
      simpa using hτ
  have hiff : ∀ σ, σ ∈ NS Ω T ↔ Φ σ ∈ NS Ω' T' := fun σ =>
    ⟨hfwd σ, fun h => by simpa using hbwd _ h⟩
  exact ⟨quotientIso Φ (NS Ω T) (NS Ω' T') hiff, fun σ => rfl⟩

end GlobalTheory.CompanionTheory.PTIso
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsoOfThickeningsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_of_thickenings : IsoOfThick := by
  first | exact @GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick | exact GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick | (intros; apply GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KaehlerFreeConeRingStatement
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kaehler_free_cone_ring : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)), Module.Free (R0 K n d S) Ω[R0 K n d S⁄K] := by
  first | exact @GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om | exact GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om | (intros; apply GlobalTheory.CompanionTheory.SurjectionOntoH4.FreeOm.free_om <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEquivCohomologyOfQuasiIsomorphismStatement
section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_equiv_cohomology_of_quasi_isomorphism : ∀ (S P₀ P₁ P₂ T B₀ B₁ B₂ : Type) [CommRing S] [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂] [AddCommGroup T] [Module S T] [AddCommGroup B₀] [Module S B₀] [AddCommGroup B₁] [Module S B₁] [AddCommGroup B₂] [Module S B₂] (a₀ : P₀ →ₗ[S] P₁) (a₁ : P₁ →ₗ[S] P₂) (π : P₁ →ₗ[S] T) (dT : T →ₗ[S] P₂) (Z : Submodule S B₁) (dB : B₀ →ₗ[S] Z) (b₁ : B₁ →ₗ[S] B₂) (f : P₁ →ₗ[S] B₁) (ψ₀ : P₀ →ₗ[S] B₀), Function.Surjective π → Function.Exact a₀ π → dT ∘ₗ π = a₁ → (∀ z, z ∈ Z ↔ b₁ z = 0) → (∀ x, a₁ x = 0 → b₁ (f x) = 0) → (∀ y, f (a₀ y) = (dB (ψ₀ y) : B₁)) → QIsoAt a₀ a₁ (Z.subtype ∘ₗ dB) b₁ f → Nonempty (LinearMap.ker dT ≃ₗ[S] Z ⧸ LinearMap.range dB) := by
  first | exact @GlobalTheory.CompanionTheory.PerfKerCoh.ker_equiv_cohomology | exact GlobalTheory.CompanionTheory.PerfKerCoh.ker_equiv_cohomology | (intros; apply GlobalTheory.CompanionTheory.PerfKerCoh.ker_equiv_cohomology <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeCocyclesLiftToNerve
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC.LowDict

theorem exists_quot_equiv {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (K : Submodule R M) (Z : Submodule R N) (hK : ∀ x, x ∈ K ↔ e x ∈ Z)
    (BK : Submodule R K) (BZ' : Submodule R Z)
    (hB : ∀ (x : K) (f : Z), e x.1 = f.1 → (x ∈ BK ↔ f ∈ BZ')) :
    ∃ u : (Z ⧸ BZ') ≃ₗ[R] (K ⧸ BK),
      (∀ (f : Z) (x : K), e x.1 = f.1 → u (BZ'.mkQ f) = BK.mkQ x) ∧ ∀ f : Z, ∃ x : K, e x.1 = f.1 := by
  have hmap : K.map (e : M →ₗ[R] N) = Z := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hK x).1 hx
    · intro hy
      exact ⟨e.symm y, (hK _).2 (by simpa using hy), by simp⟩
  let v : K ≃ₗ[R] Z := e.ofSubmodules K Z hmap
  have hv : ∀ x : K, (v x).1 = e x.1 := fun _ ↦ rfl
  have hq : BZ'.map (v.symm : Z →ₗ[R] K) = BK := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine (hB _ f ?_).2 hf
      rw [← hv]
      simp
    · intro hx
      exact ⟨v x, (hB x (v x) (hv x).symm).1 hx, by simp⟩
  refine ⟨Submodule.Quotient.equiv BZ' BK v.symm hq, fun f x h ↦ ?_, fun f ↦ ⟨v.symm f, ?_⟩⟩
  · have hx : v.symm f = x := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext h.symm
    rw [← hx]
    rfl
  · rw [← hv]
    simp

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

theorem d2_apply (z : C2 F) {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    d2 F z T T' T'' T''' φ ψ χ = z T' T'' T''' ψ χ - z T T'' T''' (φ ≫ ψ) χ + z T T' T''' φ (ψ ≫ χ) -
      mp F χ (z T T' T'' φ ψ) := rfl

theorem Z2_eq_ker : Z2 F = LinearMap.ker (d2 F) := by
  ext z
  refine ⟨fun h ↦ ?_, fun h T T' T'' T''' φ ψ χ ↦ ?_⟩
  · refine LinearMap.mem_ker.2 ?_
    funext T T' T'' T''' φ ψ χ
    rw [d2_apply]
    have := h φ ψ χ
    simp only [Pi.zero_apply]
    linear_combination -this
  · have := congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (congrFun (LinearMap.mem_ker.1 h) T) T') T'') T''') φ) ψ) χ
    rw [d2_apply] at this
    simp only [Pi.zero_apply] at this
    linear_combination -this

theorem dict_low : DictSt → ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    ∃ (u₁ : H1 F ≃ₗ[R] HH F 1) (u₂ : H2 F ≃ₗ[R] HH F 2), IsIdealValuedLiftSystemCocycle F u₁.toLinearMap ∧ IsDegreeTwoComparison F u₂.toLinearMap ∧
      (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) ∧
      (∀ f : Z2 F, ∃ x : Zc F 2, ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
        x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) := by
  intro hD R _ C _ F
  obtain ⟨e₀, e₁, e₂, e₃, v₀, v₁, v₂, -, h₀, h₁, h₂⟩ := hD R C F
  have k₁ : ∀ x, x ∈ Zc F 1 ↔ e₁ x ∈ Z1 F := fun x ↦ by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker, LinearMap.mem_ker, ← h₁, LinearEquiv.map_eq_zero_iff]
  have k₂ : ∀ x, x ∈ Zc F 2 ↔ e₂ x ∈ Z2 F := fun x ↦ by
    rw [Z2_eq_ker, LinearMap.mem_ker, LinearMap.mem_ker, ← h₂, LinearEquiv.map_eq_zero_iff]
  have b₁ : ∀ (x : Zc F 1) (f : Z1 F), e₁ x.1 = f.1 →
      (x ∈ BZ F 1 ↔ f ∈ LinearMap.range ((d0 F).codRestrict (Z1 F) (commAlgFunctorCoboundaryZero_mem_cocyclesOne F))) := fun x f hxf ↦ by
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨e₀ g, Subtype.ext ?_⟩
      rw [LinearMap.codRestrict_apply, ← h₀, hg]
      exact hxf
    · rintro ⟨g, hg⟩
      refine ⟨e₀.symm g, e₁.injective ?_⟩
      rw [h₀, LinearEquiv.apply_symm_apply]
      exact (congrArg Subtype.val hg).trans hxf.symm
  have b₂ : ∀ (x : Zc F 2) (f : Z2 F), e₂ x.1 = f.1 →
      (x ∈ BZ F 2 ↔ f ∈ LinearMap.range ((d1 F).codRestrict (Z2 F) (differential_one_mem_scaled_lattice F))) := fun x f hxf ↦ by
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨e₁ g, Subtype.ext ?_⟩
      rw [LinearMap.codRestrict_apply, ← h₁, hg]
      exact hxf
    · rintro ⟨g, hg⟩
      refine ⟨e₁.symm g, e₂.injective ?_⟩
      rw [h₁, LinearEquiv.apply_symm_apply]
      exact (congrArg Subtype.val hg).trans hxf.symm
  obtain ⟨u₁, c₁, s₁⟩ := exists_quot_equiv e₁ (Zc F 1) (Z1 F) k₁ (BZ F 1) _ b₁
  obtain ⟨u₂, c₂, s₂⟩ := exists_quot_equiv e₂ (Zc F 2) (Z2 F) k₂ (BZ F 2) _ b₂
  refine ⟨u₁, u₂, fun f x hx ↦ c₁ f x ?_, fun f x hx ↦ c₂ f x ?_, fun f ↦ ?_, fun f ↦ ?_⟩
  · funext T T' φ
    exact (v₁ x.1 T T' φ).trans (hx T T' φ)
  · funext T T' T'' φ ψ
    exact (v₂ x.1 T T' T'' φ ψ).trans (hx T T' T'' φ ψ)
  · obtain ⟨x, hx⟩ := s₁ f
    exact ⟨x, fun T T' φ ↦ (v₁ x.1 T T' φ).symm.trans (congrFun (congrFun (congrFun hx T) T') φ)⟩
  · obtain ⟨x, hx⟩ := s₂ f
    exact ⟨x, fun T T' T'' φ ψ ↦ (v₂ x.1 T T' T'' φ ψ).symm.trans
      (congrFun (congrFun (congrFun (congrFun (congrFun hx T) T') T'') φ) ψ)⟩

end GlobalTheory.CompanionTheory.HopfC.LowDict
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowDegreeComparisonIndependentOfChoice
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.HopfC

namespace GlobalTheory.CompanionTheory.HopfC

theorem mk₁_comp_functor {C D : Type} [Category.{0} C] [Category.{0} D] (G : C ⥤ D) {T T' : C} (φ : T ⟶ T') :
    (ComposableArrows.mk₁ φ ⋙ G : ComposableArrows D 1) = ComposableArrows.mk₁ (G.map φ) :=
  ComposableArrows.ext₁ rfl rfl (by show G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _; simp)

theorem mk₂_comp_functor {C D : Type} [Category.{0} C] [Category.{0} D] (G : C ⥤ D) {T T' T'' : C}
    (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (ComposableArrows.mk₂ φ ψ ⋙ G : ComposableArrows D 2) = ComposableArrows.mk₂ (G.map φ) (G.map ψ) :=
  ComposableArrows.ext₂ rfl rfl rfl (by show G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _; simp)
    (by show G.map ψ = 𝟙 _ ≫ G.map ψ ≫ 𝟙 _; simp)

theorem dictionary_pull : ∀ {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (F' : C' ⥤ CommAlgCat.{0} R) (m : CoefMap (RingHom.id R) F F') (u₁ : H1 F →ₗ[R] HH F 1) (u₁' : H1 F' →ₗ[R] HH F' 1) (u₂ : H2 F →ₗ[R] HH F 2) (u₂' : H2 F' →ₗ[R] HH F' 2), IsIdealValuedLiftSystemCocycle F u₁ → IsIdealValuedLiftSystemCocycle F' u₁' → IsDegreeTwoComparison F u₂ → IsDegreeTwoComparison F' u₂' → (∀ f : Z1 F, ∃ x : Zc F 1, ∀ (T T' : C) (φ : T ⟶ T'), x.1 (ComposableArrows.mk₁ φ) = f.1 T T' φ) → (∀ f : Z2 F, ∃ x : Zc F 2, ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), x.1 (ComposableArrows.mk₂ φ ψ) = f.1 T T' T'' φ ψ) → (∀ c, u₁' (m.pull1 c) = pullH m 1 (u₁ c)) ∧ (∀ c, u₂' (m.pull2 c) = pullH m 2 (u₂ c)) := by
  intro R _ C C' _ _ F F' m u₁ u₁' u₂ u₂' h1 h1' h2 h2' e1 e2
  refine ⟨fun c ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    obtain ⟨x, hx⟩ := e1 f
    rw [h1 f x hx, pullH_mk, CoefMap.pullCohomologyOne_class]
    refine h1' _ _ fun T T' φ ↦ ?_
    have e : x.1 (ComposableArrows.mk₁ φ ⋙ m.G) = x.1 (ComposableArrows.mk₁ (m.G.map φ)) :=
      eq_of_heq (congr_arg_heq x.1 (mk₁_comp_functor m.G φ))
    exact (congrArg (m.α T') (e.trans (hx _ _ _)))
  · obtain ⟨f, rfl⟩ := H2.mk_surjective F c
    obtain ⟨x, hx⟩ := e2 f
    rw [h2 f x hx, pullH_mk, CoefMap.pullCohomologyTwo_class]
    refine h2' _ _ fun T T' T'' φ ψ ↦ ?_
    have e : x.1 (ComposableArrows.mk₂ φ ψ ⋙ m.G) = x.1 (ComposableArrows.mk₂ (m.G.map φ) (m.G.map ψ)) :=
      eq_of_heq (congr_arg_heq x.1 (mk₂_comp_functor m.G φ ψ))
    exact (congrArg (m.α T'') (e.trans (hx _ _ _ _ _)))

end GlobalTheory.CompanionTheory.HopfC
end
end

