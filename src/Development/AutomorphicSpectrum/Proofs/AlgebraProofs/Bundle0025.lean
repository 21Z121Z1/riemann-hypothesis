import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0015
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0021
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphIdealFibreChartDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0022
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0006
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0015
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0008
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.CharacterDataBaseChange
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0008
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelFacts
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0018

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeIntOfProjectiveRingOfIntegers
section
open NumberField TensorProduct GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem finite_int_of_finite_ringOfIntegers (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L]
    [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] : Module.Finite ℤ L :=
  Module.Finite.trans (𝓞 E) L

theorem free_int_of_projective_ringOfIntegers (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L]
    [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] : Module.Free ℤ L := by
  haveI : Module.Finite ℤ L := finite_int_of_finite_ringOfIntegers E L
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective (𝓞 E) L)
  have hinj : Function.Injective s := fun x y hxy => by
    have := congrArg (Finsupp.linearCombination (𝓞 E) id) hxy
    simpa using (LinearMap.congr_fun hs x).symm.trans (this.trans (LinearMap.congr_fun hs y))
  haveI : Module.IsTorsionFree ℤ (L →₀ 𝓞 E) := inferInstance
  haveI : Module.IsTorsionFree ℤ L :=
    hinj.moduleIsTorsionFree (R := ℤ) s fun r m => by simp
  infer_instance

theorem proIso_of_unimodular_alternating :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (L L' : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L'] [Module.Finite (𝓞 E) L'] [Module.Projective (𝓞 E) L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), Module.finrank (𝓞 E) L = Module.finrank (𝓞 E) L' → (∀ x, B x x = 0) → Function.Bijective B → (∀ (a : 𝓞 E) x y, B (a • x) y = B x (bar a • y)) → (∀ x, B' x x = 0) → Function.Bijective B' → (∀ (a : 𝓞 E) x y, B' (a • x) y = B' x (bar a • y)) → Nonempty (ProIso (𝓞 E) B B') := by
  intro E _ _ _ bar hbar hun L L' _ _ _ _ _ _ _ _ B B' hrk hB hBb hBa hB' hBb' hBa'
  haveI : Module.Finite ℤ L := finite_int_of_finite_ringOfIntegers E L
  haveI : Module.Finite ℤ L' := finite_int_of_finite_ringOfIntegers E L'
  haveI : Module.Free ℤ L := free_int_of_projective_ringOfIntegers E L
  haveI : Module.Free ℤ L' := free_int_of_projective_ringOfIntegers E L'
  refine GlobalTheory.T.pro_isometry_of_local_isometries (𝓞 E) L L' B B' fun p hp => ?_
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, h1, h2⟩ := GlobalTheory.T.cm_projective_module_pairing_p E bar hbar hun p L L' B B' hrk hB hBb hBa hB' hBb' hBa'
  exact GlobalTheory.T.padic_isometry_equivariance p (𝓞 E) L L' B B' φ h1 h2

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GraphIdealFibreChartDegreeStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graph_ideal_fibre_chart_degree : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (P : Ideal (MRing ι)) (g : (Σ k, ι₂ k) → MRing ι), P.IsPrime → (∀ k₂, ∃ j, g ⟨k₂, j⟩ ∉ P) → imageZ inlV (graphIdeal P g) = P → ∀ (G : GenFibre inlV (graphIdeal P g)) (i : ∀ k, fibreIdx (Sum.elim ι ι₂) (Sum.inl : K → K ⊕ K₂) k), IsChart (fibreIdeal Sum.inl G) i → ptDeg (fibreIdeal Sum.inl G) i = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.GrDeg.graph_generic_fibre_ptDeg | exact GlobalTheory.CompanionTheory.Ar.Giv.GrDeg.graph_generic_fibre_ptDeg | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.GrDeg.graph_generic_fibre_ptDeg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeAnnihilatorLatticeHolds
section
namespace GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_stdLat_iff_algebra (R : Subalgebra o Ω) {ι : Type} (v : ι → Ω) :
    v ∈ stdLat R ι ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem linMap_mem_stdLat {F : Type} [Zero F] [Fintype F] {n : ℕ} (R : Subalgebra o Ω) (χ : F → Ω)
    (hχ : ∀ a, χ a ∈ R) (v : Fin n → Ω) (hv : v ∈ stdLat R (Fin n)) :
    linMap n χ v ∈ stdLat R (Fin n → F) := by
  rw [mem_stdLat_iff_algebra] at hv ⊢
  intro x
  simp only [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hv i) (hχ _)

theorem hodge_annihilator_lattice {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F]
    [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω)
    (p : ℕ) (w : Ω) (χ : Sg → F → Ω) (hC : CharData R p w χ) (hB : D.Base R p w) (hp : p.Prime)
    (hN : IsNoetherianRing R) (hF : IsFractionRing R Ω) (hI : IsIntegrallyClosedIn R Ω)
    (φ : Equiv.Perm Sg) (hT : D.TestFacts R p w χ φ) (hG : D.Good₁ R p χ) (τ : Sg) :
    mulLat w (stdLat R _) ≤ D.af R p (χ τ) := by
  have H := GlobalTheory.T.lattice_good_base_change D R p w χ hC hB hG
  obtain ⟨hp0, hwR, -, -, hχ⟩ := hC
  intro x hx
  obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.mp hx
  have hu' : ∀ i, u i ∈ R := (mem_stdLat_iff_algebra R u).mp hu
  refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI n (D.af R p (χ τ)) (H.1 τ).1 _ ⟨1, ?_⟩ ?_
  · have hy : linMap n (χ τ) (w • u) ∈ stdLat R (Fin n → F) :=
      linMap_mem_stdLat R (χ τ) (hχ τ).2.2 _ ((mem_stdLat_iff_algebra R _).mpr fun i => by
        simpa using R.mul_mem hwR (hu' i))
    rw [LieLatticeData.af, AddSubgroup.mem_comap]
    refine AddSubgroup.mem_sup_right (AddSubgroup.mem_map.mpr ⟨_, hy, ?_⟩)
    simp [map_smul]
  · intro C _ _ _ _ RC hTP
    have hRC : ∀ a ∈ R, algebraMap Ω C a ∈ RC := hTP.2.2.2
    rw [← ((H.2 C RC hRC).2 τ).1]
    have hFa := hT C RC hTP
    refine hFa.le_af τ (AddSubgroup.mem_map.mpr ⟨bcMap Ω C (Fin n) u, ?_, ?_⟩)
    · exact (mem_stdLat_iff_algebra RC _).mpr fun i => by simpa [bcMap] using hRC _ (hu' i)
    · ext i
      simp [bcMap]

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDifferentGenerators
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem gram_integral_unit_mod : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (σ : E →+* K) (d : A), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → ∃ G H Z Z' : Matrix (Fin N) (Fin N) A, (∀ i j, algebraMap A K (G i j) = D.gram σ d i j) ∧ G * H = 1 + ((p : A) ^ R) • Z ∧ H * G = 1 + ((p : A) ^ R) • Z' :=
  @PositivityTheory.HtPt.Ga.gram_unit

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDivisibility
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem q_onto_eigenpart_mod_pow : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (m : ℕ), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → (∀ x, D.q σ x ∈ D.omHT σ) ∧ (D.omHT σ).FG ∧ ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y' :=
  PositivityTheory.HtPt.Ga.q_surj

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateLatticeBaseChangePairingStatement
section
open GlobalTheory.CompanionTheory.Ar.HT NumberField TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_lattice_base_change_pairing : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p R N : ℕ) (W Ω : Type) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Projective A W] [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (j : W →ₗ[A] Ω), IsBaseChange K j → ∀ (ρ : 𝓞 E →+* Module.End A W) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)) (h : (Fin N → 𝓞 E) →+ W), (∀ x, e x x = 0) → (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y)) → (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → (∀ (a : 𝓞 E) x, ∃ y, h (a • x) = ρ a (h x) + (p ^ R) • y) → ∃ D : HTChart A K c p R N Ω, D.om = LinearMap.range j ∧ D.e = e ∧ (∀ x, D.h x = j (h x)) ∧ ∀ a w, D.ρΩ a (j w) = j (ρ a w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.htChart_of_projective_module | exact GlobalTheory.CompanionTheory.Ar.HT.htChart_of_projective_module | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.htChart_of_projective_module <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderIdealsEqTop
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hopf_order_ideals_eq_top : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (t : N), t ∉ K → GenAF p AA.carrier K.toAddSubgroup → ∀ χ : MulChar F R, idealX AA.carrier K t χ = ⊤ → ∃ τ : MulChar F R, IsFund p τ ∧ idealD p AA.carrier K t τ = ⊤ := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc N _ _ _ _ AA hFS K t ht hGen χ hχ
  haveI : Nontrivial R := (algebraMap R C).domain_nontrivial
  have hval : ∀ g ∈ AA.carrier, ∀ x, ∃ r : R, algebraMap R C r = g x := fun g hg =>
    (show ∀ x, ∃ r : R, algebraMap R C r = g x from AA.le_int hg)
  have hle : ∀ g ∈ AA.carrier, ∀ x, v (g x) ≤ 1 := by
    intro g hg x
    obtain ⟨r, hr⟩ := hval g hg x
    rw [← hr]
    exact hv.map_le_one r
  have hpv : ∀ z ∈ pInt (C := C) R p, v z < 1 := by
    intro z hz
    unfold pInt at hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    rw [Algebra.smul_def, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hv.map_le_one a)) hp
  have hinv : ∀ g, g ∈ invFun AA.carrier K.toAddSubgroup →
      g ∈ AA.carrier ∧ ∀ x, ∀ k ∈ K.toAddSubgroup, g (x + k) = g x := fun g hg => hg
  have hinvI : ∀ g, (g ∈ AA.carrier ∧ ∀ x, ∀ k ∈ K.toAddSubgroup, g (x + k) = g x) →
      g ∈ invFun AA.carrier K.toAddSubgroup := fun g hg => hg
  have hadd : ∀ g, g ∈ addFun (C := C) R p N →
      ∀ x y, g (x + y) - g x - g y ∈ pInt (C := C) R p := fun g hg => hg
  have h1 : (1 : R) ∈ idealX AA.carrier K t χ := by
    rw [hχ]
    exact Submodule.mem_top
  obtain ⟨g0, hg0, hg0e⟩ := Submodule.mem_map.1
    (show LinearMap.toSpanSingleton R (F → C) (fun a => algebraMap R C (χ a)) 1 ∈
      stepOrder AA.carrier K t from h1)
  have hg0a : ∀ a : F, g0 (a • t) = algebraMap R C (χ a) := by
    intro a
    have := congrFun hg0e a
    simpa [LinearMap.funLeft_apply, LinearMap.toSpanSingleton_apply] using this
  have hg0t : g0 t = 1 := by simpa using hg0a 1
  have hg0z : g0 0 = 0 := by
    have e := hg0a 0
    rwa [zero_smul, MulChar.map_zero, map_zero] at e
  obtain ⟨h, hA, hh⟩ : ∃ h ∈ afFun p (invFun AA.carrier K.toAddSubgroup),
      ¬ v (h t - h 0) < 1 := by
    by_contra hcon
    push Not at hcon
    have key : ∀ φ ∈ Algebra.adjoin R
        ((afFun p (invFun AA.carrier K.toAddSubgroup) : Submodule R (N → C)) : Set (N → C)),
        φ ∈ AA.carrier ∧ v (φ t - φ 0) < 1 := by
      intro φ hφ
      induction hφ using Algebra.adjoin_induction with
      | mem x hx =>
        have hx' := Submodule.mem_inf.1 (SetLike.mem_coe.1 hx)
        exact ⟨(hinv x hx'.1).1, hcon x (SetLike.mem_coe.1 hx)⟩
      | algebraMap r =>
        refine ⟨?_, ?_⟩
        · rw [Algebra.algebraMap_eq_smul_one]
          exact AA.carrier.smul_mem r AA.one_mem
        · simp
      | add x y _ _ hx hy =>
        refine ⟨AA.carrier.add_mem hx.1 hy.1, ?_⟩
        have e : (x + y) t - (x + y) 0 = (x t - x 0) + (y t - y 0) := by
          simp only [Pi.add_apply]
          ring
        rw [e]
        exact v.map_add_lt hx.2 hy.2
      | mul x y _ _ hx hy =>
        refine ⟨AA.mul_mem x y hx.1 hy.1, ?_⟩
        have e : (x * y) t - (x * y) 0 = x t * (y t - y 0) + y 0 * (x t - x 0) := by
          simp only [Pi.mul_apply]
          ring
        rw [e]
        refine v.map_add_lt ?_ ?_
        · rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hle x hx.1 t)) hy.2
        · rw [map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hle y hy.1 0)) hx.2
    have hk := (key g0 ((show invFun AA.carrier K.toAddSubgroup ≤ _ from hGen) hg0)).2
    rw [hg0t, hg0z, sub_zero, map_one] at hk
    exact lt_irrefl _ hk
  have hAi := Submodule.mem_inf.1 hA
  obtain ⟨hM, hK⟩ := hinv h hAi.1
  have hAd := hadd h hAi.2
  obtain ⟨r0, hr0⟩ := hval h hM 0
  have h0p : h 0 ∈ pInt (C := C) R p := by
    have h00 := hAd 0 0
    rw [add_zero, show h 0 - h 0 - h 0 = -h 0 by ring] at h00
    simpa using (pInt (C := C) R p).neg_mem h00
  obtain ⟨h', h'apply, h'M⟩ : ∃ h' : N → C, (∀ x, h' x = h x - h 0) ∧ h' ∈ AA.carrier :=
    ⟨h - r0 • (1 : N → C), fun x => by
      show h x - (r0 • (1 : N → C)) x = h x - h 0
      rw [Pi.smul_apply, Pi.one_apply, Algebra.smul_def, mul_one, hr0],
      AA.carrier.sub_mem hM (AA.carrier.smul_mem r0 AA.one_mem)⟩
  have h'z : h' 0 = 0 := by rw [h'apply, sub_self]
  have h'inv : h' ∈ invFun AA.carrier K.toAddSubgroup :=
    hinvI h' ⟨h'M, fun x k hk => by rw [h'apply, h'apply, hK x k hk]⟩
  have h'add : h' ∈ addFun (C := C) R p N := by
    show ∀ x y, h' (x + y) - h' x - h' y ∈ pInt (C := C) R p
    intro x y
    have e : h' (x + y) - h' x - h' y = (h (x + y) - h x - h y) + h 0 := by
      rw [h'apply, h'apply, h'apply]
      ring
    rw [e]
    exact (pInt (C := C) R p).add_mem (hAd x y) h0p
  have h'af : h' ∈ afFun p AA.carrier := by
    unfold afFun
    exact Submodule.mem_inf.2 ⟨h'M, h'add⟩
  have h'aug : h' ∈ augIdeal AA.carrier := by
    unfold augIdeal
    exact Submodule.mem_inf.2 ⟨h'M, by simp [LinearMap.mem_ker, h'z]⟩
  have h't : ¬ v (h' t) < 1 := by
    rw [h'apply]
    exact hh
  obtain ⟨σ, hσ⟩ := PositivityTheory.HtPt.Rb.fund_ex p C v R hv hp F f hc
  obtain ⟨P1, P2, P3, P4, -⟩ :=
    PositivityTheory.HtPt.Rb.proj_props p C v R hv hp F f hc N AA hFS σ hσ h' h'aug
  obtain ⟨m, -, hm⟩ : ∃ m ∈ Finset.Icc 1 (p ^ f - 1), ¬ v (proj (σ ^ m) h' t) < 1 := by
    by_contra hcon
    push Not at hcon
    apply h't
    rw [P2, Finset.sum_apply]
    exact v.map_sum_lt one_ne_zero hcon
  have hτ : IsFund p (σ ^ m) := by
    by_contra hnf
    have hpf := PositivityTheory.HtPt.Rb.proj_nf p C v R hv hp F f hc N AA hFS h' h'af (σ ^ m) hnf
    exact hm (hpv _ (PositivityTheory.HtPt.Rb.mem_pFun.1 hpf t))
  refine ⟨σ ^ m, hτ, ?_⟩
  have hgE : proj (σ ^ m) h' ∈ AA.carrier ∧ ∀ (a : F) x,
      proj (σ ^ m) h' (a • x) = algebraMap R C ((σ ^ m) a) * proj (σ ^ m) h' x := P1 (σ ^ m)
  have hgI := hinv _ (P4 K h'inv (σ ^ m))
  have hgA : proj (σ ^ m) h' ∈ afFun p AA.carrier := P3 h'af (σ ^ m)
  generalize proj (σ ^ m) h' = g at hgE hgI hgA hm
  obtain ⟨u, hu⟩ := hval g hgE.1 t
  have hvu : v (algebraMap R C u) = 1 := by
    rw [hu]
    exact le_antisymm (hle g hgE.1 t) (not_lt.1 hm)
  have huU : IsUnit u := by
    refine hv.isUnit_of_one (isUnit_iff_ne_zero.2 ?_) hvu
    intro h0
    rw [h0, map_zero] at hvu
    exact zero_ne_one hvu
  have hg0' : g 0 = 0 := by
    have e := hgE.2 0 0
    rwa [zero_smul, MulChar.map_zero, map_zero, zero_mul] at e
  refine (Ideal.eq_top_iff_one _).2 ?_
  show ∃ G ∈ afFun p AA.carrier,
    (∀ (a : F) x, G (a • x) - algebraMap R C ((σ ^ m) a) * G x ∈ pInt (C := C) R p) ∧
    (∀ k ∈ K, G k ∈ pInt (C := C) R p) ∧ G t - algebraMap R C 1 ∈ pInt (C := C) R p
  refine ⟨(↑huU.unit⁻¹ : R) • g, (afFun p AA.carrier).smul_mem _ hgA, ?_, ?_, ?_⟩
  · intro a x
    have e : ((↑huU.unit⁻¹ : R) • g) (a • x) - algebraMap R C ((σ ^ m) a) *
        ((↑huU.unit⁻¹ : R) • g) x = 0 := by
      simp only [Pi.smul_apply, hgE.2 a x, Algebra.smul_def]
      ring
    rw [e]
    exact Submodule.zero_mem _
  · intro k hk
    have hgk : g k = 0 := by
      have e := hgI.2 0 k hk
      rwa [zero_add, hg0'] at e
    simp [hgk]
  · have e : ((↑huU.unit⁻¹ : R) • g) t - algebraMap R C 1 = 0 := by
      rw [Pi.smul_apply, Algebra.smul_def, ← hu, ← map_mul, huU.val_inv_mul, sub_self]
    rw [e]
    exact Submodule.zero_mem _
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderPullbackAlongHomStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_pullback_along_hom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (A' : HopfOrder (C := C) R N') (j : N →+ N'), (∀ g ∈ A'.carrier, (fun x => g (j x)) ∈ AA.carrier) → (∀ g ∈ AA.carrier, (∀ k ∈ j.ker, g k = 0) → g ∈ (augIdeal A'.carrier).map (LinearMap.funLeft R C (j : N → N')) * AA.carrier) → A'.carrier.map (LinearMap.funLeft R C (j : N → N')) = invFun AA.carrier j.ker := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hopf_order_pullback_along_hom | exact GlobalTheory.CompanionTheory.Relay.hopf_order_pullback_along_hom | (intros; apply GlobalTheory.CompanionTheory.Relay.hopf_order_pullback_along_hom <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeBaseChangeLargerRingHolds
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem lattice_base_change_larger_ring : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → CharData RC p (algebraMap Ω C w) (fun τ a => algebraMap Ω C (χ τ a)) ∧ (D.bc RC).Base RC p (algebraMap Ω C w) :=
  @PositivityTheory.Xgn.character_data_base_change

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamiliesGlueToBundle
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily

theorem main : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V], (∀ Γ : (∀ k, ι k) → AddSubgroup V, IsLatFamily O x Γ → (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) → ∃ E : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧ ∀ E : ChartBundle O (mseg x) N V, IsLatFamily O x E.lat ∧ ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) :=
  @PositivityTheory.Xgn.t_bundle_of_family

end GlobalTheory.CompanionTheory.Ar.Num.BundleOfFamily
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelFactsStatement
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_family_injective_model_facts : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) ∧ ∀ τ, IsLatFamily O x (fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ (∀ i, IsLatFamily O x (fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) ∧ IsLatFamily O x (fun c => (D c).stepGraph τ (fun a => algebraMap O Ω (χ τ a)) i)) ∧ (∀ i, IsLatFamily O x (fun c => (D c).kk τ i)) ∧ IsLatFamily O x (fun c => dotDual (chartRing O (mseg x) c) ((D c).lie τ)) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → IsLatFamily O x (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ IsLatFamily O x (fun c => (D c).imH (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamConstr.main | exact GlobalTheory.CompanionTheory.Ar.Num.FamConstr.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamConstr.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeImageBaseChange
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeImageBaseChange

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

theorem map_snd_spanOver {o C V Z Vc Zc : Type} [CommRing o] [Field C] [Algebra o C]
    (RC : Subalgebra o C) [AddCommGroup V] [AddCommGroup Z] [AddCommGroup Vc] [AddCommGroup Zc]
    [Module C Vc] [Module C Zc] (b : V → Vc) (b' : Z → Zc) (G : AddSubgroup (V × Z)) :
    (spanOver RC (Prod.map b b' '' G)).map (AddMonoidHom.snd Vc Zc) =
      spanOver RC (b' '' G.map (AddMonoidHom.snd V Z)) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, b' y.2, ⟨y.2, AddSubgroup.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hz
    exact ⟨a • Prod.map b b' y, ⟨a, ha, Prod.map b b' y, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩

theorem hh_le_divLat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] {n : ℕ}
    {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω)
    (χ : F → Ω) (hw : mulLat w (stdLat R _) ≤ D.af R p χ) :
    D.hh R p χ ≤ divLat w (stdLat R (Fin n)) := by
  intro v hv
  change v ∈ dotDual R (D.af R p χ) at hv
  unfold dotDual at hv
  simp only [divLat, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply]
  rw [stdLat, AddSubgroup.mem_pi]
  intro i _
  have he : (Pi.single i (1 : Ω) : Fin n → Ω) ∈ stdLat R (Fin n) := by
    rw [stdLat, AddSubgroup.mem_pi]
    intro j _
    rw [Pi.single_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  have hwe : w • (Pi.single i (1 : Ω) : Fin n → Ω) ∈ D.af R p χ :=
    hw (AddSubgroup.mem_map_of_mem (DistribMulAction.toAddMonoidHom (Fin n → Ω) w) he)
  have h := AddSubgroup.mem_iInf.mp
    (AddSubgroup.mem_iInf.mp hv (w • (Pi.single i (1 : Ω) : Fin n → Ω))) hwe
  have h2 : (w • (Pi.single i (1 : Ω) : Fin n → Ω)) ⬝ᵥ v ∈ R := h
  have h3 : (w • v) i = (w • (Pi.single i (1 : Ω) : Fin n → Ω)) ⬝ᵥ v := by
    simp [dotProduct, Pi.single_apply]
  show (w • v) i ∈ R
  rw [h3]
  exact h2

theorem imH_bc : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.imH R p τ (χ τ)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hB hG hw C _ _ _ _ RC hR τ
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨hp, -, ⟨c, -, hpc⟩, -⟩ := hc
    exact hp (by rw [hpc, mul_zero])
  have hfst : (D.Del τ).map (AddMonoidHom.fst _ _) = divLat w (stdLat R (Fin n)) := by
    ext b
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨⟨b', c⟩, h, rfl⟩
      exact ((hB.del τ).1 b').mp ⟨c, h⟩
    · intro h
      obtain ⟨c, hcc⟩ := ((hB.del τ).1 b).mpr h
      exact ⟨(b, c), hcc, rfl⟩
  have hstab : ∀ a ∈ R, ∀ v ∈ D.hh R p (χ τ), a • v ∈ D.hh R p (χ τ) := by
    intro a ha v hv
    change v ∈ dotDual R (D.af R p (χ τ)) at hv
    change a • v ∈ dotDual R (D.af R p (χ τ))
    unfold dotDual at hv ⊢
    rw [AddSubgroup.mem_iInf]
    intro l
    rw [AddSubgroup.mem_iInf]
    intro hl
    have h1 : l ⬝ᵥ v ∈ R := AddSubgroup.mem_iInf.mp (AddSubgroup.mem_iInf.mp hv l) hl
    have h2 : l ⬝ᵥ (a • v) = a * (l ⬝ᵥ v) := by
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    show l ⬝ᵥ (a • v) ∈ R
    rw [h2]
    exact R.mul_mem ha h1
  have hhh : (D.bc RC).hh RC p (fun a => algebraMap Ω C (χ τ a)) =
      spanOver RC (bcMap Ω C (Fin n) '' D.hh R p (χ τ)) :=
    (((GlobalTheory.T.lattice_good_base_change D R p w χ hc hB hG).2 C RC hR).2 τ).2.1
  have key := (GlobalTheory.T.locally_free_base_change_quotient R RC hR (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ)))
    (isBaseChange_bcMap Ω C _) (isBaseChange_bcMap Ω C _) (D.Del τ) (D.hh R p (χ τ)) n
    (fun a ha v hv => (hB.stable τ a ha).2.1 v hv)
    (by rw [hfst]; exact locFree_divLat R hw0 (locFree_stdLat R n))
    (by rw [hfst]; exact hh_le_divLat D R p w (χ τ) (hw τ)) hstab).1
  have hDel : (D.bc RC).Del τ =
      spanOver RC (Prod.map (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ))) '' D.Del τ) := rfl
  unfold LieLatticeData.imH
  rw [hhh, hDel, key]
  exact map_snd_spanOver RC _ _ _

end GlobalTheory.CompanionTheory.Ar.Num.LatticeImageBaseChange
end
end

