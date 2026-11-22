import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0022
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0225

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousGaloisLatticeMatrixIntegral
section
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem exists_form_extending_coord {R F T V ι : Type} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] [AddCommGroup T] [Module R T] [AddCommGroup V] [Module R V]
    [Module F V] [IsScalarTower R F V] (b : Module.Basis ι R T) (f : T →ₗ[R] V)
    (hf : Function.Injective f) (i : ι) :
    ∃ φ : V →ₗ[F] F, ∀ x, φ (f x) = algebraMap R F (b.repr x i) := by
  classical
  set v : ι → V := fun j => f (b j) with hv
  have hR : LinearIndependent R v := b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hF : LinearIndependent F v := (LinearIndependent.iff_fractionRing R F).mp hR
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hF).coord i)
  refine ⟨g, fun x => ?_⟩
  have hx : f x = ∑ j ∈ (b.repr x).support, algebraMap R F (b.repr x j) • v j := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, algebraMap_smul]
  have hy : f x = ((∑ j ∈ (b.repr x).support,
      algebraMap R F (b.repr x j) • Module.Basis.span hF j : Submodule.span F (Set.range v)) : V) := by
    rw [hx, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul, Module.Basis.span_apply]
  have h2 := LinearMap.congr_fun hg
    (∑ j ∈ (b.repr x).support, algebraMap R F (b.repr x j) • Module.Basis.span hF j)
  rw [LinearMap.comp_apply, Submodule.subtype_apply] at h2
  rw [hy, h2, map_sum]
  simp only [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [Finsupp.mem_support_iff, not_not] at h
    rw [h, map_zero]

theorem continuous_form_of_moduleTopology {F L V : Type} [NontriviallyNormedField F]
    [CompleteSpace F] [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L]
    [IsTopologicalRing L] [T2Space L] [ContinuousSMul F L] [AddCommGroup V] [Module L V]
    [Module F V] [IsScalarTower F L V] [TopologicalSpace V] [IsModuleTopology L V]
    [FiniteDimensional L V] (φ : V →ₗ[F] F) : Continuous φ := by
  let e := (Module.finBasis L V).equivFun
  have he : Continuous e.toLinearMap := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  let ψ : (Fin (Module.finrank L V) → L) →ₗ[F] F := φ ∘ₗ (e.symm.toLinearMap.restrictScalars F)
  have hψ : Continuous ψ := LinearMap.continuous_of_finiteDimensional ψ
  have h : (φ : V → F) = ψ ∘ e.toLinearMap := by
    funext v
    simp [ψ]
  rw [h]
  exact hψ.comp he

variable {l : ℕ} [Fact l.Prime]

def zCHom (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* PadicComplex l :=
  (algebraMap ℚ_[l] (PadicComplex l)).comp (algebraMap ℤ_[l] ℚ_[l])

theorem zCHom_apply (x : ℤ_[l]) : zCHom l x = zC x := rfl

section Generic

variable {G R F L O : Type} [Group G] [TopologicalSpace G] [CommRing R] [Field F] [Field L]
  [Algebra F L] [CommRing O] [Algebra O L] [TopologicalSpace L] [Algebra R O]

def mulLat (R : Type) [CommRing R] [Algebra R O] (T : LocLat G F L O) (a : O) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ↥T.L.T →ₗ[R] ↥T.L.T :=
  letI := Module.compHom ↥T.L.T (algebraMap R O)
  { toFun := fun x => ⟨_, T.L.T.smul_mem a x.2⟩
    map_add' := fun x y => smul_add a x y
    map_smul' := fun c x => smul_comm a (algebraMap R O c) x }

theorem mulLat_apply (T : LocLat G F L O) (a : O) (x : ↥T.L.T) :
    mulLat R T a x = ⟨_, T.L.T.smul_mem a x.2⟩ := rfl

theorem coe_actT (T : LocLat G F L O) (g : G) (x : ↥T.L.T) :
    (actT T.L g x).1 = T.ρ g x.1 := rfl

theorem actT_mulLat (T : LocLat G F L O) (g : G) (a : O) (x : ↥T.L.T) :
    actT T.L g (mulLat R T a x) = mulLat R T a (actT T.L g x) := by
  rw [mulLat_apply, mulLat_apply]
  exact (actT T.L g).map_smul a x

theorem exists_basis_lat [Nontrivial R] [Module.Free R O] [Module.Finite R O]
    (T : LocLat G F L O) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∃ d : ℕ, Nonempty (Module.Basis (Fin d) R ↥T.L.T) := by
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  have : IsScalarTower R O ↥T.L.T := ⟨fun r o x => by
    show (r • o) • x = algebraMap R O r • (o • x)
    rw [Algebra.smul_def, mul_smul]⟩
  have : Module.Free O ↥T.L.T := T.L.free
  have : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  have : Module.Free R ↥T.L.T :=
    Module.Free.of_basis ((Module.Free.chooseBasis R O).smulTower (Module.Free.chooseBasis O ↥T.L.T))
  have : Module.Finite R ↥T.L.T := Module.Finite.trans O ↥T.L.T
  exact ⟨_, ⟨Module.finBasis R ↥T.L.T⟩⟩

theorem exists_form_lat [IsDomain R] [Algebra R F] [IsFractionRing R F]
    (hc : ∀ c : R, algebraMap O L (algebraMap R O c) = algebraMap F L (algebraMap R F c))
    (T : LocLat G F L O) {ι : Type} :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ (b : Module.Basis ι R ↥T.L.T) (i : ι),
      ∃ φ : T.V →ₗ[F] F, ∀ x : ↥T.L.T, φ x.1 = algebraMap R F (b.repr x i) := by
  intro b i
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  let _ : Module R T.V := Module.compHom T.V (algebraMap R F)
  have : IsScalarTower R F T.V := ⟨fun r c v => by
    show (r • c) • v = algebraMap R F r • (c • v)
    rw [Algebra.smul_def, mul_smul]⟩
  let f : ↥T.L.T →ₗ[R] T.V :=
    { toFun := fun x => x.1
      map_add' := fun x y => rfl
      map_smul' := fun r x => by
        show algebraMap R O r • x.1 = algebraMap R F r • x.1
        rw [← algebraMap_smul L (algebraMap R O r) x.1, hc, algebraMap_smul] }
  exact exists_form_extending_coord b f Subtype.val_injective i

def actLat (R : Type) [CommRing R] [Algebra R O] (T : LocLat G F L O) (g : G) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ↥T.L.T →ₗ[R] ↥T.L.T :=
  letI := Module.compHom ↥T.L.T (algebraMap R O)
  { toFun := actT T.L g
    map_add' := map_add _
    map_smul' := fun c x => (actT T.L g).map_smul (algebraMap R O c) x }

theorem matrices_lat {C : Type} [CommRing C] (z : R →+* C) (T : LocLat G F L O) {d : ℕ}
    (M : G → Matrix (Fin d) (Fin d) C) (A : O → Matrix (Fin d) (Fin d) C) :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ b : Module.Basis (Fin d) R ↥T.L.T,
      (∀ g i j, M g i j = z (b.repr (actT T.L g (b j)) i)) →
      (∀ a i j, A a i j = z (b.repr (⟨_, T.L.T.smul_mem a (b j).2⟩ : ↥T.L.T) i)) →
      (∀ g h, M (g * h) = M g * M h) ∧ M 1 = 1 ∧ ∀ g a, M g * A a = A a * M g := by
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  intro b hM hA
  have kM : ∀ g, M g = (LinearMap.toMatrix b b (actLat R T g)).map z := by
    intro g; ext i j; rw [hM, Matrix.map_apply, LinearMap.toMatrix_apply]; rfl
  have kA : ∀ a, A a = (LinearMap.toMatrix b b (mulLat R T a)).map z := by
    intro a; ext i j; rw [hA, Matrix.map_apply, LinearMap.toMatrix_apply]; rfl
  have hmul : ∀ g h, actLat R T (g * h) = actLat R T g * actLat R T h := by
    intro g h
    refine LinearMap.ext fun x => Subtype.ext ?_
    show T.ρ (g * h) x.1 = T.ρ g (T.ρ h x.1)
    rw [map_mul]; rfl
  have hone : actLat R T 1 = 1 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    show T.ρ 1 x.1 = x.1
    rw [map_one]; rfl
  have hcomm : ∀ g a, actLat R T g * mulLat R T a = mulLat R T a * actLat R T g :=
    fun g a => LinearMap.ext fun x => actT_mulLat (R := R) T g a x
  refine ⟨fun g h => ?_, ?_, fun g a => ?_⟩
  · rw [kM, kM, kM, hmul, LinearMap.toMatrix_mul, Matrix.map_mul]
  · rw [kM, hone, LinearMap.toMatrix_one]
    exact Matrix.map_one _ z.map_zero z.map_one
  · rw [kM, kA, ← Matrix.map_mul, ← Matrix.map_mul, ← LinearMap.toMatrix_mul,
      ← LinearMap.toMatrix_mul, hcomm]

end Generic

theorem continuous_coord_lat {G R F L O : Type} [Group G] [TopologicalSpace G] [CommRing R]
    [NontriviallyNormedField F] [CompleteSpace F] [Field L] [Algebra F L] [CommRing O]
    [Algebra O L] [TopologicalSpace L] [Algebra R O] [FiniteDimensional F L]
    [IsTopologicalRing L] [T2Space L] [ContinuousSMul F L]
    [IsDomain R] [Algebra R F] [IsFractionRing R F]
    (hc : ∀ c : R, algebraMap O L (algebraMap R O c) = algebraMap F L (algebraMap R F c))
    (T : LocLat G F L O) {ι : Type} :
    letI := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ (b : Module.Basis ι R ↥T.L.T) (x : ↥T.L.T) (i : ι),
      Continuous fun g : G => algebraMap R F (b.repr (actT T.L g x) i) := by
  intro b x i
  let _ : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  obtain ⟨φ, hφ⟩ := exists_form_lat (R := R) hc T b i
  have hφc : Continuous φ := continuous_form_of_moduleTopology (L := L) φ
  have h : (fun g : G => algebraMap R F (b.repr (actT T.L g x) i)) = fun g => φ (T.ρ g x.1) := by
    funext g
    rw [← hφ, coe_actT]
  rw [h]
  exact hφc.comp (T.cont x.1)

theorem exists_basis_lattice {G : Type} [Group G] [TopologicalSpace G] (LL : FinExt l)
    (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    letI := zlMod LL T
    ∃ d : ℕ, Nonempty (Module.Basis (Fin d) ℤ_[l] ↥T.L.T) := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure ℤ_[l] ↥LL.1
  have : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] (↥LL.1) (↥(OL LL))
  have : Module.IsTorsionFree ℤ_[l] ↥LL.1 := Module.IsTorsionFree.trans_faithfulSMul ℤ_[l] ℚ_[l] _
  have : Module.Free ℤ_[l] ↥(OL LL) :=
    IsIntegralClosure.module_free ℤ_[l] ℚ_[l] (↥LL.1) (↥(OL LL))
  exact exists_basis_lat (R := ℤ_[l]) T

theorem isMat_exists_and_props : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∃ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A) ∧ ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → (∀ i j, ContinuousOn (fun σ => M σ i j) (GK K)) ∧ (∀ σ ∈ GK K, ∀ τ ∈ GK K, M (σ * τ) = M σ * M τ) ∧ M 1 = 1 ∧ (∀ σ ∈ GK K, ∀ a, M σ * A a = A a * M σ) := by
  intro l _ K LL T
  classical
  let _ : Module ℤ_[l] ↥T.L.T := zlMod LL T
  have hc : ∀ c : ℤ_[l], algebraMap (↥(OL LL)) (↥LL.1) (algebraMap ℤ_[l] (↥(OL LL)) c) =
      algebraMap ℚ_[l] (↥LL.1) (algebraMap ℤ_[l] ℚ_[l] c) := fun c => rfl
  refine ⟨?_, ?_⟩
  · obtain ⟨d, ⟨b⟩⟩ := exists_basis_lattice (G := ↥(GK K)) LL T
    refine ⟨d, fun σ => Matrix.of fun i j =>
        if h : σ ∈ GK K then zC (b.repr (actT T.L ⟨σ, h⟩ (b j)) i) else 0,
      fun a => Matrix.of fun i j => zC (b.repr (⟨_, T.L.T.smul_mem a (b j).2⟩ : ↥T.L.T) i),
      b, fun g i j => ?_, fun a i j => rfl⟩
    show (if h : (g : GQ l) ∈ GK K then zC (b.repr (actT T.L ⟨g, h⟩ (b j)) i) else 0) = _
    exact dif_pos g.2
  · intro d M A hMA
    obtain ⟨b, hM, hA⟩ := hMA
    have key := matrices_lat (R := ℤ_[l]) (F := ℚ_[l]) (L := ↥LL.1) (zCHom l) T
      (fun g : ↥(GK K) => M g) A b (fun g i j => (hM g i j).trans (zCHom_apply _).symm)
      (fun a i j => (hA a i j).trans (zCHom_apply _).symm)
    refine ⟨fun i j => ?_, fun σ hσ τ hτ => key.1 ⟨σ, hσ⟩ ⟨τ, hτ⟩, key.2.1,
      fun σ hσ a => key.2.2 ⟨σ, hσ⟩ a⟩
    rw [continuousOn_iff_continuous_domRestrict]
    have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    have h1 := continuous_coord_lat (R := ℤ_[l]) (F := ℚ_[l]) (L := ↥LL.1) (O := ↥(OL LL)) hc T b
      (b j) i
    have h2 : Continuous (algebraMap ℚ_[l] (PadicComplex l)) := continuous_algebraMap _ _
    refine (h2.comp h1).congr fun g => ?_
    exact ((hM ⟨g.1, g.2⟩ i j).trans (zCHom_apply _).symm).symm

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContinuousNormCharLFunctionNeZeroOne
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

namespace GlobalTheory
namespace NormCharL

theorem norm_cast_eq_one (K : Type) [Field K] [NumberField K] (m : ℕ) (β : 𝓞 K)
    (h : β - 1 ∈ Ideal.span {(m : 𝓞 K)}) : ((Algebra.norm ℤ β : ℤ) : ZMod m) = 1 := by
  obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.1 h
  have hβ : β = 1 + (m : 𝓞 K) * γ := by rw [mul_comm, hγ]; ring
  let b := Module.Free.chooseBasis ℤ (𝓞 K)
  have key : (Int.castRingHom (ZMod m)).mapMatrix (Algebra.leftMulMatrix b β) = 1 := by
    rw [hβ, map_add, map_one, map_mul, map_natCast, map_add, map_one, map_mul, map_natCast]
    ext i j
    simp [Matrix.one_apply]
  have h2 := (Int.castRingHom (ZMod m)).map_det (Algebra.leftMulMatrix b β)
  rw [key, Matrix.det_one, ← Algebra.norm_eq_matrix_det] at h2
  simpa using h2

theorem sup_eq_top_iff (K : Type) [Field K] [NumberField K] (m : ℕ) (hm : m.Prime)
    (I : Ideal (𝓞 K)) : I ⊔ Ideal.span {(m : 𝓞 K)} = ⊤ ↔ ¬ m ∣ Ideal.absNorm I := by
  constructor
  · intro h hdvd
    obtain ⟨i, hi, y, hy, hiy⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 h)
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    have hmem : i - 1 ∈ Ideal.span {(m : 𝓞 K)} := by
      rw [Ideal.mem_span_singleton']
      exact ⟨-z, by rw [← hiy]; ring⟩
    have h1 := GlobalTheory.NormCharL.norm_cast_eq_one K m i hmem
    have hd : Ideal.absNorm I ∣ (Algebra.norm ℤ i).natAbs := by
      rw [← Ideal.absNorm_span_singleton]
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hi)
    have hz : ((Algebra.norm ℤ i : ℤ) : ZMod m) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Int.natCast_dvd.2 (hdvd.trans hd)
    rw [hz] at h1
    have : Fact m.Prime := ⟨hm⟩
    exact zero_ne_one h1
  · intro h
    have hc : Nat.Coprime (Ideal.absNorm I) m := (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hm).2 h))
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hc
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 K) = (u : 𝓞 K) * (Ideal.absNorm I : 𝓞 K) + (v : 𝓞 K) * (m : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) huv
      push_cast at this
      exact this.symm
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem I)))
      (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

theorem exists_continuous_ne_zero_one :
    ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → ∀ (χ : (ZMod m)ˣ →* ℂˣ) (cl : HeightOneSpectrum (𝓞 K) → (ZMod m)ˣ), (∀ P, ¬ m ∣ Ideal.absNorm P.asIdeal → (cl P : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ)) → (∃ P, ¬ m ∣ Ideal.absNorm P.asIdeal ∧ χ (cl P) ≠ 1) → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s → Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - ((χ (cl P) : ℂˣ) : ℂ) * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-(s : ℂ)))) = L s := by
  intro K _ _ m hm χ cl hcl hχ
  have : Fact m.Prime := ⟨hm⟩
  set M : Ideal (𝓞 K) := Ideal.span {(m : 𝓞 K)} with hMdef
  let ψ : ZMod m → ℂ := fun x => if h : x = 0 then 0 else ((χ (Units.mk0 x h) : ℂˣ) : ℂ)
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  have hψmul : ∀ x y, ψ (x * y) = ψ x * ψ y := by
    intro x y
    by_cases hx : x = 0
    · simp [ψ, hx]
    by_cases hy : y = 0
    · simp [ψ, hy]
    have hxy : x * y ≠ 0 := mul_ne_zero hx hy
    simp only [ψ, dif_neg hx, dif_neg hy, dif_neg hxy]
    rw [← Units.val_mul, ← map_mul]
    congr 3
    ext
    simp
  have hψunit : ∀ u : (ZMod m)ˣ, ψ (u : ZMod m) = ((χ u : ℂˣ) : ℂ) := by
    intro u
    simp only [ψ, dif_neg u.ne_zero]
    congr 3
    ext
    simp
  let X : Ideal (𝓞 K) → ℂ := fun I => ψ (Ideal.absNorm I : ZMod m)
  have hcop : ∀ I : Ideal (𝓞 K), I ⊔ M = ⊤ ↔ (Ideal.absNorm I : ZMod m) ≠ 0 := by
    intro I
    rw [GlobalTheory.NormCharL.sup_eq_top_iff K m hm I, Ne, ZMod.natCast_eq_zero_iff]
  have hM0 : M ≠ ⊥ := by
    rw [hMdef, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hm.ne_zero
  have hX0 : X ⊥ = 0 := by simp [X, hψ0]
  have hXmul : ∀ I J, X (I * J) = X I * X J := by
    intro I J
    simp only [X, map_mul, Nat.cast_mul, hψmul]
  have hXnorm : ∀ I, I ≠ ⊥ → I ⊔ M = ⊤ → ‖X I‖ = 1 := by
    intro I _ hI
    have hne := (hcop I).1 hI
    simp only [X, ψ, dif_neg hne]
    exact GlobalTheory.Mem.RayPrimes.norm_char χ _
  have hXzero : ∀ I, I ⊔ M ≠ ⊤ → X I = 0 := by
    intro I hI
    have : (Ideal.absNorm I : ZMod m) = 0 := by
      by_contra h
      exact hI ((hcop I).2 h)
    simp [X, this, hψ0]
  set ε : ℂ := ((χ (-1) : ℂˣ) : ℂ) with hε
  have hεε : ε * ε = 1 := by
    rw [hε, ← Units.val_mul, ← map_mul]
    simp
  obtain ⟨φ, hφmul, hφhom, hφsm, hφnorm, hφβ⟩ := GlobalTheory.T.exists_mixedSpace_norm_sign_character K ε hεε
  have hXφ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ M → X (Ideal.span {β}) = φ (mixedEmbedding K β) := by
    intro β hβ0 hβ1
    rw [hφβ β hβ0]
    have h1 := GlobalTheory.NormCharL.norm_cast_eq_one K m β hβ1
    have hN0 : Algebra.norm ℤ β ≠ 0 := by
      rw [Ne, Algebra.norm_eq_zero_iff]
      exact hβ0
    simp only [X, Ideal.absNorm_span_singleton]
    split_ifs with hpos
    · have : (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod m) = 1 := by
        rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos.le, h1]
      rw [this, ← Units.val_one, hψunit]
      simp
    · have hneg : Algebra.norm ℤ β ≤ 0 := le_of_not_gt hpos
      have : (((Algebra.norm ℤ β).natAbs : ℕ) : ZMod m) = ((-1 : (ZMod m)ˣ) : ZMod m) := by
        rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos hneg, Int.cast_neg, h1]
        simp
      rw [this, hψunit]
  obtain ⟨P, hPm, hPχ⟩ := hχ
  have hPtop : P.asIdeal ⊔ M = ⊤ := (GlobalTheory.NormCharL.sup_eq_top_iff K m hm P.asIdeal).2 hPm
  have hclX (Q : HeightOneSpectrum (𝓞 K)) (hQ : ¬ m ∣ Ideal.absNorm Q.asIdeal) :
      X Q.asIdeal = ((χ (cl Q) : ℂˣ) : ℂ) := by
    show ψ (Ideal.absNorm Q.asIdeal : ZMod m) = _
    rw [← hcl Q hQ, hψunit]
  have hnt : ∃ J, J ≠ ⊥ ∧ J ⊔ M = ⊤ ∧ X J ≠ 1 := by
    refine ⟨P.asIdeal, P.ne_bot, hPtop, ?_⟩
    rw [hclX P hPm]
    intro h
    exact hPχ (Units.val_eq_one.1 h)
  let c : HeightOneSpectrum (𝓞 K) → ℂ := fun Q => ((χ (cl Q) : ℂˣ) : ℂ)
  have hc : ∀ Q, ‖c Q‖ ≤ 1 := fun Q => (GlobalTheory.Mem.RayPrimes.norm_char χ (cl Q)).le
  have hcX : ∀ Q : HeightOneSpectrum (𝓞 K), ¬ M ≤ Q.asIdeal → c Q = X Q.asIdeal := by
    intro Q hQ
    have hmax : Q.asIdeal.IsMaximal := Q.isMaximal
    have htop : Q.asIdeal ⊔ M = ⊤ := by
      refine hmax.1.2 _ (lt_of_le_of_ne le_sup_left ?_)
      intro h
      exact hQ (h ▸ le_sup_right)
    rw [hclX Q ((GlobalTheory.NormCharL.sup_eq_top_iff K m hm Q.asIdeal).1 htop)]
  obtain ⟨L, hLd, hLe, hL1⟩ := GlobalTheory.idealCharacterL_continuation_ne_zero_one K M X φ hM0 hX0 hXmul
    hXnorm hXzero hφmul hφhom hφsm hφnorm hXφ hnt c hc hcX
  refine ⟨fun z => L ((max z.re 1 : ℝ) : ℂ), ?_, ?_, ?_⟩
  · refine hLd.continuousOn.comp_continuous (by fun_prop) (fun z => ?_)
    show (0 : ℝ) < ((max z.re 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    exact lt_of_lt_of_le one_pos (le_max_right _ _)
  · simpa using hL1
  · intro s hs
    have hmax : max (s : ℂ).re 1 = s := by
      rw [Complex.ofReal_re]
      exact max_eq_left hs.le
    simp only [hmax]
    exact (hLe s (by rwa [Complex.ofReal_re])).symm

end NormCharL
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamTensorCoordinatesOfBasis
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem exists_tensor_coord_of_basis {k V M : Type} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup M] [Module k M] {d : ℕ} (bV : Module.Basis (Fin d) k V) :
    ∃ Φ : V ⊗[k] M ≃ₗ[k] (Fin d → M), (∀ (v : V) (b : M) (i : Fin d), Φ (v ⊗ₜ b) i = bV.repr v i • b) ∧
      ∀ z, z = ∑ i, bV i ⊗ₜ[k] Φ z i := by
  classical
  let Φ : V ⊗[k] M ≃ₗ[k] (Fin d → M) :=
    (TensorProduct.congr bV.equivFun (LinearEquiv.refl k M)).trans
      ((TensorProduct.comm k _ _).trans (TensorProduct.piScalarRight k k M (Fin d)))
  have h : ∀ (v : V) (b : M) (i : Fin d), Φ (v ⊗ₜ b) i = bV.repr v i • b := by
    intro v b i
    simp [Φ]
  refine ⟨Φ, h, fun z => ?_⟩
  apply Φ.injective
  funext j
  rw [map_sum, Finset.sum_apply]
  simp only [h, Module.Basis.repr_self]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Finsupp.single_apply, hij]
  · simp

theorem exists_coord_tensor_dR : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), ∃ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (a : ℤ) (z : V ⊗[Qp] BdR), z ∈ FilV PD (LL := LL) (V := V) a ↔ ∀ i, Φ z i ∈ PD.Fil a) ∧ ∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i)) := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ d bV
  obtain ⟨Φ, h, hz⟩ := exists_tensor_coord_of_basis (M := BdR) bV
  refine ⟨Φ, fun a z => ⟨?_, fun H => ?_⟩, fun g z => ?_⟩
  · rintro ⟨w, rfl⟩ i
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      rw [AlgebraTensorModule.map_tmul, h]
      exact ((PD.Fil a).restrictScalars Qp).smul_mem _ b.2
    | add x y hx hy =>
      rw [map_add, map_add, Pi.add_apply]
      exact add_mem hx hy
  · rw [hz z]
    refine Submodule.sum_mem _ fun i _ => ⟨bV i ⊗ₜ ⟨Φ z i, H i⟩, ?_⟩
    rw [AlgebraTensorModule.map_tmul]
    rfl
  · have hact : ∀ (v : V) (b : BdR), actVdR PD ρ g (v ⊗ₜ b) = ρ g v ⊗ₜ PD.actdR g b := by
      intro v b
      unfold actVdR
      rw [AlgebraTensorModule.map_tmul]
      rfl
    funext i
    conv_lhs => rw [hz z]
    rw [map_sum, map_sum, Finset.sum_apply]
    simp only [hact, h, Matrix.mulVec, dotProduct, Matrix.of_apply, Algebra.smul_def]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedCharacterOfEigenUnitStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_character_of_eigen_unit : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (x : P.R.B), IsUnit x → (∀ g : ↥(GK K), ∃ a : ↥(K0 K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B a * x) → ∃ c : ↥(GK K) →* (↥(K0 K))ˣ, ∀ g : ↥(GK K), P.actQ (g : GQ l) x = algebraMap ↥(K0 K) P.R.B ((c g : (↥(K0 K))ˣ) : ↥(K0 K)) * x := by
  first | exact @GlobalTheory.ltChar_hom | exact GlobalTheory.ltChar_hom | (intros; apply GlobalTheory.ltChar_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittTiltLatticeTensorCancelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wittTilt_lattice_tensor_cancel : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), letI := Formalism.MainNotions.LocalSituation.zlMod LL T; ∃ κ : (WCb l ⊗[ℤ_[l]] ↥T.L.T) ≃+ TW (RW LL) T, ∀ (w : WCb l) (t : ↥T.L.T), κ (w ⊗ₜ[ℤ_[l]] t) = TensorProduct.tmul ↥(OL LL) ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] w : RW LL) t := by
  first | exact @GlobalTheory.HWL.exists_kappa | exact GlobalTheory.HWL.exists_kappa | (intros; apply GlobalTheory.HWL.exists_kappa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteJumpsInfFiltrationStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_setOf_inf_filtration_ne_succ : ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W), Module.Finite E ↥D → (∀ a, F (a + 1) ≤ F a) → {a : ℤ | D ⊓ F (a + 1) ≠ D ⊓ F a}.Finite := by
  first | exact @GlobalTheory.finite_jumps_inf_filtration | exact GlobalTheory.finite_jumps_inf_filtration | (intros; apply GlobalTheory.finite_jumps_inf_filtration <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankPeriodFunctorCoeffBaseChangeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_periodFunctor_coeff_baseChange : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) (LL LL' : Type) [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL'] [FiniteDimensional LL LL'] (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [AddCommGroup V'] [Module LL' V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V'] (ρ : Representation LL G V) (ρ' : Representation LL' G V') (j : V →ₗ[LL] V'), IsBaseChange LL' j → (∀ g x, j (ρ g x) = ρ' g (j x)) → finrank LL' V' = finrank LL V ∧ finrank LL' ↥(H0V ρ') = finrank LL ↥(H0V ρ) ∧ (finrank LL' ↥(Dcris PD ρ') = finrank LL ↥(Dcris PD ρ) ∧ (Module.Finite LL' ↥(Dcris PD ρ') ↔ Module.Finite LL ↥(Dcris PD ρ))) ∧ (finrank LL' ↥(DdR PD ρ') = finrank LL ↥(DdR PD ρ) ∧ (Module.Finite LL' ↥(DdR PD ρ') ↔ Module.Finite LL ↥(DdR PD ρ))) ∧ (∀ a : ℤ, finrank LL' ↥(DdR PD ρ' ⊓ FilV PD (LL := LL') (V := V') a) = finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)) ∧ (∀ τ : K₀ →ₐ[Qp] LL, finrank LL' ↥(DcrisL PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DcrisL PD ρ τ)) ∧ ∀ τ : K →ₐ[Qp] LL, finrank LL' ↥(DdRE PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ)) = finrank LL ↥(DdRE PD ρ τ) ∧ ∀ a : ℤ, finrank LL' ↥(FildR PD ρ' ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a) = finrank LL ↥(FildR PD ρ τ a) := by
  first | exact @GlobalTheory.CoeffBC.finrank_baseChange | exact GlobalTheory.CoeffBC.finrank_baseChange | (intros; apply GlobalTheory.CoeffBC.finrank_baseChange <;> assumption)
end

