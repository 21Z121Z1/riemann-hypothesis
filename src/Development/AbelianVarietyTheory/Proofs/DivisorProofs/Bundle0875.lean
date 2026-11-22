import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
import Formalism.PolynomialDimension.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0861
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreActionPreservesAdelicMatrices
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibAdel

open Formalism.HermitianLatticesTheory (localization₂)

section General

variable {K : Type} [Field K] [NumberField K]

theorem valuation_eq_one_of_vAdd (w : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) (h : vAdd w x = 0) :
    w.valuation K x = 1 := by
  unfold vAdd at h
  have h0 : w.valuation K x ≠ 0 := by simpa using hx
  rw [← WithZero.exp_log h0, neg_eq_zero.mp h, WithZero.exp_zero]

theorem kron_mul {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)] {R : Type} [CommRing R]
    (M M' : ∀ t, Matrix (J t) (J t) R) : kron M * kron M' = kron fun t => M t * M' t := by
  ext I I''
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun I' _ => ?_
  rw [Finset.prod_mul_distrib]

theorem kron_one {T : Type} [Fintype T] [DecidableEq T] {J : T → Type} [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)]
    {R : Type} [CommRing R] : (kron fun t => (1 : Matrix (J t) (J t) R)) = 1 := by
  first
  | exact @_root_.GlobalTheory.KroneckerIdentity.kron_identity
  | exact _root_.GlobalTheory.KroneckerIdentity.kron_identity
  | (apply _root_.GlobalTheory.KroneckerIdentity.kron_identity <;> assumption)
  | (intros; apply _root_.GlobalTheory.KroneckerIdentity.kron_identity <;> assumption)
  | (intros; apply @_root_.GlobalTheory.KroneckerIdentity.kron_identity <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.KroneckerIdentity.kron_identity ..)

theorem rhoMat_mul {n : ℕ} (la : Fin n → ℕ) (g h : Matrix (Fin n) (Fin n) K) :
    rhoMat la g * rhoMat la h = rhoMat la (h * g) := by
  rw [GlobalTheory.DefPt.rhoMat, GlobalTheory.DefPt.rhoMat, GlobalTheory.DefPt.rhoMat, Matrix.transpose_mul, map_mul, LinearMap.toMatrix_mul]

theorem rhoMat_one {n : ℕ} (la : Fin n → ℕ) : rhoMat la (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [GlobalTheory.DefPt.rhoMat, Matrix.transpose_one, map_one, LinearMap.toMatrix_one]

theorem exists_int_scale (w : HeightOneSpectrum (𝓞 K)) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {M : Matrix ι κ K} (hM : IntAt w M) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ A : Matrix ι κ (𝓞 K),
      A.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • M := by
  have h1 : ∀ p : ι × κ, ∃ r : 𝓞 K, ∃ d ∈ w.asIdeal.primeCompl,
      M p.1 p.2 * algebraMap (𝓞 K) K d = algebraMap (𝓞 K) K r := fun p => by
    obtain ⟨r, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer (M p.1 p.2) (hM p.1 p.2)
    exact ⟨r, d, d.2, h⟩
  choose r d hd h using h1
  refine ⟨∏ p, d p, Submonoid.prod_mem _ fun p _ => hd p,
    Matrix.of fun i j => (∏ p ∈ Finset.univ.erase (i, j), d p) * r (i, j), ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, map_mul, ← h]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)), map_mul]
  ring

theorem valuation_repr_le_one (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} {la : Fin n → ℕ} {f : nabla la K}
    (hf : f ∈ localization₂ w.asIdeal (stdLat la K)) (i : Idx la) : w.valuation K ((basis la K).repr f i) ≤ 1 := by
  obtain ⟨s, hs, hf⟩ := hf
  rw [stdLat_eq_span, Submodule.mem_span_range_iff_exists_fun] at hf
  obtain ⟨c, hc⟩ := hf
  have hc' : ∑ i, (algebraMap (𝓞 K) K (c i)) • basis la K i = (algebraMap (𝓞 K) K s) • f := hc
  have h1 := congrArg (fun x => (basis la K).repr x i) hc'
  simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
  have h2 : w.valuation K (algebraMap (𝓞 K) K s) = 1 := (w.valuation_eq_one_iff_notMem).2 hs
  have h3 : w.valuation K (algebraMap (𝓞 K) K (c i)) ≤ 1 := w.valuation_le_one (c i)
  rw [h1, map_mul, h2, one_mul] at h3
  exact h3

theorem intAt_rhoMat (w : HeightOneSpectrum (𝓞 K)) {n : ℕ} (la : Fin n → ℕ) {g : Matrix (Fin n) (Fin n) K}
    (hg : IntAt w g) : IntAt w (rhoMat la g) := by
  obtain ⟨t, ht, A, hA⟩ := exists_int_scale w (M := gᵀ) (fun i j => hg j i)
  intro i j
  have hj : basis la K j ∈ localization₂ w.asIdeal (stdLat la K) :=
    ⟨1, Submonoid.one_mem _, by rw [one_smul, stdLat_eq_span]; exact Submodule.subset_span ⟨j, rfl⟩⟩
  have h := rho_mem_locP w ht hA hj
  rw [GlobalTheory.DefPt.rhoMat, LinearMap.toMatrix_apply]
  exact valuation_repr_le_one w h i

theorem intAt_smul (w : HeightOneSpectrum (𝓞 K)) {ι κ : Type} [Fintype ι] [DecidableEq ι] {c : K}
    (hc : w.valuation K c ≤ 1) {M : Matrix ι κ K} (hM : IntAt w M) : IntAt w (c • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' hc (hM i j)

theorem intAt_kron (w : HeightOneSpectrum (𝓞 K)) {T : Type} [Fintype T] [DecidableEq T] {J : T → Type}
    [∀ t, Fintype (J t)] [∀ t, DecidableEq (J t)] {M : ∀ t, Matrix (J t) (J t) K} (hM : ∀ t, IntAt w (M t)) :
    IntAt w (kron M) := fun I I' => by
  rw [kron, Matrix.of_apply, map_prod]
  exact Finset.prod_le_one' fun t _ => hM t (I t) (I' t)

end General

theorem fibA_isAdelic : ∀ (K : Type) [Field K] [NumberField K] (T : Type) [Fintype T] [DecidableEq T] (N : T → ℕ)
    (la : ∀ t, Fin (N t) → ℕ) (a : HeightOneSpectrum (𝓞 K) → K)
    (B : HeightOneSpectrum (𝓞 K) → ∀ t, Matrix (Fin (N t)) (Fin (N t)) K), (∀ w, a w ≠ 0) →
    (Function.support fun w => vAdd w (a w)).Finite → (∀ t, IsAdelic fun w => B w t) →
    IsAdelic fun w => fibA la (a w) (B w) := by
  intro K _ _ T _ _ N la a B ha hfin hB
  have hinv : ∀ w, (a w)⁻¹ • kron (fun t => rhoMat (la t) (B w t)⁻¹) * fibA la (a w) (B w) = 1 := by
    intro w
    have e : ∀ t, rhoMat (la t) (B w t)⁻¹ * rhoMat (la t) (B w t) = 1 := fun t => by
      rw [rhoMat_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ((hB t).1 w)), rhoMat_one]
    rw [fibA, Matrix.smul_mul, Matrix.mul_smul, kron_mul, smul_smul, inv_mul_cancel₀ (ha w), one_smul]
    simp only [e]
    exact kron_one
  have hinv' : ∀ w, (fibA la (a w) (B w))⁻¹ = (a w)⁻¹ • kron (fun t => rhoMat (la t) (B w t)⁻¹) :=
    fun w => Matrix.inv_eq_left_inv (hinv w)
  refine ⟨fun w h => ?_, ?_⟩
  · have h1 := congrArg Matrix.det (hinv w)
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h1
    exact zero_ne_one h1
  · refine (hfin.union (Set.finite_iUnion fun t => (hB t).2)).subset fun w hw => ?_
    by_contra hw'
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, Function.mem_support, not_or, not_exists,
      not_not] at hw'
    obtain ⟨h0, h1⟩ := hw'
    have hv : w.valuation K (a w) = 1 := valuation_eq_one_of_vAdd w (ha w) h0
    refine hw ⟨intAt_smul w hv.le (intAt_kron w fun t => intAt_rhoMat w _ (h1 t).1), ?_⟩
    rw [hinv' w]
    exact intAt_smul w (by rw [map_inv₀, hv, inv_one]) (intAt_kron w fun t => intAt_rhoMat w _ (h1 t).2)

end GlobalTheory.FibAdel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.KS

namespace GlobalTheory.KS.PowPB

theorem powMap_pr {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) (i : Fin m) :
    powMap f φ hφ m ≫ (pr A i).left = (pr A' i).left ≫ φ := by
  unfold powMap
  rw [← Over.comp_left, Pi.lift_π]
  rfl

theorem powMap_w {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) :
    powMap f φ hφ m ≫ (pow A m).hom = (pow A' m).hom ≫ f := by
  unfold powMap
  exact Over.w _

theorem pow_left_hom_ext {S : Scheme.{0}} {A : Over S} {m : ℕ} {T : Scheme.{0}} (g₁ g₂ : T ⟶ (pow A m).left)
    (hh : g₁ ≫ (pow A m).hom = g₂ ≫ (pow A m).hom) (hi : ∀ i, g₁ ≫ (pr A i).left = g₂ ≫ (pr A i).left) :
    g₁ = g₂ := by
  let u₁ : Over.mk (g₁ ≫ (pow A m).hom) ⟶ pow A m := Over.homMk g₁ rfl
  let u₂ : Over.mk (g₁ ≫ (pow A m).hom) ⟶ pow A m := Over.homMk g₂ (by simpa using hh.symm)
  have : u₁ = u₂ := Pi.hom_ext _ _ (fun i => by
    ext
    simpa [u₁, u₂] using hi i)
  exact congrArg CommaMorphism.left this

noncomputable def liftPow {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) : T ⟶ (pow A' m).left :=
  (Pi.lift (fun i : Fin m => (Over.homMk (H.lift (a ≫ (pr A i).left) b (by rw [Category.assoc, Over.w]; exact w))
    (H.lift_snd _ _ _) : Over.mk b ⟶ A')) : Over.mk b ⟶ pow A' m).left

theorem liftPow_w {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) : liftPow H m a b w ≫ (pow A' m).hom = b := by
  unfold liftPow
  exact Over.w _

theorem liftPow_pr {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) (i : Fin m) :
    liftPow H m a b w ≫ (pr A' i).left = H.lift (a ≫ (pr A i).left) b (by rw [Category.assoc, Over.w]; exact w) := by
  unfold liftPow
  rw [← Over.comp_left, Pi.lift_π]
  rfl

theorem powMap_isPullback : ∀ (S S' : Scheme.{0}) (A : Over S) (A' : Over S') (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f), IsPullback φ A'.hom A.hom f →
    ∀ m : ℕ, IsPullback (powMap f φ hφ m) (pow A' m).hom (pow A m).hom f := by
  intro S S' A A' f φ hφ H m
  refine ⟨⟨powMap_w f φ hφ m⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => liftPow H m s.fst s.snd s.condition) ?_ ?_ ?_⟩⟩
  · intro s
    apply pow_left_hom_ext
    · rw [Category.assoc, powMap_w, ← Category.assoc, liftPow_w, s.condition]
    · intro i
      rw [Category.assoc, powMap_pr, ← Category.assoc, liftPow_pr, H.lift_fst]
  · intro s
    exact liftPow_w H m _ _ _
  · intro s u h₁ h₂
    apply pow_left_hom_ext
    · rw [h₂, liftPow_w]
    · intro i
      rw [liftPow_pr]
      apply H.hom_ext
      · rw [H.lift_fst, Category.assoc, ← powMap_pr f φ hφ, ← Category.assoc, h₁]
      · rw [H.lift_snd, Category.assoc, Over.w, h₂]

end GlobalTheory.KS.PowPB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleApproximationModConductor
section
open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.ApproxHatO

theorem exists_sub_mul_mem_hatO : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ (y : (Af E)ˣ) (z : Af E), ∃ x : E, (z - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  intro E _ _ _ c hc y z
  set N : ℕ := Ideal.absNorm c with hNdef
  have hN : N ≠ 0 := by rwa [hNdef, Ne, Ideal.absNorm_eq_zero_iff]
  have hNc : (N : OF E) ∈ c := Ideal.absNorm_mem c
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  set u : Af E := algebraMap E (Af E) (N : E)⁻¹ with hu
  set U : Set (Af E) := {a | ∀ v, (u * a * ((y⁻¹ : (Af E)ˣ) : Af E)) v ∈ v.adicCompletionIntegers E} with hU
  have hO : IsOpen {a : Af E | ∀ v, a v ∈ v.adicCompletionIntegers E} :=
    RestrictedProduct.isOpen_forall_mem
      (A := fun v : HeightOneSpectrum (𝓞 E) => (v.adicCompletionIntegers E : Set (v.adicCompletion E)))
      fun _ => Valued.isOpen_valuationSubring _
  have hV : IsOpen {x' : Af E | z - x' ∈ U} :=
    hO.preimage (((continuous_const.mul (continuous_const.sub continuous_id)).mul continuous_const))
  have hz : z ∈ {x' : Af E | z - x' ∈ U} := by
    show ∀ v, (u * (z - z) * ((y⁻¹ : (Af E)ˣ) : Af E)) v ∈ v.adicCompletionIntegers E
    intro v
    rw [sub_self, mul_zero, zero_mul]
    exact zero_mem _
  obtain ⟨x, hx⟩ := GlobalTheory.AdeleCharTwist.denseRange_fin.exists_mem_open hV ⟨z, hz⟩
  refine ⟨x, ?_⟩
  have key := GlobalTheory.CMVal.PicFin.mul_mem_hatO hNc (y := u * (z - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E)) hx
  have e : algebraMap E (Af E) (algebraMap (OF E) E (N : OF E)) * u = 1 := by
    rw [map_natCast, hu, ← map_mul, mul_inv_cancel₀ hNE, map_one]
  rwa [← mul_assoc, ← mul_assoc, e, one_mul] at key

end GlobalTheory.CMVal.ApproxHatO
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankSectionsPullbackFiniteFlatDegreeBounds
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

open FiniteCover

theorem finrank_sec_pull_sandwich_flat : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) [IsFinite φ] [Flat φ] [Surjective φ] (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, (∀ x : X, φ.finrank x = d) → (∀ t : ℕ, Module.Finite K (SecOnR f (pw H t) ⊤)) → (∀ t : ℕ, Module.Finite K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤)) → ∃ a : ℕ, ∀ t : ℕ, d * Module.finrank K (SecOnR (f) (pw H t) ⊤) ≤ Module.finrank K (SecOnR (φ ≫ f) ((pw H (t + a : ℕ)).pull φ) ⊤) ∧ Module.finrank K (SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) ≤ d * Module.finrank K (SecOnR (f) (pw H (t + a : ℕ)) ⊤) := by
  intro K _ X X' _ _ f φ _ _ _ H n s hH hs d hd hV hW
  have hd1 : 1 ≤ d := hd _ ▸ φ.one_le_finrank_map (genericPoint X')
  letI : Algebra X.functionField X'.functionField := (functionFieldMap φ).toAlgebra
  letI : Algebra K X.functionField := ((toField generic_top).comp (cst f ⊤)).toAlgebra
  letI : Algebra K X'.functionField := ((toField generic_top).comp (cst (φ ≫ f) ⊤)).toAlgebra
  haveI : IsScalarTower K X.functionField X'.functionField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      have w : φ ≫ f = (φ ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id K)) := by simp
      have e := toField_appLE φ (U := ⊤) (V := ⊤) le_top generic_top generic_top (cst f ⊤ r)
      exact (congrArg (toField generic_top)
        (appLE_cst w (V := ⊤) (V' := ⊤) le_top r)).symm.trans e
  obtain ⟨hcov, hs⟩ := hs
  choose haff r hr _ using hs
  let I := {i // genericPoint X ∈ nonzeroLocus (s i)}
  haveI : Fintype I := Fintype.ofFinite I
  let D : I → X.Opens := fun i => nonzeroLocus (s i.1)
  have hη : ∀ i, genericPoint X ∈ D i := fun i => i.2
  have hc : ⊤ ≤ ⨆ i, D i := fun x hx => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hcov.ge hx)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨i, generic_mem hi⟩, hi⟩
  have hc' : ⊤ ≤ ⨆ i, φ ⁻¹ᵁ D i := fun x _ => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc (trivial : φ x ∈ ⊤))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨i₀, -⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc generic_top)
  obtain ⟨k₀, h₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge generic_top)
  obtain ⟨x, hx⟩ := (chart_data φ (fun _ => rfl) (haff i₀.1) (hη i₀)).1
  rw [hd] at hx
  haveI : Module.Finite X.functionField X'.functionField :=
    Module.finite_of_finrank_pos (by omega)
  let e := Module.finBasisOfFinrankEq _ _ hx
  choose c hcm hc0 hc₁ hc₂ using fun i : I =>
    (chart_data φ (fun _ => rfl) (haff i.1) (hη i)).2 e
  let ρ : I → X.functionField := fun i => toField h₀ ((s i.1).f k₀)
  have hu : ∀ (i : I) k, IsUnit (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k)) :=
    fun i k => SecOn.isUnit_rs_of_le_nonzeroLocus _ k _ inf_le_left
  have hρ : ∀ i, ρ i ≠ 0 := fun i => by
    have := ((hu i k₀).map (toField (generic_inf (hη i) h₀))).ne_zero
    rwa [toField_rs] at this
  have hρr : ∀ i k : I, ρ i / ρ k = toField (hη k) (r k.1 i.1) := fun i k => by
    have := congrArg (toField (generic_inf (hη k) h₀)) (hr k.1 i.1 k₀)
    rw [map_mul, toField_rs, toField_rs, toField_rs] at this
    exact (div_eq_iff (hρ k)).2 this
  let τ : ∀ (t : ℕ) (i : I), SecOn (pw H t) (D i) := fun t i => GlobalTheory.LB.ofSec (powSec (s i.1) t) (D i)
  have hτc : ∀ (t : ℕ) (i : I) (k : H.ι), GlobalTheory.LB.coord (τ t i) k =
      rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k) ((s i.1).f k) ^ t := fun t i k =>
    (GlobalTheory.LB.coord_ofSec _ _ _).trans (map_pow (rs X (inf_le_right : D i ⊓ H.U k ≤ H.U k)) _ _)
  have hτ : ∀ (t : ℕ) (i : I) (k : H.ι), IsUnit (GlobalTheory.LB.coord (τ t i) k) := fun t i k =>
    (hτc t i k).symm ▸ (hu i k).pow t
  have hτv : ∀ (t : ℕ) (i : I), secVal (M := pw H t) (k₀ := k₀) h₀ (hη i) (τ t i) = ρ i ^ t :=
    fun t i => (congrArg (toField (generic_inf (hη i) h₀)) (hτc t i k₀)).trans (by
      rw [map_pow, toField_rs])
  have h₀' : ∀ t : ℕ, genericPoint X' ∈ ((pw H t).pull φ).U fun _ => k₀ := fun t =>
    le_pull (pw H t) φ (i := k₀) le_rfl (generic_mem_preimage φ h₀)
  refine finrank_sandwich e (fun i => (toField (hη i)).range)
    (fun i => (toField (generic_mem_preimage φ (hη i))).range) ρ c hρ hc0
    (fun i k => ⟨_, (hρr i k).symm⟩) (fun i k => ?_) ?_ hc₁ hc₂
    (fun t => SecOnR f (pw H t) ⊤) (fun t => SecOnR (φ ≫ f) ((pw H t).pull φ) ⊤) hV hW
    (fun t => secValLin (M := pw H t) (k₀ := k₀) h₀ f fun _ => rfl)
    (fun t => secValLin (h₀' t) (φ ≫ f) fun _ => rfl)
    (fun t => secVal_injective (M := pw H t) (k₀ := k₀) h₀ generic_top)
    (fun t => secVal_injective (h₀' t) generic_top) (fun t x => ?_) fun t y => ?_
  · obtain ⟨a, ha⟩ := hcm i
    rw [← ha, hρr]
    exact exists_mul_pow_mem (haff k.1) (hη k) (hη i) _
      (hρr i k ▸ div_ne_zero (hρ i) (hρ k)) (FiniteCover.basicOpen_le_nonzeroLocus _ _ _ (hr k.1 i.1)) a
  · rintro i _ ⟨a, rfl⟩
    exact ⟨_, toField_appLE φ le_rfl (hη i) _ a⟩
  · refine (exists_secVal_eq_iff (M := pw H t) (k₀ := k₀) h₀ (isLB_pw hH t) D hc hη (τ t) (hτ t)
      x).trans ?_
    simp only [hτv]
  · refine (exists_secVal_eq_iff (h₀' t) (LB.isLB_pull (isLB_pw hH t) φ) (fun i => φ ⁻¹ᵁ D i) hc'
      (fun i => generic_mem_preimage φ (hη i)) (fun i => SecOn.pull (pw H t) φ (D i) (τ t i))
      (fun i k => (hτ t i (k PUnit.unit)).map _) y).trans ?_
    refine forall_congr' fun i => ?_
    rw [secVal_pull (M := pw H t) (k₀ := k₀) h₀ φ (hη i), hτv]
    rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoefficientExtensionH2Class
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Obs GlobalTheory.LBLift
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PrimIdeal

variable {R : Type} [CommRing R] (I : Ideal R)

section Lin

variable (B : Type) [CommRing B] [Algebra R B]

def iota : I ⊗[R] B →ₗ[R] TrivSqZeroExt R I ⊗[R] B := (TrivSqZeroExt.inrHom R I).rTensor B

def tau : I ⊗[R] B →ₗ[R] B := TensorProduct.lid R B ∘ₗ I.subtype.rTensor B

def sig : TrivSqZeroExt R I ⊗[R] B →ₗ[R] B := tau I B ∘ₗ (TrivSqZeroExt.sndHom R I).rTensor B

theorem tau_tmul (i : I) (b : B) : tau I B (i ⊗ₜ b) = (i : R) • b := by
  simp [tau]

theorem sig_iota (y : I ⊗[R] B) : sig I B (iota I B y) = tau I B y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b => simp [sig, iota]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tau_mem (y : I ⊗[R] B) : tau I B y ∈ I.map (algebraMap R B) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b =>
    rw [tau_tmul, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ i.2)
  | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy

theorem sig_mem (x : TrivSqZeroExt R I ⊗[R] B) : sig I B x ∈ I.map (algebraMap R B) := tau_mem I B _

theorem tau_mulLeft (b : B) (y : I ⊗[R] B) : tau I B ((LinearMap.mulLeft R b).lTensor I y) = b • tau I B y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i c => simp [tau_tmul, Algebra.smul_def]; ring
  | add u v hu hv => simp only [map_add, hu, hv, smul_add]

theorem exists_tau {x : B} (hx : x ∈ I.map (algebraMap R B)) : ∃ y, tau I B y = x := by
  rw [Ideal.map, Ideal.span] at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨i, hi, rfl⟩ := h
    exact ⟨⟨i, hi⟩ ⊗ₜ 1, by simp [tau_tmul, Algebra.smul_def]⟩
  | zero => exact ⟨0, map_zero _⟩
  | add x x' _ _ hx hx' =>
    obtain ⟨y, rfl⟩ := hx; obtain ⟨y', rfl⟩ := hx'
    exact ⟨y + y', map_add _ _ _⟩
  | smul b x _ hx =>
    obtain ⟨y, rfl⟩ := hx
    exact ⟨(LinearMap.mulLeft R b).lTensor I y, tau_mulLeft I B b y⟩

theorem tau_injective (hB : Module.Flat R B) : Function.Injective (tau I B) :=
  (TensorProduct.lid R B).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap (M := B) I.subtype Subtype.val_injective)

variable {B} {B' : Type} [CommRing B'] [Algebra R B'] (φ : B →ₐ[R] B')

theorem iota_nat (y : I ⊗[R] B) :
    extHom (TrivSqZeroExt R I) φ (iota I B y) = iota I B' (φ.toLinearMap.lTensor I y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b => simp [iota]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tau_nat (y : I ⊗[R] B) : tau I B' (φ.toLinearMap.lTensor I y) = φ (tau I B y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul i b => simp [tau_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sig_nat (x : TrivSqZeroExt R I ⊗[R] B) :
    sig I B' (extHom (TrivSqZeroExt R I) φ x) = φ (sig I B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sig, tau_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end Lin

end GlobalTheory.PrimIdeal

namespace GlobalTheory.PrimIdeal

theorem primI_of_ext : ∀ (R : Type) [CommRing R] (I : Ideal R), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁)
    (q : R₁ →ₐ[R] R), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) ∧
    ∀ (D T : Type) [Category.{0} D] [Category.{0} T] (F : D ⥤ CommAlgCat.{0} R) (F' : T ⥤ CommAlgCat.{0} R)
      (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F'), (∀ t, Module.Flat R (F.obj t)) → (∀ t, Module.Flat R (F'.obj t)) →
      (∀ c : GlobalTheory.CatCoh.H2 (GlobalTheory.Obs.ext R₁ F),
        (extMap R₁ n₀).pull2 c = (extMap R₁ n₁).pull2 c + (extMap R₁ n₂).pull2 c → c = 0) →
      PrimI I n₀ n₁ n₂ := by
  intro R _ I
  refine ⟨TrivSqZeroExt R I, inferInstance, inferInstance, TrivSqZeroExt.fstHom R R I, ?_, ?_⟩
  · intro y y' hy hy'
    have h1 : y.fst = 0 := hy
    have h2 : y'.fst = 0 := hy'
    ext
    · simp [h1, h2]
    · simp [h1, h2]
  intro D T _ _ F F' n₀ n₁ n₂ hF hF' hc z f hz hf hrel
  choose y hy using fun (t t' t'' : D) (a : t ⟶ t') (b : t' ⟶ t'') ↦ exists_tau I (F.obj t'') (hz t t' t'' a b)
  choose y' hy' using fun (t t' : T) (a : t ⟶ t') ↦ exists_tau I (F'.obj t') (hf t t' a)
  let zh : C2 (ext (TrivSqZeroExt R I) F) := fun t t' t'' a b ↦ iota I (F.obj t'') (y t t' t'' a b)
  have hzc : zh ∈ Z2 (ext (TrivSqZeroExt R I) F) := by
    intro t t' t'' t''' φ ψ χ
    have key : (mp F χ).toLinearMap.lTensor I (y _ _ _ φ ψ) + y _ _ _ (φ ≫ ψ) χ =
        y _ _ _ φ (ψ ≫ χ) + y _ _ _ ψ χ := by
      apply tau_injective I (F.obj t''') (hF t''')
      simp only [map_add, AlgHom.toLinearMap_apply, tau_nat, hy]
      exact z.2 φ ψ χ
    have := congrArg (iota I _) key
    simp only [map_add, ← iota_nat] at this
    exact this
  obtain ⟨g, hg⟩ := H2.mk_eq_zero.1 (hc (H2.mk _ ⟨zh, hzc⟩) (by
    show H2.mk _ ((extMap _ n₀).pullbackTwoCocycle ⟨zh, hzc⟩) =
      H2.mk _ ((extMap _ n₁).pullbackTwoCocycle ⟨zh, hzc⟩) + H2.mk _ ((extMap _ n₂).pullbackTwoCocycle ⟨zh, hzc⟩)
    rw [← LinearMap.map_add (H2.mk _), H2.mk_eq_mk]
    refine ⟨fun t t' a ↦ iota I (F'.obj t') (y' t t' a), ?_⟩
    funext t t' t'' a b
    simp only [d1_apply, Submodule.coe_sub, Submodule.coe_add, Pi.sub_apply, Pi.add_apply, CoefMap.pullCocycleTwo_apply]
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hrel t) t') t'') a) b
    simp only [d1_apply, Pi.sub_apply, CoefMap.pullCocycleTwo_apply] at e
    have key : (mp F' b).toLinearMap.lTensor I (y' _ _ a) - y' _ _ (a ≫ b) + y' _ _ b =
        (coefHom n₀ t'').toLinearMap.lTensor I (y _ _ _ (n₀.G.map a) (n₀.G.map b)) -
          ((coefHom n₁ t'').toLinearMap.lTensor I (y _ _ _ (n₁.G.map a) (n₁.G.map b)) +
            (coefHom n₂ t'').toLinearMap.lTensor I (y _ _ _ (n₂.G.map a) (n₂.G.map b))) := by
      apply tau_injective I (F'.obj t'') (hF' t'')
      simp only [map_add, map_sub, AlgHom.toLinearMap_apply, tau_nat, hy, hy']
      rw [e]
      rw [sub_sub]; rfl
    have := congrArg (iota I _) key
    simp only [map_add, map_sub, ← iota_nat] at this
    exact this))
  refine ⟨fun t t' a ↦ sig I (F.obj t') (g t t' a), fun t t' a ↦ sig_mem I _ _, ?_⟩
  funext t t' t'' a b
  have e := congrFun (congrFun (congrFun (congrFun (congrFun hg t) t') t'') a) b
  simp only [d1_apply] at e ⊢
  rw [← sig_nat, ← map_sub, ← map_add]
  change sig I (F.obj t'') (mp (ext (TrivSqZeroExt R I) F) b (g t t' a) - g t t'' (a ≫ b) + g t' t'' b) = _
  rw [e]
  exact (sig_iota I _ _).trans (hy t t' t'' a b)

end GlobalTheory.PrimIdeal
end
end

