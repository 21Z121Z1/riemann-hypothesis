import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsEqAlgebraMapAddPowMul
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefJumpProof
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealPowerMembershipDivisible
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.HatDescent

variable {l : ℕ} [Fact l.Prime]

theorem aDp_ev_eis_mul_eq_zero {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (y : Per.BdRp l)
    (hy : GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) * y = 0) : y = 0 := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hxi : GlobalTheory.MemLoc.xi ε ∈ Ideal.span {ϖ.ev a (eis l a e)} := by
    rw [ϖ.span_ev_eis a, GlobalTheory.MemLoc.ker_theta_eq_span_xi hE]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hxi
  refine (GlobalTheory.MemLoc.filtration_eq_xi_pow l ε hE).2.1 y ?_
  rw [← hc, map_mul, mul_assoc, hy, mul_zero]

theorem eis_pow_dvd_of_aDp_mem {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (n : ℕ)
    (x : (Wq l a)⟦X⟧)
    (h : GlobalTheory.MemLoc.aDp l (ϖ.ev a x) ∈ Ideal.span {GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) ^ n}) :
    eis l a e ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
    have h1 : Per.θ l (ϖ.ev a x) = 0 := by
      have h2 := congrArg (Per.θD l) hc
      rw [map_mul, map_pow, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1,
        (ϖ.theta_ev_eq_zero_iff a _).2 dvd_rfl] at h2
      exact Subtype.ext (h2.symm.trans (by simp))
    obtain ⟨x', rfl⟩ := (ϖ.theta_ev_eq_zero_iff a x).1 h1
    have h2 : GlobalTheory.MemLoc.aDp l (ϖ.ev a x') ∈
        Ideal.span {GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) ^ n} := by
      rw [Ideal.mem_span_singleton']
      refine ⟨c, ?_⟩
      rw [← sub_eq_zero]
      apply aDp_ev_eis_mul_eq_zero (a := a) ϖ
      rw [map_mul, map_mul] at hc
      rw [mul_sub, ← hc]
      ring
    obtain ⟨z, hz⟩ := ih x' h2
    exact ⟨z, by rw [hz, pow_succ']; ring⟩

end GlobalTheory.BKReal.HatDescent

namespace GlobalTheory.BKReal.HatDescent

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

def crdB {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) : OD l O →ₗ[ℤ_[l]] Per.BdRp l :=
  TensorProduct.lid ℤ_[l] (Per.BdRp l) ∘ₗ (b.coord j).rTensor (Per.BdRp l)

theorem crdB_tmul {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) (o : O) (β : Per.BdRp l) :
    crdB b j (o ⊗ₜ β) = b.coord j o • β := rfl

theorem crdB_mul {J : Type} (b : Module.Basis J ℤ_[l] O) (j : J) (c : Per.BdRp l) (z : OD l O) :
    crdB b j (z * (1 ⊗ₜ c)) = crdB b j z * c := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul o β =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, crdB_tmul, crdB_tmul, smul_mul_assoc]
  | add x y hx hy => rw [add_mul, map_add, map_add, hx, hy, add_mul]

theorem crdB_sum {J : Type} [Fintype J] [DecidableEq J] (b : Module.Basis J ℤ_[l] O) (j : J)
    (β : J → Per.BdRp l) : crdB b j (∑ k, b k ⊗ₜ β k) = β j := by
  rw [map_sum, Finset.sum_eq_single j (fun k _ hk => by
    rw [crdB_tmul, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp [Finsupp.single_apply, hk])
    (by simp), crdB_tmul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, one_smul]

variable {a e : ℕ} [NeZero a] [NeZero e] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  {K : Type} [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in
theorem toAc_eis (t : Wq l a →ₐ[ℤ_[l]] O) : toAc t K (eis l a e) = fun _ => EIn l e (A O K) := by
  have hX : toAc t K X = fun _ => uIn (A O K) :=
    funext fun τ => Subtype.ext ((congrArg (PowerSeries.map _) (PowerSeries.map_X _)).trans
      (PowerSeries.map_X _))
  have hE : EIn l e (A O K) = uIn _ ^ e + (l : A O K) := Subtype.ext (by simp [E])
  rw [eis, map_add, map_pow, hX, map_natCast, hE]
  rfl

theorem exists_of_toOD_iTot_mem (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (n : ℕ) (f : ZMod a → A O K)
    (h : toOD l O (ϖ.iTot t K f) ∈
      Ideal.span {((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) : OD l O) ^ n}) :
    ∃ g : ZMod a → A O K, f = (fun _ => EIn l e (A O K)) ^ n * g := by
  classical
  set b := Module.Free.chooseBasis ℤ_[l] O
  obtain ⟨x, rfl⟩ := exists_eq_sum_toAc t K b f
  have hT : toOD l O (ϖ.iTot t K (∑ j, b j • toAc t K (x j))) =
      ∑ j, b j ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (x j)) := by
    simp only [map_sum, map_smul, PiSys.iTot_toAc]
    refine Finset.sum_congr rfl fun j _ => ?_
    show b j • ((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (x j))) = _
    rw [smul_tmul', smul_eq_mul, mul_one]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  have hx : ∀ j, eis l a e ^ n ∣ x j := fun j => by
    apply eis_pow_dvd_of_aDp_mem ϖ n
    rw [Ideal.mem_span_singleton']
    refine ⟨crdB b j z, ?_⟩
    have := congrArg (crdB b j) (hz.trans hT)
    rw [crdB_sum, Algebra.TensorProduct.tmul_pow, one_pow, crdB_mul] at this
    exact this
  choose y hy using hx
  refine ⟨∑ j, b j • toAc t K (y j), ?_⟩
  simp only [hy, map_mul, map_pow, toAc_eis, Finset.mul_sum, mul_smul_comm]

end GlobalTheory.BKReal.HatDescent

namespace GlobalTheory.BKReal.PiSys

open GlobalTheory.BKReal.HatDescent

theorem eq_Ehat_pow_mul_of_iD_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (n : ℕ) (x : ZMod a → Ahat O K l e),
    ϖ.iD t K x ∈ Ideal.span {ϖ.iD t K (fun _ => Ehat O K l e) ^ n} →
      ∃ y : ZMod a → Ahat O K l e, x = (fun _ => Ehat O K l e) ^ n * y := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ n x hx
  have hd : ϖ.iD t K (fun _ => Ehat O K l e) =
      (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
    rw [iD, glue_const, Ehat, iHat_ofAl]
    exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
  choose g x' hg using fun τ => exists_eq_algebraMap_add_pow_mul (EIn l e (invL l (A O K))) n (x τ)
  have hsplit : x = (fun τ => ofAl O K l e (g τ)) + (fun _ => Ehat O K l e) ^ n * x' :=
    funext fun τ => hg τ
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (l : A O K)) (S := invL l (A O K)) g
  choose r hr using hm

  have h1 : ϖ.iD t K (fun τ => ofAl O K l e (g τ)) ∈
      Ideal.span {ϖ.iD t K (fun _ => Ehat O K l e) ^ n} := by
    rw [hsplit, map_add, map_mul, map_pow] at hx
    exact (Ideal.add_mem_iff_left _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))).1 hx
  have h2 : (fun τ => ofA O K l e (r τ)) =
      (fun _ => ofA O K l e ((l : A O K) ^ m)) * fun τ => ofAl O K l e (g τ) := by
    funext τ
    rw [Pi.mul_apply, ofA, RingHom.comp_apply, RingHom.comp_apply, hr τ, Algebra.smul_def, map_mul]
  have h3 : toOD l O (ϖ.iTot t K r) ∈
      Ideal.span {((1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) : OD l O) ^ n} := by
    rw [← iD_ofA, h2, map_mul, ← hd]
    exact Ideal.mul_mem_left _ _ h1
  obtain ⟨h, hh⟩ := exists_of_toOD_iTot_mem t ϖ n r h3
  have hu : IsUnit (algebraMap (A O K) (invL l (A O K)) (l : A O K)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hEA : algebraMap (A O K) (invL l (A O K)) (EIn l e (A O K)) = EIn l e (invL l (A O K)) := rfl
  have hgτ : ∀ τ, g τ = EIn l e (invL l (A O K)) ^ n *
      (algebraMap (A O K) (invL l (A O K)) (h τ) * ↑(hu.unit⁻¹ ^ m)) := fun τ => by
    have h4 : algebraMap (A O K) (invL l (A O K)) (l : A O K) ^ m * g τ =
        EIn l e (invL l (A O K)) ^ n * algebraMap (A O K) (invL l (A O K)) (h τ) := by
      have h5 := (hr τ).symm
      rw [Algebra.smul_def, hh, Pi.mul_apply, Pi.pow_apply] at h5
      simp only [map_mul, map_pow, hEA] at h5
      exact h5
    have hone : (↑(hu.unit⁻¹ ^ m) : invL l (A O K)) * algebraMap (A O K) (invL l (A O K)) (l : A O K) ^ m = 1 := by
      rw [Units.val_pow_eq_pow_val, ← mul_pow, hu.val_inv_mul, one_pow]
    linear_combination (-(g τ)) * hone + (↑(hu.unit⁻¹ ^ m) : invL l (A O K)) * h4
  refine ⟨fun τ => ofAl O K l e (algebraMap (A O K) (invL l (A O K)) (h τ) * ↑(hu.unit⁻¹ ^ m)) + x' τ, ?_⟩
  funext τ
  rw [hg τ, Pi.mul_apply, Pi.pow_apply, hgτ τ, map_mul, map_pow, mul_add]
  rfl

end GlobalTheory.BKReal.PiSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.BaseCoef

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

abbrev incl {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) : ↥LL.1 →ₐ[ℚ_[l]] ↥LL'.1 :=
  IntermediateField.inclusion h

def IsLatBasis {LL : FinExt l} (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : Prop :=
  (∀ i, b i ∈ T.L.T) ∧ ∀ x ∈ T.L.T, ∀ i, b.repr x i ∈ OL LL

def matRep {LL : FinExt l} (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : G →* Matrix (Fin k) (Fin k) ↥LL.1 :=
  (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp T.ρ

def matRepExt {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : G →* Matrix (Fin k) (Fin k) ↥LL'.1 :=
  ((incl h).mapMatrix : Matrix (Fin k) (Fin k) ↥LL.1 →ₐ[ℚ_[l]] Matrix (Fin k) (Fin k) ↥LL'.1).toRingHom.toMonoidHom.comp
    (matRep T b)

def intVec (LL' : FinExt l) (k : ℕ) : Submodule ↥(OL LL') (Fin k → ↥LL'.1) where
  carrier := {v | ∀ i, v i ∈ OL LL'}
  add_mem' := fun ha hb i => add_mem (ha i) (hb i)
  zero_mem' := fun _ => zero_mem _
  smul_mem' := fun c v hv i => by
    rw [Pi.smul_apply, Subalgebra.smul_def]
    exact mul_mem c.2 (hv i)

theorem incl_integral {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {x : ↥LL.1} (hx : x ∈ OL LL) :
    incl h x ∈ OL LL' := by
  have hx' : IsIntegral ℤ_[l] x := hx
  exact hx'.map ((incl h).restrictScalars ℤ_[l])

theorem rep_apply {F : Type} [Field F] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) F) (g : G) (x : Fin k → F) :
    CJ.rep M g x = (M g).mulVec x := rfl

set_option synthInstance.maxHeartbeats 400000

def intVecEquiv (LL' : FinExt l) (k : ℕ) : ↥(intVec LL' k) ≃ₗ[↥(OL LL')] (Fin k → ↥(OL LL')) where
  toFun v := fun i => ⟨(v : Fin k → ↥LL'.1) i, v.2 i⟩
  invFun w := ⟨fun i => (w i : ↥LL'.1), fun i => (w i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem repr_integral {LL : FinExt l} {T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k : ℕ}
    {b : Module.Basis (Fin k) ↥LL.1 T.V} (hb : IsLatBasis T b) (g : G) (i j : Fin k) :
    matRep T b g i j ∈ OL LL := by
  rw [matRep, MonoidHom.comp_apply]
  change LinearMap.toMatrix b b (T.ρ g) i j ∈ OL LL
  rw [LinearMap.toMatrix_apply]
  exact hb.2 _ (T.L.stable g _ (hb.1 j)) i

abbrev extLat {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) : LocLat G ℚ_[l] ↥LL'.1 ↥(OL LL') where
  V := Fin k → ↥LL'.1
  ρ := CJ.rep (matRepExt h T b)
  cont x := by
    refine continuous_pi fun i => ?_
    simp only [rep_apply, Matrix.mulVec, dotProduct]
    refine continuous_finset_sum _ fun j _ => Continuous.mul ?_ continuous_const
    have h1 : Continuous fun g => b.coord i (T.ρ g (b j)) :=
      (IsModuleTopology.continuous_of_linearMap (b.coord i)).comp (T.cont (b j))
    have h2 : Continuous (incl h) := continuous_subtype_val.subtype_mk _
    refine (h2.comp h1).congr fun g => ?_
    simp [matRepExt, matRep, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  L :=
    { T := intVec LL' k
      stable := fun g x hx i => by
        simp only [rep_apply, Matrix.mulVec, dotProduct]
        refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ ?_ (hx j)
        exact incl_integral h (repr_integral hb g i j)
      fg := by
        haveI : Module.Finite ↥(OL LL') ↥(intVec LL' k) := Module.Finite.equiv (intVecEquiv LL' k).symm
        exact Module.Finite.iff_fg.1 inferInstance
      free := Module.Free.of_equiv (intVecEquiv LL' k).symm
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥LL'.1 (Fin k)).span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩ j
        rw [Pi.basisFun_apply]
        by_cases hij : i = j
        · subst hij; simp [one_mem]
        · simp [Pi.single_apply, Ne.symm hij, zero_mem] }

theorem hom_integral {LL : FinExt l} {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    {b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V} {b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V}
    (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) (i : Fin k₂) (j : Fin k₁) :
    LinearMap.toMatrix b₁ b₂ F.f i j ∈ OL LL := by
  rw [LinearMap.toMatrix_apply]
  exact hb₂.2 _ (F.T_le _ (hb₁.1 j)) i

def extMat {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (F : LatHom T₁.L T₂.L) :
    Matrix (Fin k₂) (Fin k₁) ↥LL'.1 :=
  (LinearMap.toMatrix b₁ b₂ F.f).map (incl h)

set_option maxHeartbeats 1000000 in
theorem extMat_comm {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (F : LatHom T₁.L T₂.L)
    (g : G) : extMat h b₁ b₂ F * matRepExt h T₁ b₁ g = matRepExt h T₂ b₂ g * extMat h b₁ b₂ F := by
  have e1 : matRepExt h T₁ b₁ g = (LinearMap.toMatrix b₁ b₁ (T₁.ρ g)).map (incl h) := rfl
  have e2 : matRepExt h T₂ b₂ g = (LinearMap.toMatrix b₂ b₂ (T₂.ρ g)).map (incl h) := rfl
  have key : LinearMap.toMatrix b₁ b₂ F.f * LinearMap.toMatrix b₁ b₁ (T₁.ρ g) =
      LinearMap.toMatrix b₂ b₂ (T₂.ρ g) * LinearMap.toMatrix b₁ b₂ F.f := by
    have c1 := LinearMap.toMatrix_comp b₁ b₁ b₂ F.f (T₁.ρ g)
    have c2 := LinearMap.toMatrix_comp b₁ b₂ b₂ (T₂.ρ g) F.f
    have hc : F.f ∘ₗ T₁.ρ g = T₂.ρ g ∘ₗ F.f := LinearMap.ext fun y => F.equiv g y
    rw [← c1, ← c2, hc]
  refine Matrix.ext fun i j => ?_
  have := congrArg (fun M => incl h (M i j)) key
  simp only [Matrix.mul_apply, map_sum, map_mul] at this
  simpa only [e1, e2, Matrix.mul_apply, extMat, Matrix.map_apply] using this

def extHom {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    {b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V} {b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V}
    (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) :
    LatHom (extLat h T₁ b₁ hb₁).L (extLat h T₂ b₂ hb₂).L where
  f := Matrix.toLin' (extMat h b₁ b₂ F)
  equiv g x := by
    change (extMat h b₁ b₂ F).mulVec ((matRepExt h T₁ b₁ g).mulVec x) =
      (matRepExt h T₂ b₂ g).mulVec ((extMat h b₁ b₂ F).mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, extMat_comm]
  cont := LinearMap.continuous_on_pi _
  T_le x hx i := by
    change (extMat h b₁ b₂ F).mulVec x i ∈ OL LL'
    simp only [Matrix.mulVec, dotProduct, extMat, Matrix.map_apply]
    exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (incl_integral h (hom_integral hb₁ hb₂ F i j)) (hx j)

def mapSig {I LL LL' : Type} [Group I] [Field LL] [Field LL'] (f : LL →+* LL') (Sig : Finset (I →* LLˣ)) :
    Finset (I →* LL'ˣ) := by
  classical
  exact Sig.image fun a => (Units.map (f : LL →* LL')).comp a

end GlobalTheory.BaseCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndepOfFracInv
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedIndep

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

omit [Field K₀] [Algebra Qp K₀] [Algebra K₀ B] [IsScalarTower Qp K₀ B] in

theorem comm_smul (b : B) (w : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (b • w) =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b)
        (TensorProduct.comm Qp B V w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul c v => simp [TensorProduct.smul_tmul']
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem comm_smul₀ (c : K₀) (w : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (c • w) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (TensorProduct.comm Qp B V w) := by
  rw [← algebraMap_smul B c w, comm_smul (LL := LL)]
  rfl

end Generic

end GlobalTheory.Per.TiedIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharOpenKerTrivialFixingNormal
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem char_inertia_trivial_on_fixing_normal : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l)
    (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) →
    ∃ F : FinExt l, Normal ℚ_[l] ↥F.1 ∧ ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)),
      (∀ x ∈ F.1, ((g : Gl l) : GQ l) x = x) → χ g = 1 := by
  intro l _ LL χ hopen
  obtain ⟨t₁, ht₁, ht₁e⟩ := isOpen_induced_iff.mp hopen
  obtain ⟨t₂, ht₂, ht₂e⟩ := isOpen_induced_iff.mp ht₁
  have h1 : (1 : GQ l) ∈ t₂ := by
    have hk : (1 : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) ∈ (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) := χ.ker.one_mem
    rw [← ht₁e] at hk
    have hk' : ((1 : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) : Gl l) ∈ t₁ := hk
    rw [← ht₂e] at hk'
    exact hk'
  obtain ⟨E, hfd, hN, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ_[l] (Om l) t₂).1 (ht₂.mem_nhds h1)
  refine ⟨⟨E, hfd⟩, hN, fun g hg => ?_⟩
  have hg₂ : ((g : Gl l) : GQ l) ∈ t₂ :=
    hE ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => hg x hx)
  have hg₁ : (g : Gl l) ∈ t₁ := by
    rw [← ht₂e]; exact hg₂
  have hg₀ : g ∈ (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) := by
    rw [← ht₁e]; exact hg₁
  exact hg₀

end GlobalTheory.InertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaConjMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

namespace GlobalTheory.InertiaConj

theorem norm_aut_eq {l : ℕ} [Fact l.Prime] (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : PadicAlgCl l) :
    ‖τ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv τ x).symm

theorem inertia_conj_mem : ∀ (l : ℕ) [Fact l.Prime] (g τ : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) →
    τ⁻¹ * g * τ ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  intro l _ g τ hg
  have hS : ∀ σ : Gl l, (∀ x : Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1) →
      ∀ x : Om l, ‖x‖ ≤ 1 → ‖((τ⁻¹ * σ * τ : Gl l) : GQ l) x - x‖ < 1 := by
    intro σ hσ x hx
    have hτx : ‖(τ : GQ l) x‖ ≤ 1 := by rw [norm_aut_eq]; exact hx
    have h1 := hσ ((τ : GQ l) x) hτx
    have h2 : ((τ⁻¹ * σ * τ : Gl l) : GQ l) x - x =
        ((τ : GQ l).symm) ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) := by
      simp [map_sub]
    rw [h2, norm_aut_eq]
    exact h1
  unfold IK at hg ⊢
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hS x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have : τ⁻¹ * (x * y) * τ = (τ⁻¹ * x * τ) * (τ⁻¹ * y * τ) := by group
    rw [this]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : τ⁻¹ * x⁻¹ * τ = (τ⁻¹ * x * τ)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ hx

end GlobalTheory.InertiaConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpanStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeRham_of_isCrystalline_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → IsDR (P.PD K) ρ ∧ ∀ y ∈ DdR (P.PD K) ρ, ∃ (m : ℕ) (c : Fin m → ↥K.1) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, mulVdR (K := ↥K.1) (BdR := P.R.BdR) (V := V) (LL := ↥LL.1) (c i) (ιV (P.PD K) (LL := ↥LL.1) (V := V) (d i)) := by
  first | exact @GlobalTheory.Per.CrisDR.isDR_of_isCrys | exact GlobalTheory.Per.CrisDR.isDR_of_isCrys | (intros; apply GlobalTheory.Per.CrisDR.isDR_of_isCrys <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitDeltaOfPrismIdealEqSpanStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_delta_of_prism_ideal_eq_span : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (d : B.A), B.I = Ideal.span {d} → IsUnit (B.D.δ d) := by
  first | exact @GlobalTheory.BSP.isUnit_δ_of_I_eq_span | exact GlobalTheory.BSP.isUnit_δ_of_I_eq_span | (intros; apply GlobalTheory.BSP.isUnit_δ_of_I_eq_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedAtOfIsUnramifiedInGaloisExtensionStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramifiedAt_of_isUnramifiedInGaloisExtension : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] {𝔭 : HeightOneSpectrum (𝓞 K)}, GlobalTheory.NT.UnramIn L 𝔭 → ∀ (P : Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver 𝔭.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) P := by
  first | exact @GlobalTheory.NT.isUnramifiedAt_of_unramIn | exact GlobalTheory.NT.isUnramifiedAt_of_unramIn | (intros; apply GlobalTheory.NT.isUnramifiedAt_of_unramIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDivisibleCoboundariesLeLocConstCocyclesAlStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_divisible_coboundaries_le_locConst_cocycles' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), BD LA ≤ divisibleCocycles LA := by
  first | exact @GlobalTheory.BDLocConst.lattice_divisible_coboundaries_le_locConst_cocycles | exact GlobalTheory.BDLocConst.lattice_divisible_coboundaries_le_locConst_cocycles | (intros; apply GlobalTheory.BDLocConst.lattice_divisible_coboundaries_le_locConst_cocycles <;> assumption)
end

