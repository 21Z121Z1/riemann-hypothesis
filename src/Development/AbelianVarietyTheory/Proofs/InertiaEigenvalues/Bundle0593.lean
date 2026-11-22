import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0558
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0537
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0581
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0582

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JBSingleMemFilT
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiPole

section Rings

variable {l : ℕ} [Fact l.Prime]

theorem ι_aB (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    C.ι (Per.aB l w) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l w) :=
  GlobalTheory.MemLoc.ULaws.iota_aB C w

private theorem aB_alg (C : GlobalTheory.MemLoc.Core l) (w : Per.Ainf l) :
    algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) w) = Per.aB l w :=
  GlobalTheory.MemLoc.ULaws.iota_injective C (by rw [C.ι_j, GlobalTheory.MemLoc.TFil.j_alg C.j_cris, ι_aB])

private theorem toB_tmul (C : GlobalTheory.MemLoc.Core l) {O : Type} [CommRing O] [Algebra ℤ_[l] O] (o : O)
    (w : Per.Ainf l) : toB l O (o ⊗ₜ[ℤ_[l]] w) = o ⊗ₜ[ℤ_[l]] Per.aB l w :=
  congrArg (fun y : Per.Bcris l => (o ⊗ₜ[ℤ_[l]] y : OB l O)) (aB_alg C w)

end Rings

section Tensor

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

theorem smul_TWincl_mem_filT (C : GlobalTheory.MemLoc.Core l) (T : LocLat G ℚ_[l] K O) {n : ℤ} {d : Per.Bcris l}
    (hd : C.ι d ∈ Per.FilD l n) (z : TW (OA l O) T) :
    ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z ∈ filT C T n := by
  unfold filT
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | tmul c x =>
    change ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • (toB l O c ⊗ₜ[O] x) ∈ _
    rw [smul_tmul', smul_eq_mul]
    induction c using TensorProduct.induction_on with
    | zero => rw [map_zero, mul_zero, zero_tmul]; exact zero_mem _
    | tmul o w =>
      have e : ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) * toB l O (o ⊗ₜ w) =
          o • ((1 : O) ⊗ₜ[ℤ_[l]] (d * Per.aB l w) : OB l O) := by
        rw [toB_tmul C o w, Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e, ← smul_tmul']
      refine Submodule.smul_mem _ o (Submodule.subset_span ⟨d * Per.aB l w, x, ?_, rfl⟩)
      rw [map_mul, ι_aB, mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hd
    | add c c' hc hc' => rw [map_add, mul_add, add_tmul]; exact add_mem hc hc'
  | add z z' hz hz' => rw [map_add, smul_add]; exact add_mem hz hz'

end Tensor

end GlobalTheory.BKGal.XiPole

open GlobalTheory.BKGal.XiPole in

theorem GlobalTheory.BKGal.XiPole.jB_single_mem_filT : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (C : GlobalTheory.MemLoc.Core l) (i : ι), R.jB (Pi.single i 1) ∈ filT C T (-(η : ℤ)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R C i

  obtain ⟨ζ, ε, h0, -, hz1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => hz1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hδl : ((frobeniusEquiv (Per.Fl l) l).symm ε) ^ l = ε := by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  have hEps : IsEps ε := ⟨he, _, hδl, hE.2⟩

  obtain ⟨-, -, -, hK4⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε _ hEps hδl
  obtain ⟨z, hz⟩ := hK4 (inclL t ϖ D.toPhiMod (Pi.single i 1)) ⟨Pi.single i 1, rfl⟩
  rw [← inclL_smul_coord] at hz
  have hB := R.cmp _ z hz
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ η) with hm
  have e1 : (fun j => toB l O (m * (Pi.single i (1 : OA l O) : ι → OA l O) j)) = toB l O m • (Pi.single i (1 : OB l O)) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Pi.single_apply, hj]
  rw [e1, map_smul] at hB
  have htm : toB l O m = (1 : O) ⊗ₜ[ℤ_[l]] Per.aB l (muOf ε ^ η) := toB_tmul C _ _

  have hμu : IsUnit (Per.aB l (muOf ε)) := by
    rw [← aB_alg C]
    exact GlobalTheory.MemLoc.TFil.isUnit_mu hE
  set d : Per.Bcris l := ((hμu.unit⁻¹ : (Per.Bcris l)ˣ) : Per.Bcris l) ^ η with hd
  have hdm : d * Per.aB l (muOf ε ^ η) = 1 := by
    rw [hd, map_pow, ← mul_pow, IsUnit.val_inv_mul, one_pow]
  clear_value d
  have hjB : R.jB (Pi.single i 1) = ((1 : O) ⊗ₜ[ℤ_[l]] d : OB l O) • TWincl (toB l O) T z := by
    rw [← hB, smul_smul, htm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hdm,
      ← Algebra.TensorProduct.one_def, one_smul]

  have hν : IsUnit (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) :=
    (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (GlobalTheory.MemLoc.TiedUnif.theta_piOne hE)
  obtain ⟨v', hv'⟩ := hν.exists_right_inv
  set U := (GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE).unit with hUdef
  have hUval : (U : Per.BdR l) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi ε)) :=
    IsUnit.unit_spec _
  have hιμ : C.ι (Per.aB l (muOf ε)) = (U : Per.BdR l) *
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) := by
    rw [ι_aB, hUval, ← map_mul, ← map_mul]
    exact congrArg _ (congrArg _ (GlobalTheory.MemLoc.TiedUnif.mu_eq ε))
  have h1 : C.ι d * (C.ι (Per.aB l (muOf ε))) ^ η = 1 := by
    rw [← map_pow, ← map_mul, ← map_pow, hdm, map_one]
  rw [hιμ] at h1
  have hpq : ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
      (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) ^ η = 1 := by
    rw [show ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
      (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) =
      ((U : Per.BdR l) * ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l)) *
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε) * v') by
      rw [map_mul]; ring, Units.mul_inv, hv', map_one, one_mul, one_pow]
  have hU : ((U ^ (-(η : ℤ)) : (Per.BdR l)ˣ) : Per.BdR l) = ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ η := by
    rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  have hdF : C.ι d ∈ Per.FilD l (-(η : ℤ)) := by
    refine (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff hE _ _).2 ⟨v' ^ η, ?_⟩
    rw [← hUdef, hU, map_pow]
    calc C.ι d = C.ι d * ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l)
            (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε)) *
          (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v')) ^ η := by
          rw [hpq, mul_one]
      _ = (C.ι d * ((U : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l)
            (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.TiedUnif.piOne ε))) ^ η) *
          (((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) v') ^ η := by
          rw [mul_pow _ _ η, mul_assoc]
      _ = _ := by rw [h1, one_mul, mul_pow]
  rw [hjB]
  exact smul_TWincl_mem_filT C T hdF z
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinModuleTensorBdRPlusEqLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.DeRhamIdent

section Generic

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
  [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G]

theorem TWincl_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) :
    TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul b x => simp [TWincl, TensorProduct.smul_tmul']

theorem TWincl_inj {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    (f : R →ₐ[O] R') (hf : Function.Injective f) (T : LocLat G ℚ_[l] K O) :
    Function.Injective (TWincl f T) := by
  haveI : Module.Free O ↥T.L.T := T.L.free
  exact Module.Flat.rTensor_preserves_injective_linearMap (M := ↥T.L.T) f.toLinearMap hf

theorem fix_of_unit {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (f : M →ₗ[R] M) (r : R)
    (hr : IsUnit r) (m : M) (h : f (r • m) = r • m) : f m = m := by
  obtain ⟨u, rfl⟩ := hr
  have h2 := congrArg (fun y => ((u⁻¹ : Rˣ) : R) • y) h
  simp only [← map_smul, smul_smul, Units.inv_mul, one_smul] at h2
  exact h2

end Generic

section Incl

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (ι : Type)

theorem inclV_apply (c : ι → OA l O) (i : ι) : inclV l O ι c i = inclO l O (c i) := rfl

theorem inclV_smul (r : OA l O) (c : ι → OA l O) : inclV l O ι (r • c) = inclO l O r • inclV l O ι c := by
  funext i
  simp only [inclV_apply, Pi.smul_apply, smul_eq_mul, map_mul]

theorem inclV_inj [Module.Free ℤ_[l] O] : Function.Injective (inclV l O ι) := fun c d h =>
  funext fun i => inclO_injective (congrFun h i)

end Incl

end GlobalTheory.DeRhamIdent

namespace GlobalTheory.DeRhamIdent

open GlobalTheory.DeRhamIdent

set_option maxHeartbeats 2000000 in

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T), ∃ jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T, ∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z → jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  obtain ⟨⟨ε, hε⟩, hεall⟩ := GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l
  set δ : OCb l := (frobeniusEquiv (OCb l) l).symm ε with hδdef
  have hδ : δ ^ l = ε := frobeniusEquiv_symm_pow_p (OCb l) l ε
  obtain ⟨-, -, hθ, -⟩ := hεall ε δ hε hδ
  obtain ⟨α, β, hα, hβ⟩ := P.exists_exponents
  obtain ⟨hK1, hK2, -, -⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι P T I α β hα hβ ε δ hε hδ
  set ν : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] muOf δ with hν
  have hpow : ∀ k : ℕ, (1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ k) = ν ^ k := fun k => by
    rw [hν, Algebra.TensorProduct.tmul_pow, one_pow]
  simp only [hpow] at hK1 hK2

  have hu : IsUnit (toOD l O ν) := by
    have h1 : IsUnit (ainfToBdRp l (muOf δ)) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
      change Per.θD l (GlobalTheory.MemLoc.aDp l (muOf δ)) ≠ 0
      rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
      intro h
      exact hθ (Subtype.ext h))
    have h2 : toOD l O ν = (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
        (ainfToBdRp l (muOf δ)) := by
      simp [hν, toOD]
    rw [h2]
    exact h1.map _
  set u : (OD l O)ˣ := hu.unit with hudef
  have hu' : (u : OD l O) = toOD l O ν := hu.unit_spec
  have hV := inclV_inj l O ι

  choose z hz using fun i => hK2 (inclV l O ι (Pi.single i 1)) ⟨_, rfl⟩
  have hsum : ∀ c : ι → OA l O,
      inclV l O ι c = ∑ i, inclO l O (c i) • inclV l O ι (Pi.single i 1) := by
    intro c
    funext j
    simp [inclV_apply, Finset.sum_apply, Pi.single_apply]
  have hJ0 : ∀ (c : ι → OA l O) (z' : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z' →
      ν ^ α • z' = ∑ i, c i • z i := by
    intro c z' h
    apply TWincl_inj (inclO l O) inclO_injective T
    calc TWincl (inclO l O) T (ν ^ α • z') = inclO l O (ν ^ α) • I.j (inclV l O ι c) := by
          rw [TWincl_smul, h]
      _ = ∑ i, inclO l O (c i) • I.j (inclO l O (ν ^ α) • inclV l O ι (Pi.single i 1)) := by
          rw [← I.j.map_smul, hsum c, Finset.smul_sum, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_comm, I.j.map_smul]
      _ = TWincl (inclO l O) T (∑ i, c i • z i) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hz i, TWincl_smul]
  let w : ι → TW (OD l O) T := fun i => ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ α • TWincl (toOD l O) T (z i)
  let jD : (ι → OD l O) →ₗ[OD l O] TW (OD l O) T := ∑ i, (LinearMap.proj i).smulRight (w i)
  have hjD : ∀ d, jD d = ∑ i, d i • w i := fun d => by
    simp [jD, LinearMap.sum_apply]
  have hJ : ∀ (c : ι → OA l O) (z' : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z' →
      jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z' := by
    intro c z' h
    have h2 : toOD l O (ν ^ α) • TWincl (toOD l O) T z' =
        ∑ i, toOD l O (c i) • TWincl (toOD l O) T (z i) := by
      rw [← TWincl_smul, hJ0 c z' h, map_sum]
      simp only [TWincl_smul]
    rw [hjD]
    calc ∑ i, toOD l O (c i) • w i
        = ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ α • ∑ i, toOD l O (c i) • TWincl (toOD l O) T (z i) := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
      _ = ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ α • (toOD l O (ν ^ α) • TWincl (toOD l O) T z') := by rw [h2]
      _ = TWincl (toOD l O) T z' := by
          rw [smul_smul, map_pow, ← hu', ← mul_pow, Units.inv_mul, one_pow, one_smul]

  have hK1' : ∀ x, ∃ y, inclV l O ι y = inclO l O (ν ^ β) • I.ofT x := fun x => LinearMap.mem_range.1 (hK1 x)
  choose Cx hC using hK1'
  let C : ↥T.L.T →ₗ[O] (ι → OA l O) :=
    { toFun := Cx
      map_add' := fun x y => hV (by rw [map_add, hC, hC, hC, map_add, smul_add])
      map_smul' := fun o x => hV (by rw [map_smul, hC, hC, map_smul, RingHom.id_apply, smul_comm]) }
  let CA : TW (OA l O) T →ₗ[OA l O] (ι → OA l O) := LinearMap.liftBaseChange (OA l O) C
  have hP1 : ∀ z' : TW (OA l O) T,
      inclV l O ι (CA z') = inclO l O (ν ^ β) • I.j.symm (TWincl (inclO l O) T z') := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]
    | tmul b x =>
      have e1 : TWincl (inclO l O) T (b ⊗ₜ[O] x) = inclO l O b • ((1 : OW l O) ⊗ₜ[O] x) := by
        simp [TWincl, TensorProduct.smul_tmul']
      have e2 : I.j.symm ((1 : OW l O) ⊗ₜ[O] x) = I.ofT x := rfl
      rw [e1, I.j.symm.map_smul, e2, LinearMap.liftBaseChange_tmul, inclV_smul]
      change inclO l O b • inclV l O ι (Cx x) = _
      rw [hC, smul_comm]
  let ψ : TW (OD l O) T →ₗ[OD l O] (ι → OD l O) := ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ β •
    LinearMap.liftBaseChange (OD l O) (((toOD l O).toLinearMap.compLeft ι) ∘ₗ C)
  have hP2 : ∀ z' : TW (OA l O) T,
      ψ (TWincl (toOD l O) T z') = ((u⁻¹ : (OD l O)ˣ) : OD l O) ^ β • fun i => toOD l O (CA z' i) := by
    intro z'
    induction z' using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      funext i
      simp
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, ← smul_add]
      congr 1
      funext i
      simp
    | tmul b x =>
      simp only [ψ, CA, TWincl, LinearMap.smul_apply, TensorProduct.map_tmul, AlgHom.toLinearMap_apply,
        LinearMap.id_apply, LinearMap.liftBaseChange_tmul]
      congr 1
      funext i
      simp [C, LinearMap.compLeft, map_mul]
  have hΨ : ∀ (c : ι → OA l O) (z' : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z' →
      ψ (TWincl (toOD l O) T z') = fun i => toOD l O (c i) := by
    intro c z' h
    have h1 : CA z' = ν ^ β • c := hV (by rw [hP1, ← h, I.j.symm_apply_apply, inclV_smul])
    rw [hP2, h1]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hu', ← mul_assoc, ← mul_pow,
      Units.inv_mul, one_pow, one_mul]
  have h1 : jD ∘ₗ ψ = LinearMap.id := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro d x
    have e0 : d ⊗ₜ[O] x = d • ((1 : OD l O) ⊗ₜ[O] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e0, map_smul, map_smul]
    congr 1
    have hx : I.j (inclV l O ι (Cx x)) = TWincl (inclO l O) T ((ν ^ β) ⊗ₜ[O] x) := by
      rw [hC, I.j.map_smul, I.j_ofT]
      simp [TWincl, TensorProduct.smul_tmul']
    have e3 : TWincl (toOD l O) T ((ν ^ β) ⊗ₜ[O] x) = ((u : OD l O) ^ β) • ((1 : OD l O) ⊗ₜ[O] x) := by
      simp [TWincl, TensorProduct.smul_tmul', hu']
    refine fix_of_unit (jD ∘ₗ ψ) ((u : OD l O) ^ β) ((Units.isUnit u).pow β) _ ?_
    rw [← e3, LinearMap.comp_apply, hΨ _ _ hx, hJ _ _ hx]
  have h2 : ψ ∘ₗ jD = LinearMap.id := by
    apply LinearMap.pi_ext'
    intro i
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    have hc : inclV l O ι (Pi.single i (ν ^ α)) = inclO l O (ν ^ α) • inclV l O ι (Pi.single i 1) := by
      rw [← inclV_smul]
      congr 1
      funext j
      simp [Pi.single_apply]
    have hzi : I.j (inclV l O ι (Pi.single i (ν ^ α))) = TWincl (inclO l O) T (z i) := by rw [hc, hz i]
    have e4 : (fun j => toOD l O ((Pi.single i (ν ^ α) : ι → OA l O) j)) =
        ((u : OD l O) ^ α) • (LinearMap.single (OD l O) (fun _ => OD l O) i 1) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hu', map_pow]
      · simp [Pi.single_apply, hj]
    refine fix_of_unit (ψ ∘ₗ jD) ((u : OD l O) ^ α) ((Units.isUnit u).pow α) _ ?_
    rw [← e4, LinearMap.comp_apply, hJ _ _ hzi, hΨ _ _ hzi]
  exact ⟨LinearEquiv.ofLinear jD ψ h1 h2, fun c z' h => hJ c z' h⟩

end GlobalTheory.DeRhamIdent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDualLiftingProof
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition

namespace GlobalTheory.Pass.LocDual

theorem T2 {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {S S' : Submodule O M} (H : Submodule O M)
    (h : S ≤ S') : BlochKatoDuality.lenMod S H ≤ BlochKatoDuality.lenMod S' H := by
  unfold BlochKatoDuality.lenMod
  have hle : S ⊔ H ≤ S' ⊔ H := sup_le_sup_right h H
  let f : ↥(S ⊔ H) ⧸ H.comap (S ⊔ H).subtype →ₗ[O] ↥(S' ⊔ H) ⧸ H.comap (S' ⊔ H).subtype :=
    Submodule.mapQ _ _ (Submodule.inclusion hle) (fun x hx => hx)
  refine Module.length_le_of_injective f ?_
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro z hz
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [LinearMap.mem_ker] at hz
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  have := (Submodule.Quotient.mk_eq_zero _).1 hz
  exact this

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : StepLocDual := by
  intro D hLOC hBK hFont hPot i r hr Xs w hw hdeg n e hPF hLF k M hSub
  unfold LocBoundP
  apply GlobalTheory.T.lengthModulo_span_le_of_forall_finset
  intro F hF
  obtain ⟨X, hX, hle⟩ := GlobalTheory.T.localCocycles_mem_span_pushout_summandLattice D hFont i r hr Xs w hw n hPF k M hSub F hF
  obtain ⟨hdrX, X', PX, hdX, hsX⟩ := GlobalTheory.T.potential_family_summand_restriction D hFont hPot i r hr Xs w hw n hPF X hX
  obtain ⟨hdrU, U', PU, hsU, LT', hdU, hrk⟩ := GlobalTheory.T.crystalline_potential_family D hFont hPot hBK i r hr Xs w hw hdeg n hPF k M hSub
  have hLift := GlobalTheory.T.liftAll_subSums_of_liftFamily_matrixFamily (Br.PD D.loc D.nbr i w hw) _ e X' U' hLF hsX hsU
  have hTw : IsTwistRep (1 : Br.G D.nbr i w hw →* (Br.LL D.nbr i w hw)ˣ)⁻¹ X.ρ X.ρ :=
    ⟨LinearEquiv.refl _ _, fun g x => by simp⟩
  have hHyp : BlochKatoDuality.Hyp (Br.PD D.loc D.nbr i w hw) X X (locU i w hw M hSub.1) X' U' 1 PX PU
      (Br.locLat D.nbr i w hw M) LT' e := ⟨hTw, hdrU, hdX, hdU, Or.inr ⟨hdrX, hLift⟩⟩
  obtain ⟨m, kk, hm, hk, hmk⟩ := hLOC.2 (D.nd.l i) (D.nbr i w hw).Kw (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)
    (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL) X X (locU i w hw M hSub.1) X' U' 1 PX PU
    (Br.locLat D.nbr i w hw M) LT' e hHyp
  refine (T2 _ hle).trans ?_
  change BlochKatoDuality.lenMod (BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M))
    (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) ≤ _
  have hm' : BlochKatoDuality.lenMod (BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M))
    (HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M)) = m := hm
  have hk' : lenOl (Br.PD D.loc D.nbr i w hw) (O := Br.OLL D.nbr i w hw) = kk := hk
  rw [hm', hk']
  have : m ≤ 2 * k * e * kk :=
    hmk.trans ((Nat.mul_le_mul_right kk (Nat.mul_le_mul_left e hrk)).trans_eq (by ring))
  exact_mod_cast this

end GlobalTheory.Pass.LocDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LtSeriesCoeffEqZero
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK

namespace GlobalTheory.LTPer

theorem sum_sub_sum_mem {A : Type*} [CommRing A] (I : Ideal A) {x : A} (hx : x ∈ I) (c : ℕ → A) (N : ℕ)
    (hc : ∀ j, N ≤ j → c j = 0) (n : ℕ) :
    ∑ j ∈ Finset.range N, c j * x ^ j - ∑ j ∈ Finset.range n, c j * x ^ j ∈ I ^ n := by
  rcases le_or_gt n N with h | h
  · rw [← Finset.sum_range_add_sum_Ico _ h, add_sub_cancel_left]
    refine Ideal.sum_mem _ fun j hj => Ideal.mul_mem_left _ _ ?_
    exact Ideal.pow_le_pow_right (Finset.mem_Ico.1 hj).1 (Ideal.pow_mem_pow hx j)
  · rw [← Finset.sum_range_add_sum_Ico _ h.le, sub_add_cancel_left,
      Finset.sum_eq_zero (fun j hj => by rw [hc j (Finset.mem_Ico.1 hj).1, zero_mul]), neg_zero]
    exact Ideal.zero_mem _

variable {l : ℕ} [Fact l.Prime]

theorem coeff_ltSeries (K : FinExt l) (π : ↥(OL K)) (j : ℕ) :
    PowerSeries.coeff j (ltSeries K π) = (if j = 1 then π else 0) + (if j = resCard K then 1 else 0) := by
  rw [ltSeries, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, mul_ite, mul_one,
    mul_zero]

theorem ltSeries_eval (K : FinExt l) (π : ↥(OL K)) (ω : AK K) :
    inO K π * ω + ω ^ resCard K =
      ∑ j ∈ Finset.range (resCard K + 2), inO K (PowerSeries.coeff j (ltSeries K π)) * ω ^ j := by
  simp only [coeff_ltSeries, map_add, add_mul, Finset.sum_add_distrib, apply_ite (inO K), map_zero, map_one,
    ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_range]
  rw [if_pos (by omega), if_pos (by omega), pow_one]

theorem ltSeries_coeff_eq_zero (K : FinExt l) (π : ↥(OL K)) (j : ℕ) (hj : resCard K + 2 ≤ j) :
    inO K (PowerSeries.coeff j (ltSeries K π)) = 0 := by
  rw [coeff_ltSeries, if_neg (by omega), if_neg (by omega), add_zero, map_zero]

end GlobalTheory.LTPer

open GlobalTheory.LTPer in

theorem GlobalTheory.LTPer.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∃ t : BK K, t ≠ 0 ∧ frobB K t = inK K (π : ↥K.1) * t ∧ ∀ g : ↥(GK K), galB g t = inK K (χ g : ↥K.1) * t := by
  intro l _ K χ π z hD
  haveI := Formalism.BasicNotions.Examples₂.LB.OL_resFinite K
  have hπ : Irreducible π := hD.1
  obtain ⟨hf, hE⟩ := GlobalTheory.T.lubin_tate_endomorphism_unique l K π hπ
  obtain ⟨ω, hω0, hθ, hφ, hg⟩ := GlobalTheory.T.lubin_tate_period_galois_expansion l K χ π z hD
  have hθ' : ω ∈ RingHom.ker (thetaK K) := hθ
  refine ⟨ltLog hπ hf ω hθ, GlobalTheory.T.lubin_tate_log_ne_zero l K π hπ _ hf ω hθ (GlobalTheory.T.lubin_tate_period_theta_kernel l K χ π z hD ω hω0 hθ hφ hg), ?_, fun g => ?_⟩
  · refine ev_log_self hπ hf hθ (y := frobq K ω) (fun n => ?_) (Ev.frob (ev_ltLog hπ hf ω hθ))
    rw [hφ, ltSeries_eval]
    exact sum_sub_sum_mem _ hθ' _ _ (fun j hj => ltSeries_coeff_eq_zero K π j hj) n
  · obtain ⟨a, ha, φ, hφE, -⟩ := hD.2.2.2.2 g
    have hy := hg g a φ ha hφE
    rw [(hE a φ).1 hφE] at hy
    rw [ev_log_hom hπ hf a hθ hy (Ev.gal g (ev_ltLog hπ hf ω hθ)), ← ha]
    rfl

end
end

