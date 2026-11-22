import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0558
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0557
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0150
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.RayPrincipalIdeals
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0462
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MuPowSmulActBSubMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal

theorem muPow_smul_actB_sub_mem : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O) (g : Gl l) (ε : OCb l), IsEps ε → ∀ (k : ℕ) (v : TW (OB l O) T) (z : TW (OA l O) T), toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • v = TWincl (toB l O) T z → ∃ z' : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) • (actB (sQ l) T g v - v) = TWincl (toB l O) T z' := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T g ε hε k v z hv
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨-, -, -, -, -, hgal, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  obtain ⟨u, hu⟩ := hgal (sQ l g)
  have hB : ∀ x : OA l O, toB l O (galOA O (sQ l g) x) = galOB O (sQ l g) (toB l O x) := fun x => by
    simp only [toB, AlgHom.comp_apply, galOB_toOB, galOCr_toOCr]
  have hμ : galOA O (sQ l g) ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) =
      ((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k * ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) := by
    rw [map_pow, galOA_tmul, hu, ← mul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hinv : ((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k * ((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k = 1 := by
    rw [← mul_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, ← Algebra.TensorProduct.one_def, one_pow]
  set m := toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ k) with hm
  set w := TWact (galOA O (sQ l g)) T g z with hw
  have h1 : actB (sQ l) T g (m • v) = TWincl (toB l O) T w := by
    rw [hv]
    exact (GlobalTheory.Cyc.Decomp.TWincl_act (toB l O) (galOA O (sQ l g)) (galOB O (sQ l g)) hB T g z).symm
  have h2 : actB (sQ l) T g (m • v) =
      toB l O (((1 : O) ⊗ₜ[ℤ_[l]] (u : Ainf l)) ^ k) • (m • actB (sQ l) T g v) := by
    rw [actB, GlobalTheory.Cyc.Decomp.TWact_smul, hm, ← hB, hμ, map_mul, mul_smul]
  have h3 : m • actB (sQ l) T g v =
      TWincl (toB l O) T ((((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k) • w) := by
    rw [GlobalTheory.Cyc.Decomp.TWincl_smul, ← h1, h2, smul_smul, ← map_mul, hinv, map_one, one_smul]
  refine ⟨(((1 : O) ⊗ₜ[ℤ_[l]] ((u⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ k) • w - z, ?_⟩
  rw [smul_sub, h3, hv, map_sub]

end GlobalTheory.BKGal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodRingNoZeroDivisors
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisNZD

theorem eq_zero_of_smul_free {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.Free R M] {a : R} (ha : a ≠ 0) {x : M} (h : a • x = 0) : x = 0 := by
  refine (Module.Free.chooseBasis R M).repr.injective (Finsupp.ext fun i => ?_)
  have h1 := congrArg (fun y => (Module.Free.chooseBasis R M).repr y i) h
  simp only [map_smul, map_zero, Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply] at h1 ⊢
  exact (mul_eq_zero.1 h1).resolve_left ha

theorem acris_dom (l : ℕ) [Fact l.Prime] : IsDomain (Per.Acris l) ∧ Function.Injective (aC l) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  haveI : IsDomain (Per.BdRp l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).1
  refine ⟨(GlobalTheory.MemLoc.crisP_injective l C.j C.j_cris).isDomain C.j, fun a b h => ?_⟩
  have h1 : C.j (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      C.j (algebraMap (Per.Ainf l) (Per.Acris l) b) := congrArg C.j h
  rw [C.j_cris.on_ainf, C.j_cris.on_ainf] at h1
  exact (GlobalTheory.MemLoc.ainf_isDomain_and_injective l).2.2 (GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective l h1)

variable {l : ℕ} [Fact l.Prime] (K : FinExt l)

theorem eq_zero_of_inC_mul {a : Ainf l} (ha : a ≠ 0) {z : CK K} (h : inC K (aC l a) * z = 0) : z = 0 := by
  haveI := (acris_dom l).1
  have ha' : aC l a ≠ 0 := fun h0 => ha ((acris_dom l).2 (h0.trans (map_zero _).symm))
  rw [← Algebra.smul_def] at h
  exact eq_zero_of_smul_free ha' h

theorem exists_dvd_inA {x : AK K} (hx : x ≠ 0) : ∃ N : Ainf l, N ≠ 0 ∧ ∃ w : AK K, inA K N = x * w := by
  obtain ⟨r, hr, w, hw⟩ := (IsIntegral.of_finite (Ainf l) x).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hx)
  exact ⟨r, hr, w, hw⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (x : AK K), x ≠ 0 → ∀ y : GlobalTheory.AcrisK.BK K,
    toB K (ofA K x) * y = 0 → y = 0 := by
  intro l _ K x hx y hy
  obtain ⟨N, hN, w, hw⟩ := exists_dvd_inA K hx
  obtain ⟨D, z, hz⟩ := exists_pow_mul y
  have h1 : toB K (ofA K x * z) = 0 := by
    rw [map_mul, ← hz, mul_left_comm, hy, mul_zero]
  have h2 : ofA K x * z = 0 := toB_injective K (h1.trans (map_zero _).symm)
  have h3 : inC K (aC l N) * z = 0 := by
    rw [← ofA_inA, hw, map_mul, mul_right_comm, h2, zero_mul]
  have h4 : z = 0 := eq_zero_of_inC_mul K hN h3
  rw [h4, map_zero] at hz
  exact ((isUnit_l K).pow D).mul_right_eq_zero.1 hz

end GlobalTheory.AcrisNZD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodTensorMapInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrisInj

theorem li_of_frac {W O F L ι : Type*} [CommRing W] [IsDomain W] [CommRing O] [Algebra W O] [Field F] [Field L]
    [Algebra F L] (o : O →+* L) (ho : Function.Injective o) (hW : Function.Injective (algebraMap W O))
    (hfrac : ∀ y : F, ∃ w s : W, s ≠ 0 ∧ algebraMap F L y * o (algebraMap W O s) = o (algebraMap W O w))
    (v : ι → O) (hv : LinearIndependent W v) : LinearIndependent F fun i => o (v i) := by
  classical
  rw [linearIndependent_iff'] at hv ⊢
  intro s g hg i hi
  choose w d hd h using hfrac
  have h1 : ∑ k ∈ s, (w (g k) * ∏ m ∈ s.erase k, d (g m)) • v k = 0 := ho (by
    rw [map_zero, map_sum, ← mul_zero (o (algebraMap W O (∏ m ∈ s, d (g m)))), ← hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← Finset.mul_prod_erase s _ hk, Algebra.smul_def, Algebra.smul_def]
    simp only [map_mul]
    rw [← h]
    ring)
  have h2 : w (g i) = 0 :=
    (mul_eq_zero.1 (hv s _ h1 i hi)).resolve_right (Finset.prod_ne_zero_iff.2 fun m _ => hd _)
  have h3 := h (g i)
  rw [h2, map_zero, map_zero] at h3
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact (algebraMap F L).injective (h4.trans (map_zero _).symm)
  · exact absurd (hW (ho (h4.trans (by rw [map_zero, map_zero])))) (hd _)

theorem eq_zero_of_sum_tmul {F V B ι : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup B] [Module F B]
    [Fintype ι] {v : ι → V} (hv : LinearIndependent F v) {β : ι → B} (h : ∑ i, v i ⊗ₜ[F] β i = 0) (i : ι) :
    β i = 0 := by
  classical
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ((Finsupp.lapply i : (ι →₀ F) →ₗ[F] F).comp hv.repr)
  have h1 : ∀ k, φ (v k) = (Finsupp.single k (1 : F)) i := fun k => by
    have hm : v k ∈ Submodule.span F (Set.range v) := Submodule.subset_span ⟨k, rfl⟩
    have := LinearMap.congr_fun hφ ⟨v k, hm⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hv.repr_eq_single k ⟨v k, hm⟩ rfl] at this
    exact this
  have h2 := congrArg (fun x => TensorProduct.lid F B (φ.rTensor B x)) h
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, h1, map_zero, Finsupp.single_apply] at h2
  simpa using h2

theorem exists_coord {W A O ι : Type*} [CommRing W] [CommRing A] [CommRing O] [Algebra W A] [Algebra W O]
    [Fintype ι] (b : Module.Basis ι W O) (z : A ⊗[W] O) : ∃ a : ι → A, z = ∑ i, a i ⊗ₜ[W] b i := by
  refine ⟨fun i => (Algebra.TensorProduct.basis A b).repr z i, ?_⟩
  conv_lhs => rw [← (Algebra.TensorProduct.basis A b).sum_repr z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem injective_abstract {A O C S F L B ι : Type*} [CommRing A] [CommRing O] [CommRing C] [CommRing S] [Field F]
    [Field L] [Algebra F L] [CommRing B] [Algebra F B] [Fintype ι] (p : A →+* C) (q : O →+* C) (t : C →+* S)
    (o : O →+* L) (κ : L →+* S) (hκ : ∀ c, κ (o c) = t (q c)) (v : ι → O)
    (hv : LinearIndependent F fun i => o (v i)) (hC : ∀ z : C, ∃ a : ι → A, z = ∑ i, p (a i) * q (v i))
    (u : S) (hu : IsUnit u) (hS : ∀ y : S, ∃ (D : ℕ) (z : C), u ^ D * y = t z) (j : A →+* B)
    (hj : Function.Injective j) (Λ : S →+* L ⊗[F] B) (h1 : ∀ c, Λ (κ c) = c ⊗ₜ[F] (1 : B))
    (h2 : ∀ a, Λ (t (p a)) = (1 : L) ⊗ₜ[F] j a) : Function.Injective Λ := by
  refine (injective_iff_map_eq_zero Λ).2 fun y hy => ?_
  obtain ⟨D, z, hz⟩ := hS y
  obtain ⟨a, rfl⟩ := hC z
  have h3 := congrArg Λ hz
  rw [map_mul, hy, mul_zero, map_sum, map_sum] at h3
  simp only [map_mul, ← hκ, h1, h2, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at h3
  have h4 : ∀ i, a i = 0 := fun i => hj ((eq_zero_of_sum_tmul hv h3.symm i).trans (map_zero j).symm)
  simp only [h4, map_zero, zero_mul, Finset.sum_const_zero] at hz
  exact (hu.pow D).mul_right_eq_zero.1 hz

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

theorem coe_thetaW (w : W0 K) :
    ((oK K (thetaW (fK K) K w) : ↥K.1) : Om l) = GlobalTheory.TameFrob.iotaO l (fK K) w :=
  (algebraMap (Om l) ℂ_[l]).injective
    (congrArg Subtype.val ((intToOC_thetaW _ K w).trans (intToOC_thetaW _ (unrExt l (fK K)) w).symm))

theorem exists_frac (y : ↥(K0 K)) : ∃ w s : W0 K, s ≠ 0 ∧
    algebraMap ↥(K0 K) ↥K.1 y * oK K (algebraMap (W0 K) ↥(OL K) s) = oK K (algebraMap (W0 K) ↥(OL K) w) := by
  have hy : (y : Om l) ∈ Kunr l (fK K) := by rw [Kunr_fK]; exact y.2
  obtain ⟨w, s, hs, h⟩ := GlobalTheory.TameFrob.exists_frac l (fK K) ⟨y, hy⟩
  refine ⟨w, s, hs, Subtype.ext ?_⟩
  rw [← coe_thetaW, ← coe_thetaW] at h
  exact h

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (B : Type) [CommRing B] [Algebra ↥(K0 K) B] (j : Per.Acris l →+* B),
    Function.Injective j → ∀ Λ : GlobalTheory.AcrisK.BK K →+* ↥K.1 ⊗[↥(K0 K)] B,
    (∀ c : ↥K.1, Λ (inK K c) = c ⊗ₜ[↥(K0 K)] (1 : B)) →
    (∀ a : Per.Acris l, Λ (toB K (inC K a)) = (1 : ↥K.1) ⊗ₜ[↥(K0 K)] j a) → Function.Injective Λ := by
  intro l _ K B _ _ j hj Λ h1 h2
  exact injective_abstract (inC K) (inI K) (toB K) (oK K) (inK K) (inK_oK K)
    (Module.Free.chooseBasis (W0 K) ↥(OL K))
    (li_of_frac (W := W0 K) (oK K) (IsFractionRing.injective ↥(OL K) ↥K.1) (thetaW_injective K) (exists_frac K) _
      (Module.Free.chooseBasis (W0 K) ↥(OL K)).linearIndependent)
    (fun z => (exists_coord (A := Per.Acris l) (Module.Free.chooseBasis (W0 K) ↥(OL K)) z).imp fun a ha =>
      ha.trans (Finset.sum_congr (M := CK K) rfl fun i _ => GlobalTheory.AcrisK.tmul_eq K _ _))
    (l : GlobalTheory.AcrisK.BK K) (isUnit_l K) exists_pow_mul j hj Λ h1 h2

end GlobalTheory.CrisInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperModCommutatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_upper_mem_inv_mul_pow_mem_of_commutator : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p e : ℕ) (v : ℝ) (C : Subgroup (L ≃ₐ[F] L)), (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F L v, ∃ τ ∈ upperRamificationGroup F L (min (2 * v) (v + e)), τ⁻¹ * σ ^ p ∈ C := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upper_mod_commutator | exact GlobalTheory.PMon.Ram.pow_mem_upper_mod_commutator | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upper_mod_commutator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeDvdAinfEnvelopeOfGaloisSections
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

set_option maxHeartbeats 1000000 in

theorem l_dvd_of_galois_sections : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, En.inl.f (bk.ev bk.E) ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)), s.comp En.inl = Hom.id _ → s.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ s.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  intro l _ K bk En κ _ x c h hx hs
  obtain ⟨-, -, -, -, -, -, hA7⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  obtain ⟨-, hM2, hM3⟩ := GlobalTheory.T.ainf_envelope_mod_prime_properties l K bk En
  let I : Ideal En.Q.A := Ideal.span {((l : ℕ) : En.Q.A)}
  let π : En.Q.A →+* En.Q.A ⧸ I := Ideal.Quotient.mk I
  have hπ : ∀ y, π y = 0 ↔ ((l : ℕ) : En.Q.A) ∣ y := fun y =>
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hl0 : ((l : ℕ) : En.Q.A ⧸ I) = 0 := by
    rw [← map_natCast π]; exact (hπ _).2 dvd_rfl
  have hreg : π (En.inl.f (bk.ev X)) ∈ nonZeroDivisors (En.Q.A ⧸ I) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : π (En.inl.f (bk.ev X) * y) = 0 := by rw [map_mul, mul_comm]; exact hy
    exact (hπ _).2 (hM2 y ((hπ _).1 this))
  have hE : π (En.inl.f (bk.ev bk.E)) = π (En.inl.f (bk.ev X)) ^ bk.Ep.natDegree := by
    let ι : Ainf l →+* En.Q.A := En.inl.f
    have h1 : ((l : ℕ) : En.Q.A) ∣ ι (bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree) := by
      have := map_dvd ι hA7
      rwa [map_natCast] at this
    have h2 := (hπ _).2 h1
    rw [map_sub, map_pow, map_sub, map_pow, sub_eq_zero] at h2
    exact h2
  have hl1 : π ((l : ℕ) : En.Q.A) = 0 := (hπ _).2 dvd_rfl
  have hφ : ∀ y, π (En.Q.D.φ y) = π y ^ l := fun y => by
    have e : π (En.Q.D.φ y - y ^ l) = 0 := (hπ _).2 ⟨En.Q.D.δ y, by rw [En.Q.D.φ_eq y]; ring⟩
    rwa [map_sub, map_pow, sub_eq_zero] at e
  have heq : ∀ j, π (En.inl.f (bk.ev X)) ^ (bk.Ep.natDegree * h) * π (x j) =
      ∑ i, π (x i) ^ l * π (c i j) := fun j => by
    have := congrArg π (hx j)
    rw [map_mul π, map_pow π, hE, ← pow_mul, map_sum π] at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul π, hφ]
  have hpts : ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (f : En.Q.A ⧸ I →+* O), f (π (En.inl.f (bk.ev X))) ≠ 0 → ¬ IsUnit (f (π (En.inl.f (bk.ev X)))) →
      IsAdicComplete (Ideal.span {f (π (En.inl.f (bk.ev X)))}) O → ∀ j, f (π (x j)) = 0 := by
    intro O _ _ _ _ _ f hf0 hfu hfc j
    obtain ⟨g, s, ψ, h1, h2, h3⟩ := GlobalTheory.T.breuilKisinEnvelope_point_factors_through_section l K bk En O (f.comp π) hf0 hfu hfc
    obtain ⟨z, hz⟩ := hs g s h1 h2 j
    have e := h3 (x j)
    rw [RingHom.comp_apply] at e
    rw [e, hz]
    have : WittVector.coeff (p := l) (R := OCb l) (((l : ℕ) : (ainfObj K).A) * z) 0 = 0 := by
      rw [mul_comm]; exact WittVector.mul_charP_coeff_zero (p := l) (R := OCb l) z
    rw [this, map_zero]
  have key := GlobalTheory.T.dvd_all_pow_of_frobenius_eq_killed_by_perfect_points l (En.Q.A ⧸ I) (π (En.inl.f (bk.ev X))) hl0 hreg κ (fun i => π (x i))
    (fun i j => π (c i j)) (bk.Ep.natDegree * h) heq (fun O _ _ _ _ _ f hf0 hfu hfc j => hpts O f hf0 hfu hfc j)
  intro j
  refine hM3 (x j) fun m => ?_
  obtain ⟨w, hw⟩ := key m j
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨z, (hπ _).1 ?_⟩
  change π (x j) = π (En.inl.f (bk.ev X)) ^ m * π z at hw
  rw [map_sub π, map_mul π, map_pow π, hw, sub_self]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCrystalChangeOfBasisConstantCoeffEqOneStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismCrystal_changeOfBasis_constantCoeff_eq_one : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (κ : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (κ₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, κ₀ τ (δ.f y) = PowerSeries.constantCoeff (κ τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), κ τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ τ, (Matrix.of fun i j => ∑ q, c i j q • κ τ (y i j q)).map PowerSeries.constantCoeff = 1 := by
  first | exact @GlobalTheory.CrysDiag.eps_constantCoeff_eq_one | exact GlobalTheory.CrysDiag.eps_constantCoeff_eq_one | (intros; apply GlobalTheory.CrysDiag.eps_constantCoeff_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (a : ℕ) (A : Matrix (Fin d) (Fin d) bk.S), (∀ j : Fin d, IsFrac (bk.toP bk.E) (M.Φ bk.prism ⟨bk.toP bk.E, Ideal.mem_span_singleton_self _⟩ (e j)) (∑ i, bk.toP (A i j) • e i) a) → ∀ (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q) (t : ↥Q.I) (y : Fin d → Q.A) (m : M.M Q) (k : ℕ), IsFrac (t : Q.A) (M.Φ Q t (∑ j, y j • M.tr g (e j))) m k → ∃ r : ℕ, (t : Q.A) ^ r • (BK.hf g bk.E ^ a • m - (t : Q.A) ^ k • ∑ i, (A.map (BK.hf g)).mulVec (fun j => Q.D.φ (y j)) i • M.tr g (e i)) = 0 := by
  first | exact @GlobalTheory.BSP.frob_tr_basis | exact GlobalTheory.BSP.frob_tr_basis | (intros; apply GlobalTheory.BSP.frob_tr_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdIdeleCharacterEqOneOfTotallyPositive
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
  GlobalTheory.NormCompat

namespace GlobalTheory.ProdLocUnitPos

theorem prod_locUnit_eq_one_of_pos : ∀ (F : Type) [Field F] [NumberField F] (B : Type) [CommGroup B] (ψ : Neutral.B1.Ideles F →* B), IsOpen (ψ.ker : Set (Neutral.B1.Ideles F)) → (∀ k : Fˣ, ψ (Neutral.B1.diagUnits F k) = 1) → (∀ y ∈ GlobalTheory.HeckeGal.infConn F, ψ y = 1) → ∀ a : Fˣ, (∀ φ : F →+* ℝ, 0 < φ (a : F)) → ∀ T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), (∀ v ∉ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1) → ∏ v ∈ T, ψ (GlobalTheory.NormCompat.locUnit F v a) = 1 := by
  intro F _ _ B _ ψ hker hd hconn a ha T hT
  classical
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  have hψ : Continuous ψ := continuous_of_isOpen_ker' ψ hker
  let ι : (InfiniteAdeleRing F)ˣ →* Ideles F :=
    Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let P : Ideles F →* (InfiniteAdeleRing F)ˣ :=
    Units.map (MonoidHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let u : (InfiniteAdeleRing F)ˣ := P (diagUnits F a)
  have hu : u ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing F)ˣ :=
    GlobalTheory.RayFromArtin.mem_connectedComponentOfOne_of_pos a ha
  have hinf : ψ (ι u) = 1 := hconn _ ⟨u, hu, rfl⟩
  let av : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletion F)ˣ :=
    fun v => Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  let z : Ideles F := diagUnits F a * (ι u)⁻¹ * (∏ v ∈ T, locUnit F v a)⁻¹
  have hPι : P (ι u) = u := Units.ext rfl
  have hPl : ∀ v, P (locUnit F v a) = 1 := fun v => Units.ext rfl
  have hz1 : (z : AdeleRing (𝓞 F) F).1 = 1 := by
    have h : P z = 1 := by
      simp only [z, map_mul, map_inv, map_prod, hPι, hPl, Finset.prod_const_one, inv_one, mul_one]
      exact mul_inv_cancel u
    exact congrArg Units.val h
  have hev_d : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (diagUnits F a) = av v := fun v => Units.ext rfl
  have hev_i : ∀ v, Units.map (GlobalTheory.Mem.LocTriv.ev v) (ι u) = 1 := fun v => Units.ext rfl
  have hev_l : ∀ v w, Units.map (GlobalTheory.Mem.LocTriv.ev v) (locUnit F w a) = if w = v then av v else 1 := by
    intro v w
    apply Units.ext
    split_ifs with h
    · subst h
      exact GlobalTheory.Mem.LocTriv.ev_local_self w _
    · exact GlobalTheory.Mem.LocTriv.ev_local_ne (Ne.symm h) _
  have hzl : ∀ v, ψ (localIdele F v (Units.map (GlobalTheory.Mem.LocTriv.ev v) z)) = 1 := by
    intro v
    have e : Units.map (GlobalTheory.Mem.LocTriv.ev v) z = av v * (∏ w ∈ T, if w = v then av v else 1)⁻¹ := by
      simp only [z, map_mul, map_inv, map_prod, hev_d, hev_i, hev_l, inv_one, mul_one]
    rw [e, Finset.prod_ite_eq' T v]
    split_ifs with hv
    · rw [mul_inv_cancel, map_one, map_one]
    · rw [inv_one, mul_one]
      exact hT v hv
  have hz := GlobalTheory.FrobDense.eq_one_of_local ψ hψ z hz1 hzl
  simp only [z, map_mul, map_inv, map_prod, hd, hinf, inv_one, one_mul] at hz
  exact inv_eq_one.mp hz

end GlobalTheory.ProdLocUnitPos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RayClassFieldInfModulusEqSupStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rayClassField_inf_modulus_eq_sup : ∀ {K H H₁ H₂ : Type} [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsAbelianGalois K H] [Field H₁] [NumberField H₁] [Algebra K H₁] [IsAbelianGalois K H₁] [Field H₂] [NumberField H₂] [Algebra K H₂] [IsAbelianGalois K H₂], (∀ u : (𝓞 K)ˣ, u = 1 ∨ u = -1) → ∀ {𝔞 𝔟 : Ideal (𝓞 K)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → ∀ {q : ℕ}, q.Prime → q ≠ 2 → 𝔞 ≤ Ideal.span {(q : 𝓞 K)} → 𝔟 ≤ Ideal.span {(q : 𝓞 K)} → GlobalTheory.FieldSize.IsRay H (𝔞 ⊓ 𝔟) → GlobalTheory.FieldSize.IsRay H₁ 𝔞 → GlobalTheory.FieldSize.IsRay H₂ 𝔟 → ∀ (f₁ : H₁ →ₐ[K] H) (f₂ : H₂ →ₐ[K] H), f₁.fieldRange ⊔ f₂.fieldRange = ⊤ := by
  first | exact @GlobalTheory.RayCompositum.fieldRange_sup_eq_top | exact GlobalTheory.RayCompositum.fieldRange_sup_eq_top | (intros; apply GlobalTheory.RayCompositum.fieldRange_sup_eq_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBoundOfAuxiliaryPrimesOdd
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel

theorem residual_bound_of_parts : Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → Gen.ArchimedeanSignatureMatching → GreenbergWiles → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X), ResidualBoundOddPrimes bkP := by
  intro hC hPT hCD hT hLF hLT hLE hGF hGE hU hA _ D N X bkP
  have hgw : ∀ i s, GalHyp bkP i s → EqDim bkP i s := fun i s h =>
    GlobalTheory.T.residual_selmer_finrank_eq_dual hC hPT hCD hT hLF hLT hLE hGF hGE hU hA D N X bkP i s h
  refine GlobalTheory.T.residual_bound_of_components D N X bkP (fun i => GlobalTheory.T.exists_auxiliary_primes_prescribed_frobenius hC D N X i)
    (fun i => GlobalTheory.T.exists_elements_selmerForms_small_corank hGF D N X bkP i fun s h =>
      ⟨GlobalTheory.T.cocycleFormsSpan_oddResidueChar D N X bkP i s h, GlobalTheory.T.span_two_of_galois_hypothesis D N X bkP i s h, hgw i s h⟩)
    (fun i s h => ?_)
  have hk := GlobalTheory.T.firstHalfLocalCohomologyVanishing_of_localDualityTheorems hLF hLT hLE hT D N X bkP i s h
  exact GlobalTheory.T.residual_selmer_determinant_order_bound hT D N X bkP i s h hk
    (GlobalTheory.T.reciprocity_auxiliaryPlaces_secondHalf hC hPT hCD hT hLF hLT hLE hGF hGE hU hA D N X bkP i s h hk) (hgw i s h)

end GlobalTheory.ResSel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurPolynomialPadZerosEqJacobiTrudiDeterminantStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurPolynomial_padZeros_eq_jacobiTrudiDeterminant : ∀ {m n : ℕ} (hmn : m ≤ n) (l : Fin m → ℕ),
    GlobalTheory.JSW.schur n (GlobalTheory.JSW.padTo hmn l) = GlobalTheory.JSW.jtDet m (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := by
  first | exact @GlobalTheory.JSW.schur_padTo_eq_jtDet | exact GlobalTheory.JSW.schur_padTo_eq_jtDet | (intros; apply GlobalTheory.JSW.schur_padTo_eq_jtDet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsGaloisFixingFlatStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistable_periods_galois_fixing_flat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ g : ↥(GK K), bk.FixFlat g → ∀ G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (Per.σA (g : GQ l)) G → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev j → ∀ x, G (j x) = j x) ∧ bk.iA τ ^ s.N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G) = G (bk.iA τ) ^ s.N • s.W := by
  first | exact @GlobalTheory.BKLim.wseed_gal_periods | exact GlobalTheory.BKLim.wseed_gal_periods | (intros; apply GlobalTheory.BKLim.wseed_gal_periods; all_goals assumption)
end

