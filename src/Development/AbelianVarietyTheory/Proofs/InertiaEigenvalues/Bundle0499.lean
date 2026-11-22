import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0476
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0467
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0438
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDualLatticeIsOpenPerfectPairing
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDual

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_dualLat_isOpen : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O →
    (∀ g, ∃ u : Oˣ, ((cycLL PD LL g : LLˣ) : LL) = algebraMap O LL (u : O)) →
    ∀ (U U' : GRep G Qp LL O) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL), IsDual1 PD U.ρ U'.ρ P →
    ∀ LT : Lattice (O := O) U.ρ, ∃ LT' : Lattice (O := O) U'.ρ, IsDualLat1 PD LT LT' P ∧ IsOpen (LT'.T : Set U'.V) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ hO hcyc U U' P hP LT

  obtain ⟨⟨hdom, hdvr, hfr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hfr
  haveI : Module.Finite O LT.T := Module.Finite.iff_fg.mpr LT.fg
  haveI : Module.Free O LT.T := LT.free
  let b := Module.Free.chooseBasis O LT.T
  let e : Module.Free.ChooseBasisIndex O LT.T → U.V := fun i => (b i : U.V)
  have he_O : LinearIndependent O e := b.linearIndependent.map' LT.T.subtype (Submodule.ker_subtype _)
  have he_L : LinearIndependent LL e := (LinearIndependent.iff_fractionRing O LL).mp he_O
  have hspanO : Submodule.span O (Set.range e) = LT.T := by
    have h1 : Set.range e = LT.T.subtype '' Set.range b := (Set.range_comp _ _)
    rw [h1, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspanL : Submodule.span LL (Set.range e) = ⊤ := by
    rw [← Submodule.span_span_of_tower O LL (Set.range e), hspanO]; exact LT.span
  let bL := Basis.mk he_L (le_of_eq hspanL.symm)
  have hbL : ∀ i, bL i = e i := fun i => Basis.mk_apply _ _ _
  let φ : U'.V →ₗ[LL] (Module.Free.ChooseBasisIndex O LT.T → LL) := LinearMap.pi (fun i => P (e i))
  have hφ : ∀ y i, φ y i = P (e i) y := fun _ _ => rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hP.2.2.1 y
    intro x
    have h1 : P.flip y = 0 := bL.ext (fun i => by
      rw [hbL]; simpa [hφ] using congrFun hy i)
    simpa using LinearMap.congr_fun h1 x
  have hdim : finrank LL U'.V = finrank LL (Module.Free.ChooseBasisIndex O LT.T → LL) := by
    rw [← hP.2.2.2, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis bL]
  have hφsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hφinj
  let φe : U'.V ≃ₗ[LL] (Module.Free.ChooseBasisIndex O LT.T → LL) := LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  let bf := (Pi.basisFun LL (Module.Free.ChooseBasisIndex O LT.T)).map φe.symm
  have hφf : ∀ i j, P (e j) (bf i) = (Pi.single i (1 : LL) : Module.Free.ChooseBasisIndex O LT.T → LL) j := fun i j => by
    have : φ (bf i) = Pi.single i 1 := by
      simp only [bf, Basis.map_apply, Pi.basisFun_apply]
      exact φe.apply_symm_apply _
    exact congrFun this j
  let T' : Submodule O U'.V :=
    { carrier := {y | ∀ x ∈ LT.T, ∃ a : O, P x y = algebraMap O LL a}
      add_mem' := by
        intro y z hy hz x hx
        obtain ⟨a, ha⟩ := hy x hx
        obtain ⟨c, hc⟩ := hz x hx
        exact ⟨a + c, by simp [ha, hc]⟩
      zero_mem' := fun x _ => ⟨0, by simp⟩
      smul_mem' := by
        intro c y hy x hx
        obtain ⟨a, ha⟩ := hy x hx
        refine ⟨c * a, ?_⟩
        show P x (c • y) = _
        rw [← algebraMap_smul LL c y, map_smul, ha, smul_eq_mul, map_mul] }
  have hmem : ∀ y, y ∈ T' ↔ ∀ x ∈ LT.T, ∃ a : O, P x y = algebraMap O LL a := fun y => Iff.rfl
  have hmem' : ∀ y, y ∈ T' ↔ ∀ i, P (e i) y ∈ Set.range (algebraMap O LL) := by
    intro y; constructor
    · intro hy i; obtain ⟨a, ha⟩ := hy (e i) (b i).2; exact ⟨a, ha.symm⟩
    · intro hy x hx
      choose a ha using hy
      have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • e i := by
        have h2 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at h2
        exact h2.symm
      obtain ⟨c, hcx⟩ : ∃ c : Module.Free.ChooseBasisIndex O LT.T → O, x = ∑ i, c i • e i := ⟨_, hx'⟩
      refine ⟨∑ i, c i * a i, ?_⟩
      rw [hcx, map_sum, LinearMap.sum_apply, map_sum (algebraMap O LL)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← algebraMap_smul LL (c i) (e i), map_smul, LinearMap.smul_apply, ← ha i,
        smul_eq_mul, map_mul]
  have hf_mem : ∀ i, bf i ∈ T' := fun i => (hmem' _).mpr fun j => by
    rw [hφf]
    refine ⟨(Pi.single i (1 : O) : Module.Free.ChooseBasisIndex O LT.T → O) j, ?_⟩
    rcases eq_or_ne j i with rfl | h
    · simp
    · simp [Pi.single_apply, h]
  have hT'eq : T' = Submodule.span O (Set.range bf) := by
    apply le_antisymm
    · intro y hy
      choose a ha using (hmem' y).mp hy
      have hy' : y = ∑ i, a i • bf i := by
        apply hφinj
        funext j
        rw [hφ, hφ, map_sum, ← ha j]
        simp_rw [← algebraMap_smul LL (a _) (bf _), map_smul, hφf, Pi.single_apply, smul_eq_mul,
          mul_ite, mul_one, mul_zero]
        simp
      rw [hy']
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hf_mem i
  have hfO : LinearIndependent O bf := (LinearIndependent.iff_fractionRing O LL).mpr bf.linearIndependent
  have hstab : ∀ g, ∀ y ∈ T', U'.ρ g y ∈ T' := by
    intro g y hy x hx
    obtain ⟨u, hu⟩ := hcyc g
    obtain ⟨a, ha⟩ := hy (U.ρ g⁻¹ x) (LT.stable g⁻¹ x hx)
    refine ⟨u * a, ?_⟩
    have hx' : U.ρ g (U.ρ g⁻¹ x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h3 := hP.1 g (U.ρ g⁻¹ x) y
    rw [hx'] at h3
    rw [h3, hu, ha, map_mul]
  have hopenT : IsOpen (T' : Set U'.V) := by
    have h4 : (T' : Set U'.V) = ⋂ i, (fun y => P (e i) y) ⁻¹' Set.range (algebraMap O LL) := by
      ext y; simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]; exact hmem' y
    rw [h4]
    exact isOpen_iInter_of_finite
      (fun i => hopen.preimage (IsModuleTopology.continuous_of_linearMap (R := LL) (P (e i))))
  refine ⟨⟨T', hstab, ?_, ?_, ?_⟩, ⟨hP, hmem⟩, hopenT⟩
  · rw [hT'eq]; exact Submodule.fg_span (Set.finite_range _)
  · rw [hT'eq]; exact Module.Free.of_basis (Basis.span hfO)
  · rw [hT'eq, Submodule.span_span_of_tower O LL]; exact bf.span_eq

end GlobalTheory.Pass.LocDual

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowMulPhiMatrixInvAhat
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.CoordInv

section Gen

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem E_pow_mem_RpiE (N : ℕ) : E K l e ^ N ∈ RpiE O K l e :=
  le_away _ _ (A_le_Rpi l e (pow_mem (E_mem l e (A O K)) N))

theorem E_mem_RpiE : E K l e ∈ RpiE O K l e :=
  le_away _ _ (A_le_Rpi l e (E_mem l e (A O K)))

theorem hat_E_pow (N : ℕ) :
    hat O l e (E K l e ^ N) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N := by
  induction N with
  | zero => simpa using (hat_coe (O := O) (K := K) l e 1).trans (map_one _)
  | succ n ih =>
    rw [pow_succ, hat_mul l e (E_pow_mem_RpiE n) E_mem_RpiE, ih, hat_E, pow_succ]

theorem main [NeZero a] (P : PhiMod O K l e a ι) :
    ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e), ∀ τ j i,
      algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i) := by
  choose n hn using fun p : ZMod a × ι × ι => mem_away.1 (P.mxInv_mem p.1 p.2.1 p.2.2)
  have hN : ∀ p : ZMod a × ι × ι, E K l e ^ Finset.univ.sup n * P.mxInv p.1 p.2.1 p.2.2 ∈ A O K := by
    intro p
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ p))
    rw [hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (E_mem l e _) c) (by simpa using hn p)
  refine ⟨Finset.univ.sup n, fun τ j i => ofA O K l e ⟨_, hN (τ, j, i)⟩, fun τ j i => ?_⟩
  rw [← hat_coe_A, hat_mul l e (E_pow_mem_RpiE _) (invE_A_le_RpiE l e (P.mxInv_mem τ j i)), hat_E_pow]

end Gen

end GlobalTheory.BK.CoordInv

open GlobalTheory.BK.CoordInv in
theorem GlobalTheory.BK.coordE_mxInv : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι), ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i) := by
  intro l _ a e _ _ _ LL _ _ ι _ _ P
  exact main P
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtFixing
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.HodgeAt

theorem phiS_idem : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L : FinExt l) [FiniteDimensional ℚ_[l] ↥K.1] (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (σ : GQ l), (∀ x : ↥K.1, σ ((τ x : ↥L.1) : Om l) = (x : Om l)) → phiS P σ L (GlobalTheory.DRFil.idem P.R.BdR τ) = 1 := by
  intro l _ P K L _ τ σ hσ
  obtain ⟨n, a, c, h, h1⟩ := GlobalTheory.DRFil.idem_repr P.R.BdR τ
  rw [h, map_sum]
  simp only [phiS_tmul]
  have hc : ∀ i, algebraMap ↥K.1 P.R.BdR (c i) = algebraMap (Om l) P.R.BdR ((c i : ↥K.1) : Om l) := fun i => rfl
  simp only [hc, ← map_mul, ← map_sum]
  have : ∑ i, σ ((a i : ↥L.1) : Om l) * ((c i : ↥K.1) : Om l) = σ (((∑ i, a i * τ (c i) : ↥L.1)) : Om l) := by
    simp only [IntermediateField.coe_sum, IntermediateField.coe_mul, map_sum, map_mul, hσ]
  rw [this, h1]
  simp

theorem phiS_mem_Fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K L : FinExt l) (σ : GQ l) (n : ℤ) (r : ↥L.1 ⊗[ℚ_[l]] P.R.BdR), r ∈ FilV (P.PD K) (LL := ↥L.1) (V := ↥L.1) n → phiS P σ L r ∈ (P.PD K).Fil n := by
  intro l _ P AI T K L σ n r hr
  have h0 : ∀ x : Om l, algebraMap (Om l) P.R.BdR x ∈ (P.PD K).Fil 0 := by
    intro x
    rw [T.fil]
    obtain ⟨y, hy, -⟩ := T.om x
    rw [hy]
    exact ((GlobalTheory.MemLoc.filD_laws l).2.2.2.2.2.2 0 y).2 (GlobalTheory.MemLoc.FilSeed.mem_filtration_zero' y)
  refine GlobalTheory.DRFil.FilV_induction (P.PD K) (p := fun r => phiS P σ L r ∈ (P.PD K).Fil n) ?_ ?_ ?_ hr
  · simp
  · intro c b hb
    rw [phiS_tmul]
    simpa using (P.PD K).Fil_mul 0 n _ _ (h0 _) hb
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

end GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem exists_ext_fixing : ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (σ : GQ l), ∃ K' : FinExt l, K.1 ≤ K'.1 ∧ ∀ g ∈ GK K', ∀ y : ↥L.1, g (σ (y : Om l)) = σ (y : Om l) := by
  intro l _ K L σ
  haveI := K.2
  haveI := L.2
  haveI : FiniteDimensional ℚ_[l] ↥(L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l)) :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap L.1 (σ : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv
  refine ⟨⟨K.1 ⊔ L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l), IntermediateField.finiteDimensional_sup _ _⟩, le_sup_left, ?_⟩
  intro g hg y
  have hmem : σ (y : Om l) ∈ K.1 ⊔ L.1.map (σ : Om l →ₐ[ℚ_[l]] Om l) :=
    le_sup_right (a := K.1) ((IntermediateField.mem_map _).2 ⟨y, y.2, rfl⟩)
  exact (mem_fixingSubgroup_iff _).1 hg _ hmem

end GlobalTheory.HodgeAt

namespace GlobalTheory.HodgeAt

theorem exists_xi_pow_mul : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l) (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (K : FinExt l) (k : ℤ) (q p : ℕ), k + q = p → ∀ x ∈ (P.PD K).Fil k, ∃ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ q * T.eD x = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ ^ p * z) := by
  intro l _ P AI T C ξ hξ K k q p hkp x hx
  obtain ⟨hP, -, -, -, -, hshift, -⟩ := GlobalTheory.MemLoc.seed_fil l C ξ hξ
  rw [T.fil] at hx
  have hy := (hshift k q (T.eD x)).2 hx
  rw [hkp] at hy
  obtain ⟨y, hye⟩ := (GlobalTheory.MemLoc.mem_FilD_iff_xi_pow l C.ε (GlobalTheory.MemLoc.core_isEps l C) p _).1 hy
  have h0 : (-(p : ℤ)).toNat = 0 := by omega
  rw [h0, pow_zero, mul_one, Int.toNat_natCast] at hye
  have hz : aDp l (xi C.ε) ^ p * y ∈ Per.FilP l p :=
    ((GlobalTheory.MemLoc.filtration_eq_xi_pow l C.ε (GlobalTheory.MemLoc.core_isEps l C)).1 p _).2 (dvd_mul_right _ _)
  rw [hP, Ideal.mem_span_singleton'] at hz
  obtain ⟨z', hz'⟩ := hz
  refine ⟨z', ?_⟩
  rw [mul_comm (aDp l ξ ^ p) z', hz', hye]

end GlobalTheory.HodgeAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteCoefficientSetFrobeniusCharpolys
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.FrobSysCoef

theorem main : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (Formalism.ConjugateSelfDual.G E Ω)) (p : Formalism.ConjugateSelfDual.G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, ι.symm z ∈ K) → ∀ ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep ρ → (∀ σ ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) → ∃ Pm : GL (Fin a) (Qbar l), ∀ g s t, ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  intro l _ ι E Ω _ _ _ _ _ a U p hU
  classical
  by_cases hex : ∃ ρ₀ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l),
      Continuous (fun g => ((ρ₀ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) ∧ IsSSRep ρ₀ ∧
      (∀ σ ∈ U, ((ρ₀ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ)
  · obtain ⟨ρ₀, hc₀, hs₀, hp₀⟩ := hex
    obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.galoisRep_entries_mem_of_finset l E Ω a ρ₀ hc₀
    refine ⟨S₀.image ι, fun K hK ρ hc hs hp => ?_⟩
    have hK' : ∀ z ∈ S₀, z ∈ K := fun z hz => by
      simpa using hK (ι z) (Finset.mem_image_of_mem _ hz)
    have hU' : ∀ σ ∈ U, ((ρ₀ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
        ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := fun σ hσ =>
      Polynomial.map_injective ι.toRingHom ι.injective ((hp₀ σ hσ).trans (hp σ hσ).symm)
    have hall := GlobalTheory.charpoly_eq_of_eqOn_dense _ _ hc₀ hc U hU hU'
    obtain ⟨Pm, hPm⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ₀ ρ hs₀ hs hall
    refine ⟨Pm⁻¹, fun g s t => ?_⟩
    have : Pm⁻¹⁻¹ * ρ g * Pm⁻¹ = ρ₀ g := by
      rw [hPm g, inv_inv]; group
    rw [this]
    exact hS₀ K hK' g s t
  · refine ⟨∅, fun K _ ρ hc hs hp => ?_⟩
    exact absurd ⟨ρ, hc, hs, hp⟩ hex

end GlobalTheory.FrobSysCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSliceMemRightDivisorSet
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.RdivSlice

theorem frobSlice_frob_mul {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime] {i : ℕ} (hi : i < l)
    (f z : K⟦X⟧) : frobSlice l i (frob K l f * z) = f * frobSlice l i z := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  rw [coeff_frobSlice, coeff_mul, coeff_mul]
  symm
  refine Finset.sum_of_injOn (fun p : ℕ × ℕ => (l * p.1, l * p.2 + i)) ?_ ?_ ?_ ?_
  · rintro ⟨p, q⟩ - ⟨p', q'⟩ - h
    simp only [Prod.mk.injEq, add_left_inj] at h ⊢
    exact ⟨Nat.eq_of_mul_eq_mul_left hl h.1, Nat.eq_of_mul_eq_mul_left hl h.2⟩
  · rintro ⟨p, q⟩ h
    simp only [Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal] at h ⊢
    rw [← h]; ring
  · rintro ⟨p, q⟩ h hn
    rw [coeff_frob]
    split_ifs with hd
    · exfalso
      obtain ⟨t, rfl⟩ := hd
      simp only [Finset.HasAntidiagonal.mem_antidiagonal] at h
      have ht : t ≤ n := by
        by_contra hc
        have : l * (n + 1) ≤ l * t := Nat.mul_le_mul_left l (by omega)
        rw [mul_add, mul_one] at this
        omega
      obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
      refine hn ⟨(t, s), by simp, ?_⟩
      rw [mul_add] at h
      simp only [Prod.mk.injEq, true_and]
      omega
    · simp
  · rintro ⟨p, q⟩ -
    simp only [coeff_frob, coeff_frobSlice, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hl]

theorem frobSlice_sum {K : Type} [Field K] (l i : ℕ) {μ : Type} (s : Finset μ) (f : μ → K⟦X⟧) :
    frobSlice l i (∑ j ∈ s, f j) = ∑ j ∈ s, frobSlice l i (f j) := by
  ext n
  simp only [coeff_frobSlice, map_sum]

theorem bdd_matrix_mul {K : Type} [NormedField K] [IsUltrametricDist K] {μ ν ρ : Type} [Fintype ν]
    {Y : Matrix μ ν K⟦X⟧} {Z : Matrix ν ρ K⟦X⟧} (hY : ∃ c : ℝ, ∀ i j n, ‖coeff n (Y i j)‖ ≤ c)
    (hZ : ∃ c : ℝ, ∀ i j n, ‖coeff n (Z i j)‖ ≤ c) :
    ∃ c : ℝ, ∀ i j n, ‖coeff n ((Y * Z) i j)‖ ≤ c := by
  obtain ⟨a, ha⟩ := hY
  obtain ⟨b, hb⟩ := hZ
  refine ⟨max a 0 * max b 0, fun i j n => ?_⟩
  rw [Matrix.mul_apply, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ => ?_
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    (le_max_right a 0) (le_max_right b 0) (f := Y i k) (g := Z k j)
    (fun m => by rw [mul_one]; exact (ha i k m).trans (le_max_left _ _))
    (fun m => by rw [mul_one]; exact (hb k j m).trans (le_max_left _ _)) n

theorem exists_pow_smul_bdd {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} [NeZero a] {μ : Type} [Fintype μ]
    (Y : ZMod a → Matrix μ μ K⟦X⟧) (hY : ∀ τ i j, Y τ i j ∈ invE l e (A O K)) :
    ∃ N : ℕ, ∀ τ i j n, ‖coeff n ((E K l e ^ N • Y τ) i j)‖ ≤ 1 := by
  choose n hn using fun p : ZMod a × μ × μ => hY p.1 p.2.1 p.2.2
  refine ⟨Finset.univ.sup n, fun τ i j => ?_⟩
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i, j)))
  rw [Matrix.smul_apply, smul_eq_mul, hc, pow_add, mul_assoc]
  exact mem_A.1 (mul_mem (pow_mem (E_mem l e (A O K)) c) (hn (τ, i, j)))

theorem exists_frobSlice_mem_rdivSet : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ∃ M : ℕ, ∀ τ, ∀ h ∈ F.rdivSet τ, ∀ i < l, frobSlice l i (E K l e ^ M * h) ∈ F.rdivSet (τ - 1) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  obtain ⟨α, hα⟩ := exists_pow_smul_bdd P.mxInv P.mxInv_mem
  obtain ⟨β, hβ⟩ := exists_pow_smul_bdd Q.mx Q.mx_mem
  refine ⟨α + β, fun τ h hh i hi => ?_⟩
  obtain ⟨hb, Y, hY, hFY⟩ := hh
  obtain ⟨c, hc⟩ := GlobalTheory.BK.Hom.bdd_mul (f := E K l e ^ (α + β))
    ⟨1, mem_A.1 (pow_mem (E_mem l e (A O K)) _)⟩ hb
  obtain ⟨d, hd⟩ := bdd_matrix_mul (bdd_matrix_mul ⟨1, hα τ⟩ hY) ⟨1, hβ τ⟩
  have h1 : (F.mat (τ - 1)).map (frob K l) * P.mxInv τ = Q.mxInv τ * F.mat τ := by
    calc _ = Q.mxInv τ * (Q.mx τ * (F.mat (τ - 1)).map (frob K l)) * P.mxInv τ := by
          rw [← Matrix.mul_assoc, Q.mxInv_mul_mx, Matrix.one_mul]
      _ = _ := by
          rw [← F.comm, Matrix.mul_assoc, Matrix.mul_assoc, P.mx_mul_mxInv, Matrix.mul_one]
  have h2 : (F.mat (τ - 1)).map (frob K l) *
      ((E K l e ^ α • P.mxInv τ) * Y * (E K l e ^ β • Q.mx τ)) =
      (E K l e ^ (α + β) * h) • (1 : Matrix κ κ K⟦X⟧) := by
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc (Q.mxInv τ), hFY,
      Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Q.mxInv_mul_mx, smul_smul, smul_smul,
      pow_add]
  refine ⟨⟨c, fun n => by rw [coeff_frobSlice]; exact hc _⟩,
    ((E K l e ^ α • P.mxInv τ) * Y * (E K l e ^ β • Q.mx τ)).map (frobSlice l i),
    ⟨d, fun s t n => by rw [Matrix.map_apply, coeff_frobSlice]; exact hd _ _ _⟩, ?_⟩
  ext1 s t
  have h3 := congrArg (fun M : Matrix κ κ K⟦X⟧ => frobSlice l i (M s t)) h2
  simp only [Matrix.mul_apply (M := (F.mat (τ - 1)).map (frob K l)), frobSlice_sum,
    Matrix.map_apply, frobSlice_frob_mul l hi] at h3
  rw [Matrix.mul_apply]
  simp only [Matrix.map_apply]
  rw [h3, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs
  · simp
  · ext n
    simp [coeff_frobSlice]

end GlobalTheory.BK.RdivSlice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFundamentalDomainRationalUpperUnitriangulaStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fundamentalDomain_rational_upperUnitriangular : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure], ∃ D : Set (GlobalTheory.CellDec.NA E n),
    IsFundamentalDomain ((GlobalTheory.CellDec.NE E n).subgroupOf (GlobalTheory.CellDec.NA E n)) D ν ∧ 0 < ν D ∧ ν D < ⊤ := by
  first | exact @GlobalTheory.CellDec.exists_fundamentalDomain_NE | exact GlobalTheory.CellDec.exists_fundamentalDomain_NE | (intros; apply GlobalTheory.CellDec.exists_fundamentalDomain_NE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjOfTeichmullerCongrStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_conj_of_teichmuller_congr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∀ v : O, WittVector.map ψ (bk.ev bk.E) ∣ WittVector.teichmuller l v - WittVector.teichmuller l (ψ bk.flat) → ∃ g : ↥(GK K), v = ψ (Per.σF (g : GQ l) bk.flat) := by
  first | exact @GlobalTheory.BSP.exists_gal_of_teichmuller_congr | exact GlobalTheory.BSP.exists_gal_of_teichmuller_congr | (intros; apply GlobalTheory.BSP.exists_gal_of_teichmuller_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixingMaxUnramifiedMapConjStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_fixing_maxUnramified_map_conj : ∀ (l : ℕ) [Fact l.Prime] (x y : Om l), Polynomial.aeval y (minpoly ↥(MaximalUnramifiedExtension l) x) = 0 → ∃ g : GQ l, (∀ z ∈ MaximalUnramifiedExtension l, g z = z) ∧ g x = y := by
  first | exact @GlobalTheory.LiftKur.exists_gal_fix_Kur_map | exact GlobalTheory.LiftKur.exists_gal_fix_Kur_map | (intros; apply GlobalTheory.LiftKur.exists_gal_fix_Kur_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_prescribed_unramified_kummer : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), e + 1 = l ^ a → ∀ (m : ZMod a) (ζ : Om l), ζ ^ e = 1 → ∃ g : GQ l, (∀ x : Om l, x ^ l ^ a = x → g x = x ^ l ^ m.val) ∧ g (ϖ.seq 0) = ζ * ϖ.seq 0 := by
  first | exact @GlobalTheory.TameFrob.exists_cover | exact GlobalTheory.TameFrob.exists_cover | (intros; apply GlobalTheory.TameFrob.exists_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHubData
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX

theorem exists_hubData : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK), SumRepresentations.adm2 D → SumRepresentations.Conclusion41 D → ∀ (e' : FamilyRepresentationConstants.RFam D → FamilyRepresentationConstants.RhoFam D → D.nd.Loc → HeightOneSpectrum (𝓞 D.host.E) → ℕ) (exc : FamilyRepresentationConstants.RhoFam D → Finset ℕ) (I : TwIn D), ∃ X : KillingConditions.HubData D, GlobalTheory.HubX.Canon L HW R X ∧ X.e' = e' X.r X.ρ ∧ X.exc = exc X.ρ ∧ X.I = I ∧ (∀ i, GoodR D.nd i (X.r i)) ∧ (0 ≤ L.etaSz → (X.eta : ℝ) ≤ 2 * L.etaSz) ∧ ∀ i, GlobalTheory.HubLoc.cBnum (D.nd.l i) ⌊2 * L.sc.b⌋₊ D.R.t (4 * D.R.n * D.R.nV) ≤ X.cB i := by
  intro hC D L HW R h2 h41 e' exc I
  obtain ⟨r, ρ, h⟩ := GlobalTheory.PtCore.exists_ptFam hC D (GlobalTheory.T.galois_reps_cuspidal D h2) (fun i => (h41 i).1.2)
  have hc := canon_ourX L HW R r ρ (e' r ρ) (exc ρ) I h
  refine ⟨ourX L HW R r ρ (e' r ρ) (exc ρ) I, hc, rfl, rfl, rfl, hc.fam.good, ?_, ?_⟩
  · intro hL
    rw [hc.eta]
    have := Nat.floor_le hL
    linarith
  · intro i
    rw [hc.cB]
    exact le_refl _

end GlobalTheory.HubX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSpanCornerSeparableStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_span_corner_charpoly_separable : ∀ {K Γ : Type} [Field K] [Infinite K] [Group Γ] {n t : ℕ} (σ : Γ →* Matrix (Fin n) (Fin n) K) (a : Matrix (Fin n) (Fin t) K) (b : Matrix (Fin t) (Fin n) K), AbsIrrDistinct (matRep σ) → b * a = 1 → a * b ∈ Submodule.span K (Set.range σ) → ∃ m ∈ Submodule.span K (Set.range σ), (b * m * a).charpoly.Separable := by
  first | exact @GlobalTheory.SpanRing.exists_mem_span_corner_separable | exact GlobalTheory.SpanRing.exists_mem_span_corner_separable | (intros; apply GlobalTheory.SpanRing.exists_mem_span_corner_separable <;> assumption)
end

