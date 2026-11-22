import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0004
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonTransferBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0480
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0554
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0490
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0539
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisComparisonImageEisensteinPowPhiInvColumns
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

private theorem tensor_inclusion_smul_sum {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    [NormedAlgebra ℚ_[l] K] {G : Type} [Group G] [TopologicalSpace G]
    {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R']
    (f : R →ₐ[O] R') (T : LocLat G ℚ_[l] K O) (s : R) {κ : Type} [Fintype κ] (r : κ → R) (x : κ → ↥T.L.T) :
    TWincl f T (∑ k, (s * r k) ⊗ₜ[O] x k) = f s • TWincl f T (∑ k, r k ⊗ₜ[O] x k) := by
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [TWincl, TensorProduct.smul_tmul']

private theorem ennreal_volume_ratio_step_cancel {R W ι : Type} [CommRing R] [AddCommGroup W] [Fintype ι] (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w)
    (u : R) (hu : IsUnit u) (y z y' z' : ι → R) (v w : ι → W) (hy : ∀ j, y' j = u * y j)
    (hz : ∀ j, z' j = u * z j) (h : ∑ j, act (y' j) (v j) = ∑ k, act (z' k) (w k)) :
    ∑ j, act (y j) (v j) = ∑ k, act (z k) (w k) := by
  obtain ⟨u, rfl⟩ := hu
  have h2 := congrArg (act ((u⁻¹ : Rˣ) : R)) h
  simp only [map_sum, hy, hz, ← hmul, ← mul_assoc, Units.inv_mul, one_mul] at h2
  exact h2

private theorem tame_lattice_inclusion (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O)
    (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι)
    (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (i : ι) (y : ι → OA l O) (s u : OA l O)
    (r : ι → OA l O) (x : ι → ↥T.L.T) (hI : inclL t ϖ P y = Pi.single i (inclO l O s))
    (hj : I.j (inclV l O ι (Pi.single i u)) = TWincl (inclO l O) T (∑ k, r k ⊗ₜ[O] x k)) :
    I.j (inclL t ϖ P (fun j => u * y j)) = TWincl (inclO l O) T (∑ k, (s * r k) ⊗ₜ[O] x k) := by
  have h1 : inclL t ϖ P (fun j => u * y j) = inclO l O s • inclV l O ι (Pi.single i u) := by
    have h2 : inclL t ϖ P (fun j => u * y j) = inclO l O u • inclL t ϖ P y := by
      rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
      congr 1
      funext j
      simp only [map_mul, Pi.smul_apply, smul_eq_mul]
    rw [h2, hI]
    funext j
    change inclO l O u * _ = inclO l O s * inclO l O ((Pi.single i u : ι → OA l O) j)
    by_cases hij : j = i
    · subst hij
      rw [Pi.single_eq_same, Pi.single_eq_same, mul_comm]
    · rw [Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij, map_zero, mul_zero, mul_zero]
  rw [h1, I.j.map_smul, hj]
  exact (tensor_inclusion_smul_sum (inclO l O) T s r x).symm

private theorem cancel_unit_in_sum_action {A R W ι : Type} [CommRing A] [CommRing R] [AddCommGroup W] [Fintype ι]
    (f : A → R) (hf : ∀ x y, f (x * y) = f x * f y) (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w)
    (u s : A) (s' : R) (hs : f s = s') (hu : IsUnit (f u)) (y r : ι → A) (m : ι → R)
    (hr : ∀ k, f (r k) = f u * m k) (v w : ι → W)
    (h : ∑ j, act (f (u * y j)) (v j) = ∑ k, act (f (s * r k)) (w k)) :
    ∑ j, act (f (y j)) (v j) = ∑ k, act (s' * m k) (w k) :=
  ennreal_volume_ratio_step_cancel act hmul hone (f u) hu _ _ _ _ v w (fun j => hf _ _)
    (fun k => by rw [hf, hs, hr, mul_left_comm]) h

theorem _root_.UpperTheory.KN.crisComparison_image_eisensteinPow_phiInvColumns :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (b : Module.Basis ι ↥(OL LL) ↥T.L.T) (m : Matrix ι ι (OD l ↥(OL LL))) (u : OA l ↥(OL LL)) (r : ι → ι → OA l ↥(OL LL)), IsUnit (toOD l ↥(OL LL) u) → (∀ i, I.j (inclV l ↥(OL LL) ι (Pi.single i u)) = TWincl (inclO l ↥(OL LL)) T (∑ k, r i k ⊗ₜ[↥(OL LL)] b k)) → (∀ i k, toOD l ↥(OL LL) (r i k) = toOD l ↥(OL LL) u * m i k) → ∀ (β : ℕ) (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1) (i : ι), ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩))) (X (jB (Pi.single j 1))) = ∑ k, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β * m i k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I jB Pl AI Td hcmp X hX act hact b m u r hu hj hr β hβ i
  have hact' := GlobalTheory.BKGal.JumpDR.odAct_mul_one l LL T Pl AI Td act hact
  have hI := UpperTheory.KN.inclL_eisensteinPow_phiInv_eq_single l a e ϖ LL ι P β hβ i
  have hE := UpperTheory.KN.iTot_eisensteinPow_eq_iD_eisensteinHatPow l a e ϖ LL β
  have h3 := tame_lattice_inclusion l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I i _ _ u (r i) (fun k => b k) hI (hj i)
  have h4 := UpperTheory.KN.crisComparison_transfer_basis_coordinates l a e ϖ LL ι P T I jB Pl AI Td hcmp X hX act hact ι _ _ _ h3
  have h5 := cancel_unit_in_sum_action (toOD l ↥(OL LL)) (map_mul (toOD l ↥(OL LL))) act hact'.1 hact'.2 u _ _ hE hu _ (r i) (m i)
    (hr i) _ _ h4
  exact h5
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisInclIBEqDeRhamInclID
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.crisIncl_iB_eq_deRhamIncl_iD :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (f : ZMod a → invL l (S O K e)),
    iotaO O C (ϖ.iB t K f) = dRO l O (ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (f τ : K⟦X⟧))) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ C f
  have hS : ∀ τ, ϖ.iSD O K (f τ) = ϖ.iHat O K (GlobalTheory.GalStep.hatR O (f τ : K⟦X⟧)) := fun τ => by
    have hm : ((f τ : invL l (S O K e)) : K⟦X⟧) ∈ Rpi O K l e := invL_S_le_Rpi l e (f τ).2
    refine GlobalTheory.BKReal.TwoMaps.iSD_eq_iHat_of_hat l a e O K t ϖ (f τ) _ ?_
    rw [GlobalTheory.GalStep.hatR_of_mem (O := O) hm]
    exact hat_coe_Rpi l e ⟨_, hm⟩
  rw [PiSys.iB, PiSys.iD, glue_apply, glue_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hI : iotaO O C (idem (constB t) τ) = dRO l O (idem (constD t) τ) :=
    iotaO_toB C (constA t (Pi.single τ 1))
  rw [map_mul, hI, iotaO_iSl ϖ C (f τ), hS, map_mul]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsTensorBdRActionOnLatticeBdR
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.exists_tensorBdR_action_on_latticeBdR :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), ∃ B : OdR l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR),
    ∀ (o : ↥(OL LL)) (b : Per.BdR l) (v : T.V) (c : Pl.R.BdR), B (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (Td.eD.symm b * c) := by
  intro l _ LL T Pl AI Td
  have hz : ∀ z : ℤ_[l], Td.eD.symm (algebraMap ℤ_[l] (Per.BdR l) z) = algebraMap ℚ_[l] Pl.R.BdR (z : ℚ_[l]) :=
    fun z => GlobalTheory.BKGal.JumpDR.cD_algebraMap Td z
  let φ : ↥(OL LL) → T.V →ₗ[ℚ_[l]] T.V := fun o =>
    { toFun := fun v => (o : ↥LL.1) • v
      map_add' := fun v w => smul_add _ v w
      map_smul' := fun q v => by
        simp only [RingHom.id_apply]
        rw [← algebraMap_smul (↥LL.1) q v, ← algebraMap_smul (↥LL.1) q ((o : ↥LL.1) • v), smul_smul, smul_smul,
          mul_comm] }
  let F : ↥(OL LL) → Per.BdR l → (T.V ⊗[ℚ_[l]] Pl.R.BdR →ₗ[ℚ_[l]] T.V ⊗[ℚ_[l]] Pl.R.BdR) := fun o b =>
    TensorProduct.map (φ o) (LinearMap.mulLeft ℚ_[l] (Td.eD.symm b))
  have hF : ∀ o b v c, F o b (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (Td.eD.symm b * c) := fun o b v c => rfl
  have hb : ∀ o b b', F o (b + b') = F o b + F o b' := fun o b b' => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, map_add, add_mul, tmul_add]
  have ho : ∀ o o' b, F (o + o') b = F o b + F o' b := fun o o' b => by
    apply TensorProduct.ext'
    intro v c
    rw [LinearMap.add_apply, hF, hF, hF, Subalgebra.coe_add, add_smul, add_tmul]
  let f : ↥(OL LL) →+ Per.BdR l →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR) :=
    AddMonoidHom.mk' (fun o => AddMonoidHom.mk' (fun b => (F o b).toAddMonoidHom)
      (fun b b' => AddMonoidHom.ext fun x => by
        show F o (b + b') x = F o b x + F o b' x
        rw [hb]; rfl))
      (fun o o' => AddMonoidHom.ext fun b => AddMonoidHom.ext fun x => by
        show F (o + o') b x = F o b x + F o' b x
        rw [ho]; rfl)
  have hbal : ∀ (z : ℤ_[l]) (o : ↥(OL LL)) (b : Per.BdR l), f (z • o) b = f o (z • b) := by
    intro z o b
    apply AddMonoidHom.ext
    intro x
    show F (z • o) b x = F o (z • b) x
    congr 1
    apply TensorProduct.ext'
    intro v c
    rw [hF, hF, Algebra.smul_def z b, map_mul, hz, mul_assoc, ← Algebra.smul_def,
      ← TensorProduct.smul_tmul (R := ℚ_[l])]
    congr 1
    show ((z : ℚ_[l]) • (o : ↥LL.1)) • v = (z : ℚ_[l]) • ((o : ↥LL.1) • v)
    rw [smul_assoc]
  refine ⟨TensorProduct.liftAddHom f hbal, fun o b v c => ?_⟩
  rw [TensorProduct.liftAddHom_tmul]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LatticeTensorDeRhamCrysRelationGaloisStable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private noncomputable def gdR {l : ℕ} [Fact l.Prime] (g : GQ l) : Per.BdR l →ₐ[ℤ_[l]] Per.BdR l where
  toRingHom := Per.σD g
  commutes' z := (GlobalTheory.MemLoc.FilLaws.σD_alg g (algebraMap ℤ_[l] (Per.BdRp l) z)).trans
    (congrArg (algebraMap (Per.BdRp l) (Per.BdR l)) ((GlobalTheory.GalStep.galD g).commutes z))

private noncomputable def gOdR {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (g : GQ l) :
    OdR l O →ₐ[O] OdR l O := Algebra.TensorProduct.map (AlgHom.id _ _) (gdR g)

private theorem gOdR_dRO {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] (g : GQ l) (x : OD l O) :
    gOdR O g (dRO l O x) = dRO l O (GlobalTheory.GalStep.galOD O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y) (GlobalTheory.MemLoc.FilLaws.σD_alg g w)
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem gOdR_iotaO {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (C : GlobalTheory.MemLoc.Core l) (g : GQ l) (x : OB l O) :
    gOdR O g (iotaO O C x) = iotaO O C (galOB O g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdR l => o ⊗ₜ[ℤ_[l]] y) (GlobalTheory.BKGal.FilStable.ι_σB C g w).symm
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem act_incl {O G Qp LL R R' : Type} [CommRing O] [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
    [Algebra Qp LL] [Algebra O LL] [TopologicalSpace LL] [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (i : R →ₐ[O] R') (f : R →ₐ[O] R) (f' : R' →ₐ[O] R') (h : ∀ r, f' (i r) = i (f r))
    (T : LocLat G Qp LL O) (g : G) (z : TW R T) :
    TWact f' T g (TWincl i T z) = TWincl i T (TWact f T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    simp only [TWact, TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem _root_.UpperTheory.KN.latticeTensor_deRham_crys_relation_galois_stable :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (g : Gl l) (y : TW (OD l O) T) (b : TW (OB l O) T) (x : OD l O),
    TWincl (dRO l O) T y = dRO l O x • TWincl (iotaO O C) T b →
    TWincl (dRO l O) T (TWact (GlobalTheory.GalStep.galOD O (sQ l g)) T g y) =
      dRO l O (GlobalTheory.GalStep.galOD O (sQ l g) x) • TWincl (iotaO O C) T (TWact (galOB O (sQ l g)) T g b) := by
  intro l _ O K _ _ _ _ _ _ _ T C g y b x h
  have h1 := act_incl (dRO l O) (GlobalTheory.GalStep.galOD O (sQ l g)) (gOdR O (sQ l g)) (gOdR_dRO O (sQ l g)) T g y
  have h2 := act_incl (iotaO O C) (galOB O (sQ l g)) (gOdR O (sQ l g)) (gOdR_iotaO O C (sQ l g)) T g b
  have h3 := GlobalTheory.GalStep.TWact_smul_of (gOdR O (sQ l g)) T g (dRO l O x) (TWincl (iotaO O C) T b)
  have h4 := gOdR_dRO O (sQ l g) x
  refine h1.symm.trans ((congrArg (TWact (gOdR O (sQ l g)) T g) h).trans (h3.trans ?_))
  rw [h4, h2]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LatticeTensorInclDeRhamInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.latticeTensorIncl_deRham_injective :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O), Function.Injective (TWincl (dRO l O) T) := by
  intro l _ O K _ _ _ _ _ _ _ T
  classical
  have h0 : Function.Injective (bdRpToBdR l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1
  have h1 : Function.Injective (dRO l O) := by
    intro r s h
    let b := Module.Free.chooseBasis ℤ_[l] O
    apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
    ext k
    apply h0
    rw [← equivFinsuppOfBasisLeft_map_id, ← equivFinsuppOfBasisLeft_map_id]
    exact congrArg (fun y => TensorProduct.equivFinsuppOfBasisLeft b y k) h
  intro w z h
  haveI := T.L.free
  let bT := Module.Free.chooseBasis O ↥T.L.T
  apply (TensorProduct.equivFinsuppOfBasisRight bT).injective
  refine Finsupp.ext (fun j => ?_)
  apply h1
  rw [← equivFinsuppOfBasisRight_map_id, ← equivFinsuppOfBasisRight_map_id]
  exact congrArg (fun y => TensorProduct.equivFinsuppOfBasisRight bT y j) h
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.PhiModCoefficientsEqSumOfInverseMatrix
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

private theorem hat_mulVec' {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
    {ι : Type} [Fintype ι] {Y : Matrix ι ι K⟦X⟧} (hY : ∀ i j, Y i j ∈ RpiE O K l e) {m : ι → K⟦X⟧}
    (hm : ∀ j, m j ∈ RpiE O K l e) (i : ι) :
    hat O l e ((Y *ᵥ m) i) = ∑ j, hat O l e (Y i j) * hat O l e (m j) := by
  have : (Y *ᵥ m) i = ((∑ j, ⟨Y i j, hY i j⟩ * ⟨m j, hm j⟩ : RpiE O K l e) : K⟦X⟧) := by
    simp [Matrix.mulVec, dotProduct]
  rw [this, hat_coe, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hat_of_mem l e (hY i j), hat_of_mem l e (hm j)]

theorem _root_.UpperTheory.KN.phiMod_coefficients_eq_sum_of_inverse_matrix :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat O K l e),
    (∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) →
    ∀ j, (fun τ => c τ j) = ∑ k, s k * fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P n s m c h j
  funext τ
  apply algebraMap_AhatE_injective l e
  rw [h τ j, Finset.sum_apply, map_sum]
  simp only [GlobalTheory.BKGal.JumpDR.hsum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc (i : ι) : (coordL P (invL l (S O K e)) (m k) i τ : K⟦X⟧) ∈ Rpi O K l e :=
    invL_S_le_Rpi l e (coordL P (invL l (S O K e)) (m k) i τ).2
  have hm (i : ι) : (m k).1 τ i ∈ RpiE O K l e := by
    have := congrFun (mx_mulVec_coordL P (invL l (S O K e)) (m k) τ) i
    rw [← this]
    exact Subalgebra.sum_mem _ fun i' _ =>
      mul_mem (invE_A_le_RpiE l e (P.mx_mem τ i i')) (le_away _ _ (hc i'))
  have h1 : (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧) = (P.mxInv τ *ᵥ (m k).1 τ) j := rfl
  rw [Pi.mul_apply, map_mul, GlobalTheory.GalStep.hatR_of_mem (hc j), ← hat_coe_Rpi]
  change _ = _ * hat O l e (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧)
  rw [h1, hat_mulVec' (fun i i' => invE_A_le_RpiE l e (P.mxInv_mem τ i i')) hm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.PhiModDeRhamImageCoordExpansion
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem _root_.UpperTheory.KN.phiMod_deRham_image_coord_expansion :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (α : ℕ) (hx : ∀ τ i j, E K l e ^ α * P.mx τ i j ∈ A O K) (σ : P.MMl),
    GlobalTheory.GalStep.YD t ϖ (E K l e ^ α • σ.1) = ∑ j, ϖ.iD t K (fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) σ j τ : K⟦X⟧)) •
      fun i => toOD l O (ϖ.iTot t K (fun τ => ⟨E K l e ^ α * P.mx τ i j, hx τ i j⟩)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P α hx σ
  funext i
  simp only [GlobalTheory.GalStep.YD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [← PiSys.iD_ofA, ← map_mul]
  rw [← map_sum]
  congr 1
  funext τ
  have hw' : ∀ k, (coordL P (invL l (S O K e)) σ k τ : K⟦X⟧) ∈ Rpi O K l e := fun k =>
    invL_S_le_Rpi l e (coordL P (invL l (S O K e)) σ k τ).2
  have hb' : ∀ k, E K l e ^ α * P.mx τ i k ∈ Rpi O K l e := fun k => A_le_Rpi l e (hx τ i k)
  have hs : E K l e ^ α * σ.1 τ i =
      ∑ k, (coordL P (invL l (S O K e)) σ k τ : K⟦X⟧) * (E K l e ^ α * P.mx τ i k) := by
    rw [← mx_mulVec_coordL P (invL l (S O K e)) σ τ]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hm : (∑ k, (coordL P (invL l (S O K e)) σ k τ : K⟦X⟧) * (E K l e ^ α * P.mx τ i k)) ∈ Rpi O K l e :=
    Subalgebra.sum_mem _ fun k _ => mul_mem (hw' k) (hb' k)
  have hA : ∀ k, ofA O K l e ⟨E K l e ^ α * P.mx τ i k, hx τ i k⟩ = toHat O K l e ⟨_, hb' k⟩ := fun k =>
    (toHat_eq_ofAl l e rfl).symm
  rw [hs, GlobalTheory.GalStep.hatR_of_mem (O := O) hm, Finset.sum_apply]
  simp only [Pi.mul_apply, GlobalTheory.GalStep.hatR_of_mem (O := O) (hw' _), hA, ← map_mul]
  rw [← map_sum]
  congr 1
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  rfl
end

