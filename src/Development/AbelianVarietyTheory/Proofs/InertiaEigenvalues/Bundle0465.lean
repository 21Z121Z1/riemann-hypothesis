import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0230
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0066
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0402
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBdRPlusLatticeGeneratorsDdR
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BdRLatticeGens

variable {l : ℕ} [Fact l.Prime]

theorem iota_sigma {K : FinExt l} {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) (g : ↥(GK K)) (b : Per.Bcris l) :
    C.ι (Per.σB (g : GQ l) b) = Per.σD (g : GQ l) (C.ι b) := by
  obtain ⟨b0, rfl⟩ := T.eB.surjective b
  have h1 := (P.PD K).ι_comm g b0
  rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h1
  rw [← T.actB, ← hF.ι, ← hF.ι, h1, T.actD]

theorem iota_zB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) (a : ℤ_[l]) : C.ι (Per.zB l a) = Per.zD l a := by
  rw [← T.zB, ← hF.ι, AlgHom.commutes, T.zD]

theorem sigma_U' {d : ℕ} {K : FinExt l} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)) (hUU : U * U' = 1)
    (hU : ∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) (g : ↥(GK K)) :
    U'.map (Per.σB (g : GQ l)) = U' * (ρ g).map (Per.zB l) := by
  have h1 : U.map (Per.σB (g : GQ l)) * U'.map (Per.σB (g : GQ l)) = 1 := by
    rw [← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (ρ g).map (Per.zB l) = U * U'.map (Per.σB (g : GQ l)) := by
    conv_rhs => rw [← hU g]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have h3 : U' * U = 1 := mul_eq_one_comm.1 hUU
  rw [h2, ← Matrix.mul_assoc, h3, Matrix.one_mul]

theorem inv_vec {K : FinExt l} {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) {d : ℕ} (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l]))
    (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)) (hUU : U * U' = 1)
    (hU : ∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U)
    (v : Fin d → Per.BdR l)
    (hv : ∀ g : ↥(GK K), ((ρ g).map (Per.zD l)).mulVec (fun r => Per.σD (g : GQ l) (v r)) = v)
    (g : ↥(GK K)) (r : Fin d) :
    Per.σD (g : GQ l) ((U'.map C.ι).mulVec v r) = (U'.map C.ι).mulVec v r := by
  rw [RingHom.map_mulVec]
  have e1 : (U'.map C.ι).map (Per.σD (g : GQ l)) = U'.map C.ι * (ρ g).map (Per.zD l) := by
    have : (U'.map C.ι).map (Per.σD (g : GQ l)) = (U'.map (Per.σB (g : GQ l))).map C.ι := by
      ext a b; simp [iota_sigma hF g]
    rw [this, sigma_U' ρ U U' hUU hU g, Matrix.map_mul]
    congr 1
    ext a b; simp [iota_zB hF]
  rw [e1, ← Matrix.mulVec_mulVec]
  exact congrFun (congrArg _ (hv g)) r

theorem isUnit_aDp_zA {y : ℤ_[l]} (hy : y ≠ 0) : IsUnit (aDp l (Per.zA l y)) := by
  rw [PadicInt.unitCoeff_spec hy, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
  exact ((PadicInt.unitCoeff hy).isUnit.map _).map _ |>.mul ((isUnit_l_BdRp l).pow _)

theorem oD_int (C : Core l) (y : ℤ_[l]) (x : Om l) :
    C.oD (algebraMap ℚ_[l] (Om l) (y : ℚ_[l]) * x) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) * C.oD x := by
  rw [map_mul]
  congr 1
  simp only [Core.oD, RingHom.comp_apply, C.o_sec.z]

theorem descend {K : FinExt l} (C : Core l) (hI : C.InvdR) {d : ℕ} (w : Fin d → Per.BdR l)
    (hw : ∀ (g : ↥(GK K)) r, Per.σD (g : GQ l) (w r) = w r) :
    ∃ (y : ℤ_[l]) (z : Fin d → ↥(OL K)), y ≠ 0 ∧
      ∀ r, C.oD (K.1.val.toRingHom ((OL K).val.toRingHom (z r))) =
        algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) * w r := by
  have hx : ∀ r, ∃ x ∈ K.1, C.oD x = w r := fun r => hI K (w r) (fun g hg => hw ⟨g, hg⟩ r)
  choose x hxK hxw using hx
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  classical
  obtain ⟨y, hy0, hint⟩ := exists_integral_multiples ℤ_[l] ℚ_[l]
    (Finset.univ.image fun r => (⟨x r, hxK r⟩ : ↥K.1))
  refine ⟨y, fun r => ⟨y • ⟨x r, hxK r⟩, hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ r))⟩, hy0, fun r => ?_⟩
  rw [← hxw r, ← oD_int]
  congr 1
  change ((y • (⟨x r, hxK r⟩ : ↥K.1) : ↥K.1) : Om l) = _
  rw [← algebraMap_smul ℚ_[l] y, Algebra.smul_def]
  simp

theorem exists_lattice_generators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → C.InvdR → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (U U' : Matrix (Fin d) (Fin d) (Per.Bcris l)), U * U' = 1 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U) → (∀ j : Fin d, ∃ (m : ℕ) (k : Fin m → ℤ) (c : Fin m → Per.BdR l) (v : Fin m → Fin d → Per.BdR l), (∀ i (g : ↥(GK K)), ((ρ g).map (Per.zD l)).mulVec (fun r => Per.σD (g : GQ l) (v i r)) = v i) ∧ (∀ i r, v i r ∈ Per.FilD l (k i)) ∧ (∀ i, c i ∈ Per.FilD l (-k i)) ∧ (Pi.single j 1 : Fin d → Per.BdR l) = ∑ i, c i • v i) → ∀ N₀ : ℕ, ∃ (N m : ℕ) (k : Fin m → ℤ) (c : Matrix (Fin d) (Fin m) (↥(OL K))) (β : Matrix (Fin m) (Fin d) (Per.BdR l)), N₀ ≤ N ∧ (∀ i, |k i| ≤ N) ∧ (∀ r s, C.ι (U r s) ∈ Per.FilD l (-(N : ℤ))) ∧ (∀ r i, (U.map C.ι * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i ∈ Per.FilD l (k i)) ∧ (∀ i j, β i j ∈ Per.FilD l (-k i)) ∧ U.map C.ι * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) * β = 1 := by
  intro l _ K P AI T C hF hI d ρ U U' hUU hU hfam N₀
  have hfil := GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (xi C.ε) C.ker_theta.symm
  obtain ⟨-, -, hmono, -, hbd, -, -⟩ := hfil
  choose m k c v hv hvF hcF hsum using hfam
  have hUι : U.map C.ι * U'.map C.ι = 1 := by
    rw [← Matrix.map_mul, hUU, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcol : ∀ (j : Fin d) (a : Fin (m j)), ∃ (y : ℤ_[l]) (z : Fin d → ↥(OL K)), y ≠ 0 ∧
      ∀ r, (U.map C.ι).mulVec (fun s => C.oD (K.1.val.toRingHom ((OL K).val.toRingHom (z s)))) r =
        algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y)) * v j a r := by
    intro j a
    obtain ⟨y, z, hy0, hz⟩ := descend (K := K) C hI ((U'.map C.ι).mulVec (v j a))
      (inv_vec hF ρ U U' hUU hU (v j a) (hv j a))
    refine ⟨y, z, hy0, fun r => ?_⟩
    have : (fun s => C.oD (K.1.val.toRingHom ((OL K).val.toRingHom (z s)))) =
        (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l y))) • (U'.map C.ι).mulVec (v j a) := by
      ext s; rw [hz s]; rfl
    rw [this, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hUι, Matrix.one_mulVec]
    rfl
  choose y z hy0 hz using hcol
  choose n hn using hbd

  classical
  let e : Fin (∑ j, m j) ≃ (Σ j : Fin d, Fin (m j)) := finSigmaFinEquiv.symm
  let inv : (p : Σ j : Fin d, Fin (m j)) → Per.BdRp l := fun p => ((isUnit_aDp_zA (hy0 p.1 p.2)).unit⁻¹ : (Per.BdRp l)ˣ)
  let kk : Fin (∑ j, m j) → ℤ := fun i => k (e i).1 (e i).2
  let cc : Matrix (Fin d) (Fin (∑ j, m j)) ↥(OL K) := fun r i => z (e i).1 (e i).2 r
  let β : Matrix (Fin (∑ j, m j)) (Fin d) (Per.BdR l) := fun i j' =>
    if (e i).1 = j' then algebraMap (Per.BdRp l) (Per.BdR l) (inv (e i)) * c (e i).1 (e i).2 else 0
  let N : ℕ := max N₀ (max (Finset.univ.sup fun i => (kk i).natAbs) (Finset.univ.sup fun q : Fin d × Fin d => n (C.ι (U q.1 q.2))))
  have hA : ∀ r i, (U.map C.ι * cc.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y (e i).1 (e i).2))) * v (e i).1 (e i).2 r := by
    intro r i
    rw [← hz]
    rfl
  refine ⟨N, ∑ j, m j, kk, cc, β, le_max_left _ _, fun i => ?_, fun r s => ?_, fun r i => ?_, fun i j' => ?_, ?_⟩
  · have h1 : (kk i).natAbs ≤ N :=
      le_trans (Finset.le_sup (f := fun i => (kk i).natAbs) (Finset.mem_univ i))
        (le_trans (le_max_left _ _) (le_max_right _ _))
    rw [Int.abs_eq_natAbs]; exact_mod_cast h1
  · have h1 : n (C.ι (U r s)) ≤ N :=
      le_trans (Finset.le_sup (f := fun q : Fin d × Fin d => n (C.ι (U q.1 q.2))) (Finset.mem_univ (r, s)))
        (le_trans (le_max_right _ _) (le_max_right _ _))
    exact hmono _ _ (by simpa using h1) (hn _)
  · rw [hA, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (hvF _ _ _)
  · simp only [β]
    split_ifs
    · rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ (hcF _ _)
    · exact Submodule.zero_mem _
  · ext r j'
    rw [Matrix.mul_apply]
    simp_rw [hA]
    let G : (Σ j : Fin d, Fin (m j)) → Per.BdR l := fun p =>
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y p.1 p.2))) * v p.1 p.2 r *
        (if p.1 = j' then algebraMap (Per.BdRp l) (Per.BdR l) (inv p) * c p.1 p.2 else 0)
    have e1 : ∀ i, algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y (e i).1 (e i).2))) * v (e i).1 (e i).2 r * β i j' = G (e i) := fun i => rfl
    simp_rw [e1]
    rw [Equiv.sum_comp e G, Fintype.sum_sigma, Finset.sum_eq_single j']
    · have hs : ∀ a : Fin (m j'), G ⟨j', a⟩ = c j' a * v j' a r := by
        intro a
        show algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y j' a))) * v j' a r *
          (if j' = j' then algebraMap (Per.BdRp l) (Per.BdR l) (inv ⟨j', a⟩) * c j' a else 0) = _
        rw [if_pos rfl]
        have hu : algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y j' a))) *
            algebraMap (Per.BdRp l) (Per.BdR l) (inv ⟨j', a⟩) = 1 := by
          rw [← map_mul, show aDp l (Per.zA l (y j' a)) * inv ⟨j', a⟩ = 1 from
            (isUnit_aDp_zA (hy0 j' a)).mul_val_inv, map_one]
        calc _ = (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l (y j' a))) *
            algebraMap (Per.BdRp l) (Per.BdR l) (inv ⟨j', a⟩)) * (c j' a * v j' a r) := by ring
          _ = _ := by rw [hu, one_mul]
      simp_rw [hs]
      have h2 := congrFun (hsum j') r
      rw [Finset.sum_apply] at h2
      simp only [Pi.smul_apply, smul_eq_mul] at h2
      rw [← h2, Pi.single_apply, Matrix.one_apply]
    · intro j _ hj
      exact Finset.sum_eq_zero fun a _ => by simp [G, hj]
    · intro h; exact absurd (Finset.mem_univ j') h

end GlobalTheory.BdRLatticeGens
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoordAcrisBcris
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CoordTW

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K]
  [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G]
  (T : LocLat G ℚ_[l] K O) (φ : ↥T.L.T →+ ℤ_[l])
  (hφ : ∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t)
  (R : Type) [CommRing R] [Algebra ℤ_[l] R]

def inner (t : ↥T.L.T) : O ⊗[ℤ_[l]] R →+ R :=
  TensorProduct.liftAddHom
    { toFun := fun o => AddMonoidHom.mulLeft (algebraMap ℤ_[l] R (φ (o • t)))
      map_zero' := by ext r; simp
      map_add' := by intro a b; ext r; simp [add_smul, add_mul] }
    (fun z o r => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.coe_mulLeft]
      rw [Algebra.smul_def z o, mul_smul, hφ, Algebra.smul_def z r, map_mul]; ring)

theorem inner_tmul (t : ↥T.L.T) (o : O) (r : R) :
    inner T φ hφ R t (o ⊗ₜ[ℤ_[l]] r) = algebraMap ℤ_[l] R (φ (o • t)) * r := by
  simp [inner]

theorem inner_add (t t' : ↥T.L.T) (w : O ⊗[ℤ_[l]] R) :
    inner T φ hφ R (t + t') w = inner T φ hφ R t w + inner T φ hφ R t' w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o r => simp only [inner_tmul, smul_add, map_add, add_mul]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

theorem inner_zero (w : O ⊗[ℤ_[l]] R) : inner T φ hφ R 0 w = 0 := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o r => simp [inner_tmul]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem inner_smul (o : O) (t : ↥T.L.T) (w : O ⊗[ℤ_[l]] R) :
    inner T φ hφ R t (o • w) = inner T φ hφ R (o • t) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul o' r =>
    rw [TensorProduct.smul_tmul', inner_tmul, inner_tmul, smul_eq_mul, mul_smul, smul_comm o o' t]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

def coord : TW (O ⊗[ℤ_[l]] R) T →+ R :=
  TensorProduct.liftAddHom
    { toFun := fun w =>
        { toFun := fun t => inner T φ hφ R t w
          map_zero' := inner_zero T φ hφ R w
          map_add' := fun t t' => inner_add T φ hφ R t t' w }
      map_zero' := by ext t; simp
      map_add' := by intro a b; ext t; simp }
    (fun o w t => by simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]; exact inner_smul T φ hφ R o t w)

theorem coord_tmul (w : O ⊗[ℤ_[l]] R) (t : ↥T.L.T) :
    coord T φ hφ R (w ⊗ₜ[O] t) = inner T φ hφ R t w := by
  simp [coord]

theorem coord_mul (a : R) (w : TW (O ⊗[ℤ_[l]] R) T) :
    coord T φ hφ R (((1 : O) ⊗ₜ[ℤ_[l]] a : O ⊗[ℤ_[l]] R) • w) = a * coord T φ hφ R w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    rw [TensorProduct.smul_tmul', coord_tmul, coord_tmul, smul_eq_mul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inner_tmul, inner_tmul]; ring
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy, mul_add]

theorem coord_one_tmul (t : ↥T.L.T) :
    coord T φ hφ R ((1 : O ⊗[ℤ_[l]] R) ⊗ₜ[O] t) = algebraMap ℤ_[l] R (φ t) := by
  rw [coord_tmul, Algebra.TensorProduct.one_def, inner_tmul, one_smul, mul_one]

theorem coord_algebraMap_smul (z : ℤ_[l]) (w : TW (O ⊗[ℤ_[l]] R) T) :
    coord T φ hφ R ((algebraMap ℤ_[l] O z) • w) = algebraMap ℤ_[l] R z * coord T φ hφ R w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    rw [TensorProduct.smul_tmul', coord_tmul, coord_tmul, inner_smul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      rw [inner_tmul, inner_tmul, smul_comm o (algebraMap ℤ_[l] O z) t, hφ, map_mul]; ring
    | add x y hx hy => simp only [mul_add, map_add, hx, hy]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy, mul_add]

theorem coord_toOB (w : TW (OCr l O) T) :
    coord T φ hφ (Per.Bcris l) (TWincl (toOB l O) T w) = acrisToBcris l (coord T φ hφ (Per.Acris l) w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x t =>
    simp only [TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_coe, id_eq,
      coord_tmul]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul o r =>
      simp only [toOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, inner_tmul, map_mul,
        AlgHom.commutes]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.CoordTW

namespace GlobalTheory

open GlobalTheory.CoordTW in

theorem exists_coord_acris_bcris : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (φ : ↥T.L.T →+ ℤ_[l]), (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → ∃ (ΦA : TW (OCr l O) T →+ Per.Acris l) (ΦB : TW (OB l O) T →+ Per.Bcris l), (∀ (a : Per.Acris l) (w : TW (OCr l O) T), ΦA (((1 : O) ⊗ₜ[ℤ_[l]] a : OCr l O) • w) = a * ΦA w) ∧ (∀ (y : Per.Bcris l) (w : TW (OB l O) T), ΦB (((1 : O) ⊗ₜ[ℤ_[l]] y : OB l O) • w) = y * ΦB w) ∧ (∀ x : ↥T.L.T, ΦB ((1 : OB l O) ⊗ₜ[O] x) = algebraMap ℤ_[l] (Per.Bcris l) (φ x)) ∧ (∀ (N : ℕ) (w : TW (OCr l O) T), ΦA (((l : O) ^ N) • w) = (l : Per.Acris l) ^ N * ΦA w) ∧ (∀ w : TW (OCr l O) T, ΦB (TWincl (toOB l O) T w) = acrisToBcris l (ΦA w)) := by
  intro l _ O K _ _ _ _ _ _ G _ _ T φ hφ
  refine ⟨coord T φ hφ (Per.Acris l), coord T φ hφ (Per.Bcris l), coord_mul T φ hφ _,
    coord_mul T φ hφ _, coord_one_tmul T φ hφ _, fun N w => ?_, coord_toOB T φ hφ⟩
  have h : ((l : O) ^ N) = algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ N) := by simp
  rw [h, coord_algebraMap_smul]
  simp

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystalCoordinatesOverBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysExt

theorem exists_ext {A B M N R T ι : Type} [CommRing A] [CommRing B] [CommRing R] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (J : T → B →+* R)
    (v : M →+ (T → ι → R)) (hv : ∀ (w : A) (x : M) τ i, v (w • x) τ i = J τ (f w) * v x τ i) :
    ∃ lam : N →+ (T → ι → R), (∀ (r : B) (y : N) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧
      ∀ x, lam (u x) = v x := by
  letI : Module B (T → ι → R) := Module.compHom (T → ι → R)
    (RingHom.pi fun τ => RingHom.pi fun _ : ι => J τ : B →+* (T → ι → R))
  let v' : M →ₛₗ[f] (T → ι → R) :=
    { toFun := v
      map_add' := v.map_add
      map_smul' := fun w x => funext fun τ => funext fun i => hv w x τ i }
  obtain ⟨lam, hlam, -⟩ := h (T → ι → R) v'
  exact ⟨lam.toAddMonoidHom, fun r y τ i => congrFun (congrFun (lam.map_smul r y) τ) i, hlam⟩

theorem frob_toAc {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O)
    (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem exists_coord : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → ∃ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) ∧ ∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ EE c hc PP p J g hJ
  let v : EE.M (ϖ.prism a) →+ (ZMod a → ι → K⟦X⟧⟦X⟧) :=
    { toFun := fun x τ i => g (frob K l (c x (τ - 1) i))
      map_zero' := by ext1 τ; ext1 i; simp
      map_add' := fun x y => by ext1 τ; ext1 i; simp }
  obtain ⟨lam, h1, h2⟩ := exists_ext (EE.tr_bc p) J v (fun w x τ i => by
    change g (frob K l (c (w • x) (τ - 1) i)) = J τ (p.f w) * g (frob K l (c x (τ - 1) i))
    have e1 : c (w • x) (τ - 1) i = (toAc t K w (τ - 1) : K⟦X⟧) * c x (τ - 1) i :=
      congrFun (congrFun (hc w x) (τ - 1)) i
    have e2 := hJ τ w
    have e3 := frob_toAc (K := K) t w τ
    rw [e1, map_mul, map_mul]
    exact congrArg (· * _) ((congrArg g e3).trans e2.symm))
  exact ⟨lam, h1, fun x τ i => congrFun (congrFun (h2 x) τ) i⟩

end GlobalTheory.CrysExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescent
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CrysWD

theorem exists_descent {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] {a : ℕ}
    (r : G →* Matrix.GeneralLinearGroup (Fin a) (Om l))
    (hr : Continuous (fun g => ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) :
      Matrix (Fin a) (Fin a) (Om l))))
    (L : FinExt l)
    (hL : ∀ g i j, ((r g : Matrix.GeneralLinearGroup (Fin a) (Om l)) :
      Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) :
    ∃ ρ : G →* Matrix.GeneralLinearGroup (Fin a) ↥L.1,
      Continuous (fun g => ((ρ g : Matrix.GeneralLinearGroup (Fin a) ↥L.1) :
        Matrix (Fin a) (Fin a) ↥L.1)) ∧
      mapRep (algebraMap ↥L.1 (Om l)) ρ = r := by
  let M : G →* Matrix (Fin a) (Fin a) ↥L.1 :=
    { toFun := fun g => Matrix.of fun i j => ⟨_, hL g i j⟩
      map_one' := by
        ext i j
        simp only [Matrix.of_apply, map_one, Units.val_one, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g h => by
        ext i j
        simp [Matrix.mul_apply] }
  refine ⟨M.toHomUnits, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact Continuous.subtype_mk ((continuous_apply j).comp ((continuous_apply i).comp hr)) _
  · ext g i j
    rfl

theorem crysIffWD (D : D7) : CrysIffWD D.nd D.naut := by
  intro i a r w hw hr
  refine ⟨fun hc => ?_, fun h => (D.naut.wdOf_unrL i r w hw hr h.1).1 h.2⟩
  suffices hd : D.naut.IsdRW i r w from ⟨hd, (D.naut.wdOf_unrL i r w hw hr hd).2 hc⟩
  have := D.nd.lPrime i
  obtain ⟨L, hle, hL⟩ := GlobalTheory.T.compactGroup_rep_defined_over_finite_extension (D.nd.l i) _ a r hr (D.nbr i w hw).LL
  obtain ⟨ρ, hρ, rfl⟩ := exists_descent r hr L hL
  obtain ⟨h1, h2, -⟩ := (D.loc_tie i w hw).2.2 L hle a ρ hρ
  have := L.2
  have h3 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ L _ _ (h1.1 hc)).1
  refine h2.2 ?_
  unfold IsDR at h3
  unfold LocBridge.IsdRE
  simpa using h3

end GlobalTheory.CrysWD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFixFlatOfTiltMapsAgree
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_galK_fixFlat_of_tilt_maps_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type)
    [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O),
    ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O →
    ∀ ψ' : OCb l →+* O, (∀ s : bk.S, ψ ((bk.ev s).coeff 0) = ψ' ((bk.ev s).coeff 0)) →
    ∃ g : ↥(GK K), bk.FixFlat g ∧ ∀ y, ψ' y = ψ (Per.σF (g : GQ l) y) := by
  intro l _ K bk O _ _ _ _ _ ψ h0 hu hc ψ' hs
  have hflat : ψ' bk.flat = ψ bk.flat := by
    have h := hs X
    rw [bk.ev_X, WittVector.teichmuller_coeff_zero] at h
    exact h.symm
  have hW := GlobalTheory.T.wittVector_map_breuilKisin_ev_eq l K bk O ψ ψ' h0 hc hs
  obtain ⟨θ₁, hθ₁, hinj₁, hdom, hdiv⟩ := GlobalTheory.T.exists_injective_map_integers_Cl_to_wittQuotient l K bk O ψ h0 hu hc
  obtain ⟨θ₂', hθ₂', hinj₂', -, -⟩ :=
    GlobalTheory.T.exists_injective_map_integers_Cl_to_wittQuotient l K bk O ψ' (hflat ▸ h0) (hflat ▸ hu) (hflat ▸ hc)
  have hI : Ideal.span {WittVector.map ψ' (bk.ev bk.E)} = Ideal.span {WittVector.map ψ (bk.ev bk.E)} := by
    rw [hW bk.E]
  let θ₂ := (Ideal.quotEquivOfEq hI).toRingHom.comp θ₂'
  have hθ₂ : ∀ a : Ainf l, θ₂ (Per.θ l a) = Ideal.Quotient.mk _ (WittVector.map ψ' a) := by
    intro a
    simp only [θ₂, RingHom.comp_apply, hθ₂' a, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      Ideal.quotEquivOfEq_mk]
  have hinj₂ : Function.Injective θ₂ := (Ideal.quotEquivOfEq hI).injective.comp hinj₂'
  haveI := hdom
  have hK : ∀ r : ↥(OL K), θ₁ (intToOC K r) = θ₂ (intToOC K r) := by
    intro r
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (bk.str r)
    rw [← bk.θ_ev r x hx, hθ₁, hθ₂, hW x]
  obtain ⟨g, halg, hl⟩ := GlobalTheory.T.exists_galois_eq_embeddings_OC_mod_prime l K _ θ₁ θ₂ hinj₁ hinj₂ hK
  obtain ⟨hroot, hfix⟩ := GlobalTheory.T.untiltOfTiltRoot_flat_algebraic_and_galois_fix l K bk

  have key : ∀ z : OCb l, ψ z = ψ' z →
      ψ ((frobeniusEquiv (OCb l) l).symm z) = ψ' ((frobeniusEquiv (OCb l) l).symm z) := by
    intro z hz
    apply frobenius_inj O l
    rw [← RingHom.map_frobenius, ← RingHom.map_frobenius, frobenius_apply_frobeniusEquiv_symm, hz]
  have hiter : ∀ n : ℕ, ψ (((frobeniusEquiv (OCb l) l).symm)^[n] bk.flat) =
      ψ' (((frobeniusEquiv (OCb l) l).symm)^[n] bk.flat) := by
    intro n
    induction n with
    | zero => exact hflat.symm
    | succ n ih => rw [Function.iterate_succ_apply']; exact key _ ih
  have hθroot : ∀ n : ℕ, θ₁ (GlobalTheory.MemLoc.rootT bk.flat n) = θ₂ (GlobalTheory.MemLoc.rootT bk.flat n) := by
    intro n
    have e : GlobalTheory.MemLoc.rootT bk.flat n =
        Per.θ l (WittVector.teichmuller l (((frobeniusEquiv (OCb l) l).symm)^[n] bk.flat)) := by
      rw [GlobalTheory.MemLoc.rootT, WittVector.fontaineTheta_teichmuller]
    rw [e, hθ₁, hθ₂, WittVector.map_teichmuller, WittVector.map_teichmuller, hiter n]
  refine ⟨g, ?_, ?_⟩
  · refine hfix (g : GQ l) bk.flat fun n => ?_
    obtain ⟨z, hz⟩ := hroot n
    have h := halg _ ⟨z, hz⟩
    rw [← hθroot n] at h
    exact (hinj₁ h).symm
  · have hext := GlobalTheory.T.ringHom_eq_of_perfect_of_dvd_sub_adicSeparated l (OCb l) O (ψ bk.flat) bk.Ep.natDegree bk.deg_pos hc.toIsHausdorff
      ψ' (ψ.comp (Per.σF (g : GQ l))) fun y => ?_
    · intro y
      exact RingHom.congr_fun hext y
    · have hmk := hl (Per.θ l (WittVector.teichmuller l y))
      rw [← GlobalTheory.RingBasics.θ_σA, hθ₁, hθ₂] at hmk
      have e2 : Per.σA (g : GQ l) (WittVector.teichmuller l y) =
          WittVector.teichmuller l (Per.σF (g : GQ l) y) := by
        exact GlobalTheory.RingIface.sigA_teich l (g : GQ l) y
      rw [e2, WittVector.map_teichmuller, WittVector.map_teichmuller, ← map_sub] at hmk
      have h := hdiv _ hmk
      rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
        WittVector.teichmuller_coeff_zero] at h
      simpa [RingHom.comp_apply] using h

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisDeRhamLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodge_basis_deRham_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), Formalism.MainNotions.N.IsDR (P.PD K) (qRep ρ) → ∃ H : Hodge C ξ (fun g => (ρ g).val.map (zOm l)) K, ∀ N : ℕ, (DdR (P.PD K) (qRep ρ) ≤ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) (-(N : ℤ)) ∧ DdR (P.PD K) (qRep ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := Fin d → ℚ_[l]) ((N : ℤ) + 1) = ⊥) → ∀ i, |(H.p i : ℤ) - H.q| ≤ N := by
  first | (exact @GlobalTheory.HodgeEx.exists_hodge) | (exact GlobalTheory.HodgeEx.exists_hodge) | (intros; apply GlobalTheory.HodgeEx.exists_hodge  <;> assumption)
end

