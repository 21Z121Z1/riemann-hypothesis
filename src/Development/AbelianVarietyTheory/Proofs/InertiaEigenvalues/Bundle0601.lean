import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0561
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0588
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0422
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0438
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0432
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0589
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0419
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0591

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvariantBasisDeRhamBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.InvBasis

variable {l : ℕ} [Fact l.Prime]

theorem pD_alg_pt : ∀ (l : ℕ) [Fact l.Prime] (a : Formalism.Per.AinfP l), Formalism.Per.pD l a = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) a) :=
  GlobalTheory.RingIface.pD_eq_alg

theorem zD_alg_pt : ∀ (l : ℕ) [Fact l.Prime] (z : ℤ_[l]), Formalism.Per.zD l z = algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) (algebraMap (Formalism.Per.AinfP l) (Formalism.Per.BdRp l) (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) (Formalism.Per.zA l z))) :=
  GlobalTheory.RingIface.zD_eq_alg

theorem isUnit_gen_pt (l : ℕ) [Fact l.Prime] {a : Per.AinfP l} (h : Per.kerP l = Ideal.span {a}) : IsUnit (Per.pD l a) := GlobalTheory.RingIface.isUnit_of_generator l h

theorem padicInt_hom_ext_pt (f g : ℤ_[l] →+* Per.Ainf l) : f = g := by
  ext1 z
  haveI : IsHausdorff (Ideal.span {((l : ℕ) : Per.Ainf l)}) (Per.Ainf l) := inferInstance
  rw [← sub_eq_zero]
  refine IsHausdorff.haus this _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h := PadicInt.appr_spec n z
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hz : z = (z.appr n : ℤ_[l]) + (l : ℤ_[l]) ^ n * c := by rw [← hc]; ring
  refine ⟨f c - g c, ?_⟩
  conv_lhs => rw [hz]
  simp only [map_add, map_mul, map_pow, map_natCast]
  ring

theorem zD_eq_pt (z : ℤ_[l]) :
    algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (algebraMap ℤ_[l] (Ainf l) z)) = Per.zD l z := by
  have h : algebraMap ℤ_[l] (Ainf l) = Per.zA l := padicInt_hom_ext_pt _ _
  rw [h, zD_alg_pt l z, aDp, RingHom.comp_apply]

theorem matrix_map_smul {R S : Type} [CommRing R] [CommRing S] {d : ℕ} (f : R →+* S) (r : R) (M : Matrix (Fin d) (Fin d) R) :
    (r • M).map f = f r • M.map f := by
  ext i j; simp

theorem frob_basis_eq {K : FinExt l} {bk : BK K} {τ : Ainf l} (hτ : bk.IsPer τ) {N d : ℕ}
    {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]} (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l))
    (hY : Y.map (inclW l) = inclW l τ ^ N • F.T) :
    Y.map WittVector.frobenius = Y * F.A.map bk.ev := by
  have hYij : ∀ i j, inclW l (Y i j) = inclW l τ ^ N * F.T i j := fun i j => by
    simpa using congrFun (congrFun hY i) j
  have hφij : ∀ i j, bk.evW bk.E ^ N * frobW l (F.T i j) = ∑ k, F.T i k * inclW l (bk.ev (F.A k j)) := fun i j => by
    simpa [Matrix.mul_apply, BK.evW] using congrFun (congrFun F.φ i) j
  refine Matrix.ext fun i j => ?_
  apply GlobalTheory.Prism.inclW_injective
  rw [Matrix.map_apply, ← frobW_inclW, hYij, map_mul, map_pow, frobW_inclW, hτ.1, Matrix.mul_apply, map_sum]
  simp_rw [map_mul, hYij]
  calc (inclW l (bk.ev bk.E) * inclW l τ) ^ N * frobW l (F.T i j)
      = inclW l τ ^ N * (bk.evW bk.E ^ N * frobW l (F.T i j)) := by simp only [BK.evW, RingHom.comp_apply]; ring
    _ = _ := by rw [hφij, Finset.mul_sum]; simp only [mul_assoc, Matrix.map_apply]

theorem isUnit_Etau {K : FinExt l} {bk : BK K} {τ : Ainf l} (hτ : bk.IsPer τ) :
    IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev bk.E * τ))) := by
  rw [map_mul, map_mul]
  refine IsUnit.mul ?_ ?_
  · have hk : Per.kerP l = Ideal.span {algebraMap (Per.Ainf l) (Per.AinfP l) (bk.ev bk.E)} := by
      rw [GlobalTheory.Per.kerQ_eq_map_ker_theta, ← bk.span_ev, Ideal.map_span, Set.image_singleton]
    have hu := isUnit_gen_pt l hk
    rw [pD_alg_pt] at hu
    rw [aDp, RingHom.comp_apply]
    exact hu
  · have h := GlobalTheory.T.theta_ainf_period_pow_ne_zero l K bk τ hτ 1
    rw [pow_one] at h
    exact ((GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ h).map _

theorem exists_invariant_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), F.IsDR → Y.map (inclW l) = inclW l τ ^ N • F.T → ∃ (B : Matrix (Fin d) (Fin d) (Per.BdRp l)) (Q : Matrix (Fin d) (Fin d) (Per.BdR l)), IsUnit B ∧ IsUnit Q ∧ (∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m) ∧ (algebraMap (Per.BdRp l) (Per.BdR l)) (aDp l (bk.ev bk.E * τ)) ^ N • Q = ((Y * F.A.map bk.ev).map (aDp l) * B).map (algebraMap (Per.BdRp l) (Per.BdR l)) ∧ ∀ g : ↥(GK K), (ρ g).map (Per.zD l) * Q.map (Per.σD (g : GQ l)) = Q := by
  intro l _ K bk τ hτ C N d ρ F Y hDR hY
  obtain ⟨B, hB⟩ := GlobalTheory.T.exists_beta_limit_bdRPlus_deRhamFrame l K bk N d ρ F hDR
  obtain ⟨k1, β1, hβ1, hB1⟩ := hB 1
  have hBu : IsUnit B := GlobalTheory.T.isUnit_bdRPlus_matrix_of_congr_one l K bk d k1 β1 B hβ1.1 hB1
  have hinv := GlobalTheory.T.breuilKisinLatticeFrame_limit_galois_invariant l K bk N d ρ F B hB
  have hφY := frob_basis_eq hτ F Y hY
  have hgal := GlobalTheory.T.frobenius_galois_relation_frame_ainf l K bk τ hτ N d ρ F Y hY
  obtain ⟨v, hv⟩ := isUnit_Etau hτ
  set ι : Per.BdRp l →+* Per.BdR l := algebraMap (Per.BdRp l) (Per.BdR l) with hι
  set j : Ainf l →+* Per.BdR l := ι.comp (aDp l) with hj
  set P : Matrix (Fin d) (Fin d) (Ainf l) := Y.map WittVector.frobenius with hP
  have hjv : j (bk.ev bk.E * τ) = v := hv.symm
  have hM : ((Y * F.A.map bk.ev).map (aDp l) * B).map ι = P.map j * B.map ι := by
    rw [Matrix.map_mul, ← hφY, Matrix.map_map]; rfl
  refine ⟨B, ((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ N • (((Y * F.A.map bk.ev).map (aDp l) * B).map ι), hBu, ?_,
    fun m => ?_, ?_, ?_⟩
  · obtain ⟨Y₀, Y₀', hY₀, hYY⟩ := GlobalTheory.T.breuilKisinPreframe_bounded_poles l K bk τ hτ N d ρ F.toPre
    have hY0 : Y₀ = Y := Matrix.ext fun i k => GlobalTheory.Prism.inclW_injective (by
      have := congrFun (congrFun (hY₀.trans hY.symm) i) k
      simpa using this)
    rw [hY0] at hYY
    have hPP : P * Y₀'.map WittVector.frobenius = (bk.ev bk.E * τ) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
      rw [hP, ← Matrix.map_mul, hYY, matrix_map_smul, Matrix.map_one _ (map_zero _) (map_one _), map_pow, hτ.1]
    have hPj : P.map j * (Y₀'.map WittVector.frobenius).map j = ((v : Per.BdR l) ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (Per.BdR l)) := by
      rw [← Matrix.map_mul, hPP, matrix_map_smul, Matrix.map_one _ (map_zero _) (map_one _), map_pow, hjv]
    have hPu : IsUnit (P.map j) := by
      rw [Matrix.isUnit_iff_isUnit_det]
      refine Matrix.isUnit_det_of_right_inverse (B := (((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ (2 * N)) • (Y₀'.map WittVector.frobenius).map j) ?_
      rw [Matrix.mul_smul, hPj, smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]
    have hMu : IsUnit (P.map j * B.map ι) := hPu.mul (hBu.map (ι.mapMatrix (m := Fin d)))
    rw [hM, Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
    exact (((v⁻¹).isUnit.pow N).pow _).mul ((Matrix.isUnit_iff_isUnit_det _).1 hMu)
  · obtain ⟨k, β, -, h⟩ := hB m
    exact ⟨k, β, h⟩
  · rw [← hv, smul_smul, ← mul_pow, Units.mul_inv, one_pow, one_smul]
  · intro g
    have hσj : ∀ a : Ainf l, Per.σD (g : GQ l) (j a) = j (Per.σA (g : GQ l) a) := fun a => by
      simp only [hj, RingHom.comp_apply, hι, GlobalTheory.MemLoc.ActLaws.σD_alg, GlobalTheory.MemLoc.ActLaws.σDp_aDp]
    have hσι : ∀ b : Per.BdRp l, Per.σD (g : GQ l) (ι b) = ι (Per.σDp (g : GQ l) b) := fun b =>
      GlobalTheory.MemLoc.ActLaws.σD_alg _ b
    set c : Per.BdR l := ((v⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ N with hc
    set R : Matrix (Fin d) (Fin d) (Per.BdR l) := (ρ g).map (Per.zD l) with hR
    set S : Matrix (Fin d) (Fin d) (Per.BdR l) := (P.map (Per.σA (g : GQ l))).map j with hS
    set T' : Matrix (Fin d) (Fin d) (Per.BdR l) := (B.map (Per.σDp (g : GQ l))).map ι with hT'
    set Ej : Matrix (Fin d) (Fin d) (Per.BdR l) := ((F.ε g).map ((aDp l).comp WittVector.frobenius)).map ι with hEj
    have f1 : (v : Per.BdR l) ^ N • (R * S) = Per.σD (g : GQ l) (v : Per.BdR l) ^ N • (P.map j * Ej) := by
      have h1 := congrArg (fun M => M.map j) (hgal g)
      simp only [matrix_map_smul, Matrix.map_mul, map_pow] at h1
      rw [hjv, ← hσj, hjv] at h1
      have eR : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map j = R := Matrix.ext fun a b => zD_eq_pt (ρ g a b)
      have eE : ((F.ε g).map WittVector.frobenius).map j = Ej := Matrix.ext fun _ _ => rfl
      rw [eR, eE] at h1
      exact h1
    have f2 : Ej * T' = B.map ι := by
      have h2 := congrArg (fun M => M.map ι) (hinv g)
      simpa only [Matrix.map_mul] using h2
    have f3 : (c • (P.map j * B.map ι)).map (Per.σD (g : GQ l)) = Per.σD (g : GQ l) c • (S * T') := by
      rw [matrix_map_smul, Matrix.map_mul]
      congr 2
      · exact Matrix.ext fun a b => by simp only [Matrix.map_apply, hS, hσj]
      · exact Matrix.ext fun a b => by simp only [Matrix.map_apply, hT', hσι]
    have hw : Per.σD (g : GQ l) c * Per.σD (g : GQ l) (v : Per.BdR l) ^ N = 1 := by
      rw [hc, map_pow, ← mul_pow, ← map_mul, Units.inv_mul, map_one, one_pow]
    have key : (v : Per.BdR l) ^ N • (R * (Per.σD (g : GQ l) c • (S * T'))) = P.map j * B.map ι := by
      rw [Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul, f1,
        Matrix.smul_mul, smul_smul, Matrix.mul_assoc, f2, hw, one_smul]
    rw [hM, f3]
    calc R * (Per.σD (g : GQ l) c • (S * T')) = (c * (v : Per.BdR l) ^ N) • (R * (Per.σD (g : GQ l) c • (S * T'))) := by
          rw [hc, ← mul_pow, Units.inv_mul, one_pow, one_smul]
      _ = c • (P.map j * B.map ι) := by rw [mul_smul, key]

end GlobalTheory.BKLim.InvBasis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsModificationOfFiltration
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKModif

theorem mulFil {l : ℕ} [Fact l.Prime]
    (hmul : ∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b))
    (hanti : ∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a)
    {p q n : Type} [Fintype q] (M : Matrix p q (Per.BdR l)) (Q : Matrix q n (Per.BdR l))
    (a : p → q → ℤ) (b : q → n → ℤ) (c : p → n → ℤ)
    (hM : ∀ r t, M r t ∈ Per.FilD l (a r t)) (hQ : ∀ t j, Q t j ∈ Per.FilD l (b t j))
    (h : ∀ r t j, c r j ≤ a r t + b t j) (r : p) (j : n) : (M * Q) r j ∈ Per.FilD l (c r j) := by
  rw [Matrix.mul_apply]
  exact Submodule.sum_mem _ fun t _ => hanti _ _ (h r t j) (hmul _ _ _ _ (hM r t) (hQ t j))

theorem mul_comm_of_scalar {R : Type} [CommRing R] [IsDomain R] {d : ℕ} (X X' : Matrix (Fin d) (Fin d) R)
    (a : R) (ha : a ≠ 0) (h : X * X' = a • (1 : Matrix (Fin d) (Fin d) R)) :
    X' * X = a • (1 : Matrix (Fin d) (Fin d) R) := by
  have hdet : X.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
    exact pow_ne_zero _ ha this.symm
  have h1 : X * (X' * X - a • 1) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      sub_self]
  have h2 : X.det • (X' * X - a • 1) = 0 := by
    have : X.det • (X' * X - a • 1) = (X.adjugate * X) * (X' * X - a • 1) := by
      rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [this, Matrix.mul_assoc, h1, Matrix.mul_zero]
  have h3 : X' * X - a • 1 = 0 := by
    ext i j
    have := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at this
    simpa using (mul_eq_zero.1 this).resolve_left hdet
  exact sub_eq_zero.1 h3

theorem map_smul_ringHom {R S : Type} [CommRing R] [CommRing S] {p q : Type} (f : R →+* S) (a : R)
    (M : Matrix p q R) : (a • M).map f = f a • M.map f := by
  ext i j
  simp

theorem l_ne_zero {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) : (l : bk.S) ≠ 0 := by
  intro h
  have := congrArg (PowerSeries.constantCoeff) h
  simp only [map_natCast] at this
  have h1 := WittVector.coeff_p_one (p := l) (R := Fq l bk.a)
  rw [this] at h1
  simp at h1

set_option maxHeartbeats 1000000 in

theorem exists_modification_of_filtration : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (U U' : Matrix (Fin d) (Fin d) (Per.BdR l)), U * U' = 1 → ∀ (N m : ℕ) (k : Fin m → ℤ) (c : Matrix (Fin d) (Fin m) (↥(OL K))) (β : Matrix (Fin m) (Fin d) (Per.BdR l)), (∀ i, |k i| ≤ N) → (∀ r s, U r s ∈ Per.FilD l (-(N : ℤ))) → (∀ r i, (U * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom))) r i ∈ Per.FilD l (k i)) → (∀ i j, β i j ∈ Per.FilD l (-k i)) → U * c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) * β = 1 → ∃ (c₂ : ℕ) (X X' : Matrix (Fin d) (Fin d) (bk.S)), X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j) ∧ (∀ i j, (U * X.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev))) i j ∈ Per.FilD l N) ∧ (∀ i j, (X'.map ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) * U') i j ∈ Per.FilD l N) := by
  intro l _ K bk C d U U' hUU' N m k c β hk hU hUc hβ hUcβ
  obtain ⟨hFilP, hmul, hanti, hP, -, hxi, -⟩ := GlobalTheory.T.bdR_filtration_ker_theta_generator_facts l C (bk.ev bk.E) bk.span_ev
  have hcc_apply : ∀ r i, c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) r i =
      algebraMap (Per.BdRp l) (Per.BdR l) (C.o ((c r i : ↥K.1) : Om l)) := fun r i => rfl
  generalize c.map (C.oD.comp (K.1.val.toRingHom.comp (OL K).val.toRingHom)) = cc at hcc_apply hUc hUcβ ⊢
  have hφdef : ∀ x, ((algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev)) x =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (bk.ev x)) := fun x => rfl
  generalize (algebraMap (Per.BdRp l) (Per.BdR l)).comp ((aDp l).comp bk.ev) = φ at hφdef ⊢
  have hmap0 : ∀ z : Per.BdRp l, algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l 0 := by
    intro z
    have := (hP 0 z).2 (by rw [hFilP 0, pow_zero, Ideal.span_singleton_one]; exact Submodule.mem_top)
    simpa using this
  have hφ0 : ∀ x : bk.S, φ x ∈ Per.FilD l 0 := fun x => by rw [hφdef]; exact hmap0 _
  have hone : (1 : Per.BdR l) ∈ Per.FilD l 0 := by simpa using hmap0 1
  have hepow : ∀ n : ℕ, φ bk.E ^ n ∈ Per.FilD l n := by
    intro n
    have : φ bk.E ^ n * 1 ∈ Per.FilD l (0 + n) := by rw [hφdef]; exact (hxi 0 n 1).2 hone
    simpa using this
  have hlu : IsUnit ((l : ℕ) : Per.BdRp l) := by
    have h := (GlobalTheory.RingBasics.isUnit_l l).map (algebraMap (Per.AinfP l) (Per.BdRp l))
    rwa [map_natCast] at h
  have hl0 := l_ne_zero bk

  have hlift := fun r i => GlobalTheory.T.exists_breuilKisin_lift_compatible_bdR_prisms l K bk C (2 * N) (c r i)
  choose k0 s0 hs0 hnp0 using hlift
  obtain ⟨κ, hkκ⟩ : ∃ κ : ℕ, ∀ r i, k0 r i ≤ κ := ⟨Finset.univ.sup (fun p : Fin d × Fin m => k0 p.1 p.2),
    fun r i => Finset.le_sup (f := fun p : Fin d × Fin m => k0 p.1 p.2) (Finset.mem_univ (r, i))⟩
  have hlκ0 : (l : Per.BdR l) ^ κ ∈ Per.FilD l 0 := by simpa using hmap0 (((l : ℕ) : Per.BdRp l) ^ κ)
  obtain ⟨s, hs⟩ : ∃ s : Matrix (Fin d) (Fin m) bk.S, ∀ r i, s r i = (l : bk.S) ^ (κ - k0 r i) * s0 r i :=
    ⟨fun r i => (l : bk.S) ^ (κ - k0 r i) * s0 r i, fun _ _ => rfl⟩
  have hnp : ∀ r i, ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ,
      BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (BK.hf f (s r i) - BK.hf g (s r i)) := by
    intro r i B f g
    obtain ⟨k', hk'⟩ := hnp0 r i B f g
    refine ⟨k', ?_⟩
    have : (l : B.A) ^ k' * (BK.hf f (s r i) - BK.hf g (s r i)) =
        (l : B.A) ^ (κ - k0 r i) * ((l : B.A) ^ k' * (BK.hf f (s0 r i) - BK.hf g (s0 r i))) := by
      simp only [hs, map_mul, map_pow, map_natCast]; ring
    rw [this]
    exact Dvd.dvd.mul_left hk' _
  have hF : ∀ r i, (s.map φ - (l : Per.BdR l) ^ κ • cc) r i ∈ Per.FilD l ((2 * N : ℕ) : ℤ) := by
    intro r i
    have hmem : ((l : ℕ) : Per.BdRp l) ^ (κ - k0 r i) * (aDp l (bk.ev (s0 r i)) -
        ((l : ℕ) : Per.BdRp l) ^ k0 r i * C.o ((c r i : ↥K.1) : Om l)) ∈ Per.FilP l (2 * N) :=
      Ideal.mul_mem_left _ _ (hs0 r i)
    have h2 := (hP (2 * N) _).2 hmem
    convert h2 using 1
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, hcc_apply, smul_eq_mul]
    simp only [hφdef, hs, map_mul, map_pow, map_natCast, map_sub]
    rw [← pow_sub_mul_pow (l : Per.BdR l) (hkκ r i)]
    ring
  have hFt : ∀ t i, (s.map φ - (l : Per.BdR l) ^ κ • cc) t i ∈ Per.FilD l (2 * (N : ℤ)) := by
    intro t i; have := hF t i; push_cast at this; exact this
  obtain ⟨n, hn⟩ : ∃ n : Fin m → ℕ, ∀ i, (n i : ℤ) = N - k i := ⟨fun i => ((N : ℤ) - k i).toNat, fun i =>
    Int.toNat_of_nonneg (by have := (abs_le.1 (hk i)).2; linarith)⟩
  obtain ⟨c₂, X, X', R, Q, Q', hXX', hX, hY⟩ :=
    GlobalTheory.T.exists_breuilKisin_eisenstein_lattice_basis l K bk d m (2 * N) (s * Matrix.diagonal fun i => bk.E ^ n i)
  refine ⟨c₂, X, X', hXX', GlobalTheory.T.breuilKisin_changeOfBasis_no_pole_at_E l K bk d m N c₂ s n X X' R Q Q' hnp hXX' hX hY, ?_, ?_⟩
  ·
    have hXφ : X.map φ = (s.map φ * Matrix.diagonal (fun i => φ bk.E ^ n i)) * Q.map φ +
        φ bk.E ^ (2 * N) • R.map φ := by
      rw [hX, Matrix.map_add _ (map_add φ), Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero φ), map_smul_ringHom]
      simp only [map_pow]
    have hUs : ∀ r i, (U * s.map φ) r i = (l : Per.BdR l) ^ κ * (U * cc) r i +
        (U * (s.map φ - (l : Per.BdR l) ^ κ • cc)) r i := by
      intro r i
      simp [Matrix.mul_sub, Matrix.mul_smul]
    have hUs_mem : ∀ r i, ((U * s.map φ) * Matrix.diagonal (fun i => φ bk.E ^ n i)) r i ∈ Per.FilD l N := by
      intro r i
      rw [Matrix.mul_diagonal, hUs, add_mul]
      refine add_mem ?_ ?_
      · have h1 : (l : Per.BdR l) ^ κ * (U * cc) r i ∈ Per.FilD l (0 + k i) := hmul _ _ _ _ hlκ0 (hUc r i)
        have := hmul _ _ _ _ h1 (hepow (n i))
        rwa [hn i, show (0 + k i + (N - k i) : ℤ) = N by ring] at this
      · have h1 : (U * (s.map φ - (l : Per.BdR l) ^ κ • cc)) r i ∈ Per.FilD l N :=
          mulFil hmul hanti U _ (fun _ _ => -(N : ℤ)) (fun _ _ => 2 * (N : ℤ)) (fun _ _ => (N : ℤ)) hU hFt
            (fun _ _ _ => by linarith) r i
        have := hmul _ _ _ _ h1 (hepow (n i))
        exact hanti _ _ (by have := hn i; have := (abs_le.1 (hk i)).2; linarith) this
    intro r j
    rw [hXφ, Matrix.mul_add, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    refine add_mem ?_ ?_
    · exact mulFil hmul hanti _ _ (fun _ _ => (N : ℤ)) (fun _ _ => 0) (fun _ _ => (N : ℤ)) hUs_mem
        (fun t j => hφ0 _) (fun _ _ _ => by simp) r j
    · have h1 := mulFil hmul hanti U (R.map φ) (fun _ _ => -(N : ℤ)) (fun _ _ => 0) (fun _ _ => -(N : ℤ)) hU
        (fun t j => hφ0 _) (fun _ _ _ => by simp) r j
      have := hmul _ _ _ _ (hepow (2 * N)) h1
      exact hanti _ _ (by push_cast; linarith) this
  ·
    have ha : ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ bk.E_ne_zero)
    have hX'X := mul_comm_of_scalar X X' _ ha hXX'
    have hS : X' * (s * Matrix.diagonal fun i => bk.E ^ n i) = bk.E ^ (2 * N) • Q' := by
      have h1 : (l : bk.S) ^ c₂ • (X' * (s * Matrix.diagonal fun i => bk.E ^ n i)) =
          (l : bk.S) ^ c₂ • (bk.E ^ (2 * N) • Q') := by
        rw [← Matrix.mul_smul, hY, ← Matrix.mul_assoc, hX'X, Matrix.smul_mul, Matrix.one_mul, smul_smul]
      refine Matrix.ext fun r i => ?_
      have := congrFun (congrFun h1 r) i
      simp only [Matrix.smul_apply, smul_eq_mul] at this
      exact mul_left_cancel₀ (pow_ne_zero _ hl0) this
    have hcol : ∀ r i, (X'.map φ * s.map φ) r i * φ bk.E ^ n i = φ bk.E ^ (2 * N) * φ (Q' r i) := by
      intro r i
      have := congrArg φ (congrFun (congrFun hS r) i)
      rw [← Matrix.mul_assoc, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul, map_mul, map_mul, map_pow,
        map_pow] at this
      rw [← Matrix.map_mul]
      exact this
    have hXs : ∀ r i, (X'.map φ * s.map φ) r i ∈ Per.FilD l (N + k i) := by
      intro r i
      refine (hxi (N + k i) (n i) _).1 ?_
      rw [← hφdef]
      rw [mul_comm, hcol, hn i, show ((N : ℤ) + k i + (N - k i) : ℤ) = 2 * (N : ℤ) + 0 by ring]
      have := hmul _ _ _ _ (hepow (2 * N)) (hφ0 (Q' r i))
      push_cast at this
      exact this
    have hXc : ∀ r i, (l : Per.BdR l) ^ κ * (X'.map φ * cc) r i ∈ Per.FilD l (N + k i) := by
      intro r i
      have hsplit : (l : Per.BdR l) ^ κ * (X'.map φ * cc) r i = (X'.map φ * s.map φ) r i -
          (X'.map φ * (s.map φ - (l : Per.BdR l) ^ κ • cc)) r i := by
        simp [Matrix.mul_sub, Matrix.mul_smul]
      rw [hsplit]
      refine sub_mem (hXs r i) ?_
      exact mulFil hmul hanti _ _ (fun _ _ => 0) (fun _ _ => 2 * (N : ℤ)) (fun _ i => (N : ℤ) + k i)
        (fun _ _ => hφ0 _) hFt (fun _ _ i => by have := (abs_le.1 (hk i)).2; linarith) r i
    intro r j
    have hU'eq : U' = cc * β := by
      have h1 : U' * U = 1 := mul_eq_one_comm.1 hUU'
      calc U' = U' * (U * cc * β) := by rw [hUcβ, Matrix.mul_one]
        _ = (U' * U) * cc * β := by simp only [Matrix.mul_assoc]
        _ = cc * β := by rw [h1, Matrix.one_mul]
    have hfin : (l : Per.BdR l) ^ κ * (X'.map φ * U') r j ∈ Per.FilD l N := by
      rw [hU'eq, ← Matrix.mul_assoc, Matrix.mul_apply, Finset.mul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [← mul_assoc]
      have := hmul _ _ _ _ (hXc r i) (hβ i j)
      rwa [show (N : ℤ) + k i + -k i = N by ring] at this
    obtain ⟨u, hu⟩ := hlu
    have hinv : ((↑(u⁻¹ ^ κ) : Per.BdRp l)) * ((l : ℕ) : Per.BdRp l) ^ κ = 1 := by
      rw [← hu, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
    have key := Submodule.smul_mem _ ((↑(u⁻¹ ^ κ) : Per.BdRp l)) hfin
    rw [Algebra.smul_def, ← mul_assoc,
      show (l : Per.BdR l) ^ κ = algebraMap (Per.BdRp l) (Per.BdR l) (((l : ℕ) : Per.BdRp l) ^ κ) by simp,
      ← map_mul, hinv, map_one, one_mul] at key
    exact key

end GlobalTheory.BKModif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesLiftOfPeriodPowSmulIntegralMatr
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.KisinFF

theorem exists_of_inclW_eq_pow_mul {l : ℕ} [Fact l.Prime] (n : ℕ) : ∀ (a : Ainf l) (w : WCb l),
    inclW l a = (l : WCb l) ^ n * w → ∃ a', a = (l : Ainf l) ^ n * a' ∧ inclW l a' = w := by
  induction n with
  | zero => intro a w h; exact ⟨a, by simp, by simpa using h⟩
  | succ n ih =>
    intro a w h
    obtain ⟨a₁, ha₁⟩ := GlobalTheory.HWL.TensorWitt.ainf_saturated_in_tiltWitt_prime a ((l : WCb l) ^ n * w) (by rw [h]; ring)
    obtain ⟨a', ha', hw'⟩ := ih a₁ w ha₁
    refine ⟨a', ?_, hw'⟩
    have h1 : a = (l : Ainf l) * a₁ := by
      apply GlobalTheory.HWL.TensorWitt.inclW_injective
      rw [map_mul, map_natCast, ha₁, h]; ring
    rw [h1, ha']; ring

theorem scalar {l : ℕ} [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (M : ℕ)
    (w : WCb l) (hw : w ∈ bk.OE) (a : Ainf l) (ha : inclW l a = inclW l τ ^ M * w) :
    ∃ s : bk.S, bk.evW s = w := by
  classical
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB M
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hr
  obtain ⟨v, -, hv⟩ := (GlobalTheory.T.integral_elements_unit_factorization l K bk).2.1
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : bk.S, s₀ = c.sum fun i μ => μ * TB.c i a := ⟨_, rfl⟩
  have hev : ∀ t : bk.S, inclW l (bk.ev t) = bk.evW t := fun t => rfl
  have key : ∀ n : ℕ, (l : WCb l) ^ n ∣ bk.evW s₀ - (l : WCb l) ^ r * w := by
    intro n
    obtain ⟨m, s, y, h⟩ := hw n
    have hz : inclW l (bk.ev X ^ m * a - τ ^ M * bk.ev s) = (l : WCb l) ^ n * (inclW l τ ^ M * y) := by
      rw [map_sub, map_mul, map_mul, map_pow, map_pow, hev, hev, ha]
      linear_combination (inclW l τ ^ M) * h
    obtain ⟨z', hz', -⟩ := exists_of_inclW_eq_pow_mul n _ _ hz
    have hci : ∀ i, X ^ m * TB.c i a - s * TB.c i (τ ^ M) = (l : bk.S) ^ n * TB.c i z' := by
      intro i
      have := congrArg (TB.c i) hz'
      rw [map_sub, show bk.ev X ^ m = bk.ev (X ^ m) from (map_pow _ _ _).symm, TB.c_mul, mul_comm (τ ^ M) (bk.ev s), TB.c_mul,
        show ((l : Ainf l) ^ n) = bk.ev ((l : bk.S) ^ n) by simp, TB.c_mul] at this
      exact this
    obtain ⟨t, ht⟩ : ∃ t : bk.S, t = c.sum fun i μ => μ * TB.c i z' := ⟨_, rfl⟩
    have hS : X ^ m * s₀ - s * (l : bk.S) ^ r = (l : bk.S) ^ n * t := by
      rw [← hc, hs₀, ht]
      simp only [Finsupp.sum, Finset.mul_sum, smul_eq_mul]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by linear_combination c i * hci i
    have hW := congrArg bk.evW hS
    simp only [map_sub, map_mul, map_pow, map_natCast] at hW
    have hv' : bk.evW X ^ m * v ^ m = 1 := by rw [← mul_pow, hv, one_pow]
    refine ⟨v ^ m * (bk.evW t - (l : WCb l) ^ r * y), ?_⟩
    linear_combination v ^ m * hW - (l : WCb l) ^ r * v ^ m * h - (bk.evW s₀ - (l : WCb l) ^ r * w) * hv'
  have hd : bk.evW s₀ - (l : WCb l) ^ r * w = 0 := by
    refine IsHausdorff.haus' (I := Ideal.span {(l : WCb l)}) _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact key n
  obtain ⟨a', -, ha'⟩ := exists_of_inclW_eq_pow_mul r (bk.ev s₀) w (by rw [hev]; linear_combination hd)
  obtain ⟨s', hs'⟩ := GlobalTheory.T.integral_witt_element_of_evaluation l K bk w hw a' ha'.symm
  exact ⟨s', by rw [← hev, ← hs', ha']⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d d' M : ℕ) (X : Matrix (Fin d') (Fin d) (WCb l)) (x : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, X i j ∈ bk.OE) → x.map (inclW l) = inclW l τ ^ M • X → ∃ Y : Matrix (Fin d') (Fin d) bk.S, Y.map bk.evW = X := by
  intro l _ K bk τ hτ d d' M X x hX hx
  have he : ∀ i j, inclW l (x i j) = inclW l τ ^ M * X i j := fun i j => by
    have := congrFun (congrFun hx i) j
    simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using this
  choose Y hY using fun i j => scalar K bk τ hτ M (X i j) (hX i j) (x i j) (he i j)
  exact ⟨Y, Matrix.ext fun i j => hY i j⟩

end GlobalTheory.BSP.KisinFF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitAdelicMatrixLocalComponent
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem exists_split_loc : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (g : GA E a), ∃ (h : GA E a) (gw : GL (Fin a) (w.adicCompletion E)),
      g = h * finGL E a (locGL E a w gw) ∧
        ∀ u : GL (Fin a) (w.adicCompletion E),
          h * finGL E a (locGL E a w u) = finGL E a (locGL E a w u) * h := by
  intro E _ _ _ a w g
  obtain ⟨gw, hgw⟩ : ∃ gw, gw = GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) g) := ⟨_, rfl⟩
  refine ⟨g * (finGL E a (locGL E a w gw))⁻¹, gw, by rw [inv_mul_cancel_right], fun u => ?_⟩
  have hk : GeneralLinearGroup.map (pLoc E w)
      (GeneralLinearGroup.map (pFin E) (g * (finGL E a (locGL E a w gw))⁻¹)) = 1 := by
    rw [map_mul, map_inv, pFin_finGL, map_mul, map_inv, pLoc_locGL, hgw, mul_inv_cancel]
  generalize g * (finGL E a (locGL E a w gw))⁻¹ = k at hk ⊢
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, pInf_finGL, one_mul, mul_one]
  · rw [map_mul, map_mul, pFin_finGL]
    exact LocUniq.comm_locGL w hk u

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittPowerSeriesApproxMatrixBdRPlusStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wittPowerSeries_approx_matrix_bdRPlus : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (c : Matrix (Fin d) (Fin d) (Om l)), (∀ i j, c i j ∈ K.1) → ∀ n : ℕ, ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * C.o (c i j) ∈ Per.FilP l n := by
  first | (exact @GlobalTheory.LiftMatK.lift_matrix) | (exact GlobalTheory.LiftMatK.lift_matrix) | (intros; apply GlobalTheory.LiftMatK.lift_matrix  <;> assumption)
end

