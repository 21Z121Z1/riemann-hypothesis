import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0377
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0398
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0401
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableInvariantBdRPlusBasisApprox
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer.SFil

def texp {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) (x : R) :
    Matrix (Fin d) (Fin d) R :=
  ∑ i ∈ Finset.range d, (q ((i.factorial : ℚ)⁻¹) * x ^ i) • N ^ i

theorem map_sum_smul_pow {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {d : ℕ}
    (N : Matrix (Fin d) (Fin d) R) (a : ℕ → R) :
    (∑ i ∈ Finset.range d, a i • N ^ i).map f = ∑ i ∈ Finset.range d, f (a i) • (N.map f) ^ i := by
  change f.mapMatrix _ = ∑ i ∈ Finset.range d, f (a i) • (f.mapMatrix N) ^ i
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow]
  ext a b
  simp [RingHom.mapMatrix_apply]

theorem texp_map {R R' : Type} [CommRing R] [CommRing R'] (q : ℚ →+* R) (q' : ℚ →+* R') (f : R →+* R') {d : ℕ}
    (N : Matrix (Fin d) (Fin d) R) (x : R) : (texp q N x).map f = texp q' (N.map f) (f x) := by
  have e : q' = f.comp q := Subsingleton.elim _ _
  unfold texp
  rw [map_sum_smul_pow, e]
  simp only [map_mul, map_pow, RingHom.comp_apply]

theorem texp_add {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) (hN : N ^ d = 0)
    (x y : R) : texp q N x * texp q N y = texp q N (x + y) := by
  letI : Algebra ℚ R := q.toAlgebra
  have h : ∀ z : R, (z • N) ^ d = 0 := fun z => by rw [smul_pow, hN, smul_zero]
  have e : ∀ z : R, texp q N z = IsNilpotent.exp (z • N) := fun z => by
    rw [IsNilpotent.exp_eq_sum (h z)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_pow, mul_smul]
    exact algebraMap_smul R ((i.factorial : ℚ)⁻¹) _
  rw [e, e, e, add_smul, IsNilpotent.exp_add_of_commute _ ⟨d, h x⟩ ⟨d, h y⟩]
  exact ((Commute.refl N).smul_left x).smul_right y

theorem texp_zero {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) :
    texp q N 0 = 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  unfold texp
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [zero_pow hi]
  · intro h
    exact absurd (Finset.mem_range.2 hd) h

theorem texp_sub_mem {R : Type} [CommRing R] (q : ℚ →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) R) (I : Ideal R)
    {x y : R} (h : x - y ∈ I) (i j : Fin d) : (texp q N x - texp q N y) i j ∈ I := by
  unfold texp
  rw [← Finset.sum_sub_distrib, Matrix.sum_apply]
  refine I.sum_mem fun n _ => ?_
  rw [← sub_smul, Matrix.smul_apply, smul_eq_mul, ← mul_sub]
  exact I.mul_mem_right _ (I.mul_mem_left _ (Ideal.mem_of_dvd I (sub_dvd_pow_sub_pow x y n) h))

theorem cleared_map {S R : Type} [CommRing S] [CommRing R] (q : ℚ →+* R) (f : S →+* R) {d : ℕ}
    (N : Matrix (Fin d) (Fin d) S) {l : ℕ} (hl : l ≠ 0) (c e : ℕ) (a : ℕ → S)
    (ha : ∀ i < d, ((i.factorial : S) * (l : S) ^ (c * i)) * a i = (l : S) ^ e) (x : S) :
    (∑ i ∈ Finset.range d, (a i * x ^ i) • N ^ i).map f =
      (l : R) ^ e • texp q (N.map f) (q ((l : ℚ) ^ c)⁻¹ * f x) := by
  rw [map_sum_smul_pow]
  unfold texp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [smul_smul]
  congr 1
  have h1 := congrArg f (ha i (Finset.mem_range.1 hi))
  simp only [map_mul, map_pow, map_natCast] at h1
  have h2 : q ((i.factorial : ℚ)⁻¹) * q ((l : ℚ) ^ c)⁻¹ ^ i * ((i.factorial : R) * (l : R) ^ (c * i)) = 1 := by
    have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
    have hf : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
    rw [← map_natCast q, ← map_natCast q l, ← map_pow, ← map_pow, ← map_mul, ← map_mul, ← map_mul, ← map_one q]
    congr 1
    rw [pow_mul, inv_pow]
    field_simp
  rw [map_mul, map_pow, mul_pow, ← h1]
  linear_combination (-(f (a i) * f x ^ i)) * h2

theorem exists_cleared {l : ℕ} [Fact l.Prime] (c d : ℕ) :
    ∃ (e : ℕ) (a : ℕ → ℤ_[l]), ∀ i < d, ((i.factorial : ℤ_[l]) * (l : ℤ_[l]) ^ (c * i)) * a i = (l : ℤ_[l]) ^ e := by
  obtain ⟨e, m, hm, hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd d.factorial_ne_zero l (Fact.out : l.Prime).ne_one
  refine ⟨e + c * d, fun i => ecoef l (e + c * d) c i, fun i hi => ?_⟩
  apply Subtype.ext
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hf0 : (i.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero i)
  push_cast
  rw [ecoef_val (ecoefQ_norm_le c hm hd hi)]
  unfold ecoefQ
  field_simp

theorem approx {l : ℕ} [Fact l.Prime] {S R : Type} [CommRing S] [IsDomain S] [CharZero S] [CommRing R]
    (z : ℤ_[l] →+* S) (q : ℚ →+* R) (f : S →+* R) {d : ℕ} (N : Matrix (Fin d) (Fin d) S) (hN : N ^ d = 0)
    (I : Ideal R) (k k' : ℕ) (s : S) (lam : R) (h : f s - (l : R) ^ k' * lam ∈ I) :
    ∃ (e : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) S), Λ * Λ' = (l : S) ^ (2 * e) • (1 : Matrix (Fin d) (Fin d) S) ∧
      ∀ i j, (Λ.map f - (l : R) ^ e • texp q (N.map f) (-(q ((l : ℚ) ^ k)⁻¹ * lam))) i j ∈ I := by
  obtain ⟨e, a, ha⟩ := exists_cleared (l := l) (k + k') d
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have ha' : ∀ i < d, ((i.factorial : S) * (l : S) ^ ((k + k') * i)) * z (a i) = (l : S) ^ e := fun i hi => by
    simpa only [map_mul, map_pow, map_natCast] using congrArg z (ha i hi)
  refine ⟨e, ∑ i ∈ Finset.range d, (z (a i) * (-s) ^ i) • N ^ i, ∑ i ∈ Finset.range d, (z (a i) * s ^ i) • N ^ i,
    ?_, fun i j => ?_⟩
  · have hinj := IsFractionRing.injective S (FractionRing S)
    apply Matrix.map_injective hinj
    have hN' : (N.map (algebraMap S (FractionRing S))) ^ d = 0 := by
      change ((algebraMap S (FractionRing S)).mapMatrix N) ^ d = 0
      rw [← map_pow, hN, map_zero]
    change Matrix.map _ _ = Matrix.map _ _
    rw [Matrix.map_mul, cleared_map (algebraMap ℚ _) _ N hl _ _ _ ha', cleared_map (algebraMap ℚ _) _ N hl _ _ _ ha',
      Matrix.smul_mul, Matrix.mul_smul, texp_add _ _ hN', map_neg, mul_neg, neg_add_cancel, texp_zero, smul_smul,
      ← pow_add, two_mul]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  · rw [cleared_map q f N hl _ _ _ ha', ← smul_sub, Matrix.smul_apply, smul_eq_mul]
    refine I.mul_mem_left _ (texp_sub_mem q _ I ?_ i j)
    have h2 : q ((l : ℚ) ^ k)⁻¹ = q ((l : ℚ) ^ (k + k'))⁻¹ * (l : R) ^ k' := by
      have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl
      rw [← map_natCast q l, ← map_pow, ← map_mul]
      congr 1
      field_simp
      ring
    have h3 := I.mul_mem_left (-q ((l : ℚ) ^ (k + k'))⁻¹) h
    convert h3 using 1
    rw [h2, map_neg]
    ring

theorem invariant_basis_approx : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (U : Matrix (Fin d) (Fin d) (Per.Bcris l)) (k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) (c : ↥(GK K) → ℤ_[l]), Mn ^ d = 0 → (∀ g : ↥(GK K), (ρ g).map (Per.zB l) * U.map (Per.σB (g : GQ l)) = U * ∑ i ∈ Finset.range d, (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) * (Per.zB l (c g) * C.tB) ^ i) • (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)) ^ i) → ∀ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) → ∃ Λ₀ : Matrix (Fin d) (Fin d) (Per.BdRp l), (∀ g : ↥(GK K), (ρ g).map (Per.zD l) * (U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))).map (Per.σD (g : GQ l)) = U.map C.ι * Λ₀.map (algebraMap (Per.BdRp l) (Per.BdR l))) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ Λ' : Matrix (Fin d) (Fin d) (bk.S)), Λ * Λ' = (l : bk.S) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ ∀ i j, (Λ.map ((aDp l).comp bk.ev) - (l : Per.BdRp l) ^ k • Λ₀) i j ∈ Per.FilP l m := by
  intro l _ K bk P AI T C hF d ρ U k Mn c hMn hU lam hlam happ
  obtain ⟨-, -, -, -, -, -, -, -, -, hD, hDp, -, -⟩ := ActLaws.act_laws l
  let q : ℚ →+* Per.BdRp l := C.o.comp (algebraMap ℚ (Om l))
  let a : Per.BdRp l →+* Per.BdR l := algebraMap (Per.BdRp l) (Per.BdR l)
  let w : Wq l bk.a →+* Per.BdRp l := (aDp l).comp (wA l bk.a).toRingHom
  refine ⟨texp q (Mn.map w) (-(q ((l : ℚ) ^ k)⁻¹ * lam)), fun g => ?_, fun m => ?_⟩
  · have hN : ((Mn.map w).map a) ^ d = 0 := by
      change (a.mapMatrix (w.mapMatrix Mn)) ^ d = 0
      rw [← map_pow, ← map_pow, hMn, map_zero, map_zero]
    have hNσ : ((Mn.map w).map a).map (Per.σD (g : GQ l)) = (Mn.map w).map a := by
      ext i j
      change Per.σD (g : GQ l) (a (aDp l (wA l bk.a (Mn i j)))) = a (aDp l (wA l bk.a (Mn i j)))
      rw [hD, hDp, bk.gal_w]
    have hq : ∀ x : ℚ, Per.σD (g : GQ l) (a (q x)) = a (q x) := fun x =>
      RingHom.congr_fun (Subsingleton.elim ((Per.σD (g : GQ l)).comp (a.comp q)) (a.comp q)) x
    have hqB : ∀ x : ℚ, C.ι (C.qB (x : ℚ_[l])) = a (q x) := fun x =>
      RingHom.congr_fun (Subsingleton.elim (C.ι.comp (C.qB.comp (Rat.castHom ℚ_[l]))) (a.comp q)) x
    have h1 := congrArg (fun M => Matrix.map M C.ι) (hU g)
    simp only [Matrix.map_mul] at h1
    rw [map_sum_smul_pow] at h1
    have e1 : ((ρ g).map (Per.zB l)).map C.ι = (ρ g).map (Per.zD l) := by
      ext i j
      change C.ι (Per.zB l (ρ g i j)) = Per.zD l (ρ g i j)
      rw [← T.zB, ← hF.ι, AlgHom.commutes, T.zD]
    have e2 : (U.map (Per.σB (g : GQ l))).map C.ι = (U.map C.ι).map (Per.σD (g : GQ l)) := by
      ext i j
      exact ULaws.iota_sigma C _ _
    have e3 : (Mn.map ((Per.aB l).comp (wA l bk.a).toRingHom)).map C.ι = (Mn.map w).map a := by
      ext i j
      exact ULaws.iota_aB C _
    have e4 : ∑ i ∈ Finset.range d, C.ι (C.qB (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) *
        (Per.zB l (c g) * C.tB) ^ i) • ((Mn.map w).map a) ^ i =
        texp (a.comp q) ((Mn.map w).map a) (a (q ((l : ℚ) ^ k)⁻¹) * a (aDp l (Per.zA l (c g)) * C.j C.t)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have e5 : (((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹) =
          (((i.factorial : ℚ)⁻¹ * ((l : ℚ) ^ k)⁻¹ ^ i : ℚ) : ℚ_[l]) := by
        push_cast
        rw [mul_inv, pow_mul, inv_pow]
      have e6 : C.ι (Per.zB l (c g)) = a (aDp l (Per.zA l (c g))) := by
        rw [← ULaws.u_padicInt C, C.ι_u, ← C.o_sec.z]
        rfl
      have e7 : C.ι C.tB = a (C.j C.t) := C.ι_j _
      rw [map_mul C.ι, e5, hqB, map_pow C.ι, map_mul C.ι, e6, e7]
      simp only [map_mul, map_pow, RingHom.comp_apply, mul_pow]
      ring
    rw [e1, e2, e3, e4] at h1
    change _ * (U.map C.ι * Matrix.map _ a).map _ = U.map C.ι * Matrix.map _ a
    rw [texp_map q (a.comp q) a, Matrix.map_mul, texp_map (a.comp q) (a.comp q), hNσ, ← Matrix.mul_assoc, h1,
      Matrix.mul_assoc, texp_add _ _ hN]
    congr 2
    have e8 : Per.σD (g : GQ l) (a lam) = a lam + a (aDp l (Per.zA l (c g)) * C.j C.t) :=
      (hD _ lam).trans ((congrArg a (hlam g)).trans (map_add a _ _))
    rw [map_neg a, map_mul a (q _), map_neg, map_mul (Per.σD (g : GQ l)), hq, e8]
    ring
  · obtain ⟨k', s, -, hs⟩ := happ m
    haveI : CharZero bk.S := RingHom.charZero ((Per.θD l).comp ((aDp l).comp bk.ev))
    have hN : (Mn.map (PowerSeries.C : Wq l bk.a →+* bk.S)) ^ d = 0 := by
      change ((PowerSeries.C : Wq l bk.a →+* bk.S).mapMatrix Mn) ^ d = 0
      rw [← map_pow, hMn, map_zero]
    have e1 : (Mn.map (PowerSeries.C : Wq l bk.a →+* bk.S)).map ((aDp l).comp bk.ev) = Mn.map w := by
      ext i j
      exact congrArg (aDp l) (bk.ev_C _)
    have := approx ((PowerSeries.C : Wq l bk.a →+* bk.S).comp (algebraMap ℤ_[l] (Wq l bk.a))) q
      ((aDp l).comp bk.ev) _ hN (Per.FilP l m) k k' s lam hs
    rwa [e1] at this

end GlobalTheory.SstPer.SFil

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SignsAndJumpSetsAtTypePrime
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.HostJumpSets

open AdmissibleParameterJ

variable {D : D7}

theorem Jp_finite (j : ℕ) (ρ : D.what₂.Tau) : (Jp D j ρ).Finite := by
  refine (((Set.finite_range fun a : Fin (D.R.k - 1) => sz D j ρ + (D.hc ρ).v a + c0 D).union
    (Set.finite_range fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D)).union
    (Set.finite_range fun c : Fin D.R.t => ((c : ℕ) : ℚ))).subset ?_
  rintro q ((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨c, hc, rfl⟩)
  · exact Or.inl (Or.inl ⟨a, rfl⟩)
  · exact Or.inl (Or.inr ⟨a, rfl⟩)
  · exact Or.inr ⟨⟨c, hc⟩, rfl⟩

theorem refl_injective : Function.Injective (AdmissibleParameterJ.refl D) := by
  intro x y h
  simp only [AdmissibleParameterJ.refl] at h
  linarith

theorem refl_surjective : Function.Surjective (AdmissibleParameterJ.refl D) := by
  intro y
  refine ⟨((D.R.t : ℚ) - 1) - y, ?_⟩
  simp only [AdmissibleParameterJ.refl]
  ring

theorem JJ_finite (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : (JJ D up j ρ).Finite := by
  cases up
  · exact (Jp_finite j ρ).preimage refl_injective.injOn
  · exact Jp_finite j ρ

theorem JJ_ncard (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : (JJ D up j ρ).ncard = (Jp D j ρ).ncard := by
  cases up
  · exact Set.ncard_preimage_of_injective_subset_range refl_injective
      (fun q _ => refl_surjective q)
  · rfl

theorem abs_le_two_b (L : SizeData₂ D) (hJe : JumpAbsoluteBound L) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) (q : ℚ) (hq : q ∈ JJ D up j ρ) : |(q : ℝ)| ≤ 2 * L.sc.b :=
  ((hJe.1 j hj1 hj2 ρ up q hq).trans hJe.2.1).trans hJe.2.2.2

theorem elem_ok (L : SizeData₂ D) (hJb : CloudCentreDistance L) (hJc : jcCondition L) (hJe : JumpAbsoluteBound L)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m) (ρ : D.what₂.Tau)
    (up : Bool) (a : ℤ) (ha : (a : ℚ) ∈ JJ D up j ρ) :
    ((0 ≤ a ∧ a < D.R.t) ∨ |(a : ℚ) - PairedCharacterCondition.cen (D := D)| ≤ (⌊L.etaSz⌋₊ : ℚ) + 1 ∨
        PairedCharacterCondition.cloud (D := D) up (⌊3 * L.sc.b⌋₊ + 2 + 0) a) ∧ a ≠ -1 ∧ a ≠ D.R.t := by
  have hnot := (hJc j hj1 hj2 ρ).2.1 up
  refine ⟨?_, fun h => hnot.1 (by rw [h] at ha; exact_mod_cast ha),
    fun h => hnot.2 (by rw [h] at ha; exact_mod_cast ha)⟩
  have hfl : 3 * L.sc.b < (⌊3 * L.sc.b⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfe : L.etaSz < (⌊L.etaSz⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _

  have hcl : ∀ q ∈ cloudJ D j ρ, (D.R.t : ℚ) + 1 < q ∧ q ≤ ((⌊3 * L.sc.b⌋₊ + 2 + 0 : ℕ) : ℚ) := by
    intro q hq
    refine ⟨(hJc j hj1 hj2 ρ).2.2.1 q hq, ?_⟩
    have h2 := abs_le_two_b L hJe hj1 hj2 ρ true q (Or.inl (Or.inl hq))
    have h3 : (q : ℝ) ≤ ((⌊3 * L.sc.b⌋₊ + 2 + 0 : ℕ) : ℝ) := by
      push_cast
      linarith [le_abs_self (q : ℝ)]
    exact_mod_cast h3
  have hlow : ∀ q ∈ lowJ D j ρ, |q - c0 D| ≤ (⌊L.etaSz⌋₊ : ℚ) + 1 := by
    intro q hq
    have h1 := (hJb j hj1 hj2 ρ).2.1 q hq
    have h2 : ((|q - c0 D| : ℚ) : ℝ) ≤ (((⌊L.etaSz⌋₊ : ℚ) + 1 : ℚ) : ℝ) := by
      push_cast at h1 ⊢
      linarith
    exact_mod_cast h2
  cases up
  ·
    change AdmissibleParameterJ.refl D (a : ℚ) ∈ Jp D j ρ at ha
    rcases ha with (hq | hq) | ⟨c, hc, hx⟩
    · right; right
      obtain ⟨h1, h2⟩ := hcl _ hq
      simp only [PairedCharacterCondition.cloud, PairedCharacterCondition.cen, AdmissibleParameterJ.refl] at h1 h2 ⊢
      simp only [Bool.false_eq_true, if_false]
      constructor <;> linarith
    · right; left
      have h := hlow _ hq
      simp only [PairedCharacterCondition.cen, AdmissibleParameterJ.refl, c0] at h ⊢
      rw [show (a : ℚ) - ((D.R.t : ℚ) - 1) / 2 = -((D.R.t : ℚ) - 1 - (a : ℚ) - ((D.R.t : ℚ) - 1) / 2) by ring,
        abs_neg]
      exact h
    · left
      simp only [AdmissibleParameterJ.refl] at hx
      have hx' : (a : ℚ) = ((D.R.t : ℤ) - 1 - (c : ℤ) : ℤ) := by push_cast; linarith
      have hx'' : a = (D.R.t : ℤ) - 1 - c := by exact_mod_cast hx'
      omega
  · change (a : ℚ) ∈ Jp D j ρ at ha
    rcases ha with (hq | hq) | ⟨c, hc, hx⟩
    · right; right
      obtain ⟨h1, h2⟩ := hcl _ hq
      simp only [PairedCharacterCondition.cloud, PairedCharacterCondition.cen, if_true]
      constructor <;> linarith
    · right; left
      exact hlow _ hq
    · left
      have hx'' : a = c := by exact_mod_cast hx
      omega

theorem algHom_eq_of_finrank_one {F K A : Type} [Field F] [Field K] [Ring A] [Algebra F K] [Algebra F A]
    (h : finrank F K = 1) (f g : K →ₐ[F] A) : f = g := by
  ext x
  have hx : x ∈ (⊥ : Subalgebra F K) := by
    rw [Subalgebra.bot_eq_top_of_finrank_eq_one h]; trivial
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hx
  simp

theorem emb_inj (D : D7) : Function.Injective D.host.emb := by
  intro g g' h
  have h1 : D.host.sigmaOf g = D.host.sigmaOf g' :=
    AlgEquiv.ext fun x => D.host.φ₀.injective (RingHom.congr_fun h x)
  exact (D.host.gal).symm.injective h1

theorem decide_flip {P Q : Prop} {iP : Decidable P} {iQ : Decidable Q} (h : P ↔ ¬ Q) :
    @decide P iP = !@decide Q iQ := by
  by_cases hq : Q
  · rw [decide_eq_true hq, decide_eq_false (fun hp => h.1 hp hq)]; rfl
  · rw [decide_eq_false hq, decide_eq_true (h.2 hq)]; rfl

theorem typeU_flip (D : D7) (ep : Bool) (g : D.R.GG) :
    TypeU D ep g ↔ ¬ TypeU D ep (g * D.R.cc) := by
  have hP := Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g
  unfold TypeU
  cases ep <;> by_cases h : g ∈ D.R.Psi <;> simp_all

def incl (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 :=
  ((D.nbr i w hw).Kw.1.val).codRestrict (D.nbr i w hw).LL.1.toSubalgebra
    (fun x => (D.nbr i w hw).LL_split (D.nbr i w hw).Kw.1.val x)

end GlobalTheory.HostJumpSets

end

noncomputable section

namespace GlobalTheory.HostJumpSets

open AdmissibleParameterJ

theorem main : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → (D.R.t : ℝ) ≤ L.sc.b → ∀ (i : D.nd.Loc) (k : Fin 2) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), D.nd.l i = D.host.g k → GoodR D.nd i r → ∃ (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i r ⌊L.etaSz⌋₊ (⌊3 * L.sc.b⌋₊ + 2) 0 sg U := by
  intro D L ep hJa hJb hJc hJe _htb i k r hk hgood
  obtain ⟨hdeg, hemb⟩ := GlobalTheory.TypePlace.type_prime_places D i k hk
  have hj := D.nd.j_range i
  have hex := fun w (hw : w ∈ placesOver D.host.E (D.nd.l i)) =>
    hJa i r hgood w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (incl D i w hw)
  choose gf ρf hR hJ using hex
  classical
  let sg : HeightOneSpectrum (𝓞 D.host.E) → Bool := fun w =>
    if hw : w ∈ placesOver D.host.E (D.nd.l i) then decide (TypeU D ep (gf w hw)) else false
  let U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ := fun w =>
    if hw : w ∈ placesOver D.host.E (D.nd.l i) then
      (Finset.Icc (-((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)).filter
        (fun a : ℤ => (a : ℚ) ∈ JJ D (sg w) (D.nd.j i) (ρf w hw))
    else ∅
  have hsg : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), sg w = decide (TypeU D ep (gf w hw)) :=
    fun w hw => dif_pos hw
  refine ⟨sg, U, ?_, ?_⟩
  · intro w w' hw hc _hne
    have hw' : w' ∈ placesOver D.host.E (D.nd.l i) := by
      have := hc ((D.nd.l i : ℕ) : 𝓞 D.host.E) ((D.nd.l i : ℕ) : 𝓞 D.host.E) (by simp)
      exact this.1 hw
    have hind : ∀ v (hv : v ∈ placesOver D.host.E (D.nd.l i)),
        InducesW D.nd i (gEmb (TruncatedSeriesCountingIdentities.CoefExt.self i v hv) (incl D i v hv)) v := fun v hv =>
      (GlobalTheory.LocalEmbedding.inducesW_and_exists_emb D i v hv _ (incl D i v hv) _ (fun _ => rfl)).1
    have heq : gEmb (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (incl D i w hw) =
        (gEmb (TruncatedSeriesCountingIdentities.CoefExt.self i w' hw') (incl D i w' hw')).comp (D.host.conj : D.host.E →+* D.host.E) := by
      apply hemb
      intro x
      let X : 𝓞 D.host.E := ⟨(D.host.conj : D.host.E →+* D.host.E) (x : D.host.E),
        (RingOfIntegers.isIntegral_coe x).map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom⟩
      rw [hind w hw x, RingHom.comp_apply]
      have h2 := hind w' hw' X
      rw [show ((X : 𝓞 D.host.E) : D.host.E) = (D.host.conj : D.host.E →+* D.host.E) (x : D.host.E) from rfl] at h2
      rw [h2]
      exact hc x X rfl
    have hg : gf w hw = gf w' hw' * D.R.cc := by
      apply emb_inj D
      rw [Formalism.L2.Geo.emb_mul_cc_comp, ← (hR w hw).1, ← (hR w' hw').1, heq]
      rfl
    rw [hsg w hw, hsg w' hw', hg]
    exact decide_flip (typeU_flip D ep (gf w' hw'))
  · intro w hw
    have hU : U w = (Finset.Icc (-((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)).filter
        (fun a : ℤ => (a : ℚ) ∈ JJ D (sg w) (D.nd.j i) (ρf w hw)) := dif_pos hw
    refine ⟨?_, ?_, ?_⟩
    · rw [hU, ← Set.ncard_coe_finset]
      have h1 : ((Finset.filter (fun a : ℤ => (a : ℚ) ∈ JJ D (sg w) (D.nd.j i) (ρf w hw))
          (Finset.Icc (-((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) : Finset ℤ) : Set ℤ).ncard ≤
          (JJ D (sg w) (D.nd.j i) (ρf w hw)).ncard :=
        Set.ncard_le_ncard_of_injOn (fun a : ℤ => (a : ℚ))
          (fun a ha => (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2)
          (fun a _ b _ h => Int.cast_injective h) (JJ_finite _ _ _)
      rw [JJ_ncard] at h1
      exact h1.trans_eq ((hJb _ hj.1 hj.2 (ρf w hw)).2.2.2.2.2)
    · intro x τ a ha
      obtain rfl : τ = incl D i w hw := algHom_eq_of_finrank_one (hdeg w hw).1 _ _
      have e : TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (rTwO D.nd i r x) = Br.loc D.nbr i w hw (rTwO D.nd i r x) := by
        ext; rfl
      have h1 := ((hJ w hw).1 x a).1
      rw [e] at h1
      have hmem := h1.1 ha
      rw [← hsg w hw] at hmem
      rw [hU, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨?_, hmem⟩
      have hb := abs_le_two_b L hJe hj.1 hj.2 (ρf w hw) _ _ hmem
      have hfl : 3 * L.sc.b < (⌊3 * L.sc.b⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h0 : 0 ≤ L.sc.b := by linarith [abs_nonneg ((a : ℚ) : ℝ)]
      rw [abs_le] at hb
      push_cast at hb
      have h3 : (a : ℝ) ≤ ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
      have h4 : -((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℝ) ≤ (a : ℝ) := by push_cast; linarith
      constructor
      · exact_mod_cast h4
      · exact_mod_cast h3
    · intro a ha
      rw [hU, Finset.mem_filter] at ha
      exact elem_ok L hJb hJc hJe hj.1 hj.2 (ρf w hw) (sg w) a ha.2

end GlobalTheory.HostJumpSets

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanSingletonClosedOfBoundedTorsionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_singleton_of_bounded_torsion_of_adic_limit : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (d : A) (N : ℕ), d ∈ nonZeroDivisors A → (∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d}) → IsAdicComplete (Ideal.span {(l : A)} ⊔ Ideal.span {d}) A → ∀ x : A, (∀ n : ℕ, ∃ z, x - d * z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n) → x ∈ Ideal.span {d} := by
  first | exact @GlobalTheory.BSP.span_singleton_closed_of_bounded_torsion | exact GlobalTheory.BSP.span_singleton_closed_of_bounded_torsion | (intros; apply GlobalTheory.BSP.span_singleton_closed_of_bounded_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCharpolyLatticeKillsSpanStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_charpoly_lattice_kills_span : ∀ (O V B : Type) [CommRing O] [IsDomain O] [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V] [FiniteDimensional (FractionRing O) V] [AddCommGroup B] [Module O B] [Module.Free O B] [Module.Finite O B] (e : B →ₗ[O] V) (t : Module.End O B) (T : Module.End (FractionRing O) V), (∀ x, e (t x) = T (e x)) → ((LinearMap.charpoly t).map (algebraMap O (FractionRing O))).Splits → ∃ p : (FractionRing O)[X], p ≠ 0 ∧ p.Splits ∧ ∀ x ∈ Submodule.span (FractionRing O) (Set.range e), Polynomial.aeval T p x = 0 := by
  first | exact @GlobalTheory.charpoly_split_kills_span | exact GlobalTheory.charpoly_split_kills_span | (intros; apply GlobalTheory.charpoly_split_kills_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtNegPrimeMemPadicCyclotomicStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrt_neg_prime_mem_padic_cyclotomic : ∀ (l : ℕ) [Fact l.Prime], l % 4 = 3 → ∀ y : Om l, y ^ 2 = -(l : Om l) → y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} := by
  first | exact @GlobalTheory.sqrt_neg_l_mem_adjoin_roots_of_unity | exact GlobalTheory.sqrt_neg_l_mem_adjoin_roots_of_unity | (intros; apply GlobalTheory.sqrt_neg_l_mem_adjoin_roots_of_unity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtNegPrimeNotMemMaxUnramifiedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrt_neg_prime_not_mem_max_unramified : ∀ (l : ℕ) [Fact l.Prime] (y : Om l), y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l := by
  first | exact @GlobalTheory.sqrt_neg_l_not_mem_Kur | exact GlobalTheory.sqrt_neg_l_not_mem_Kur | (intros; apply GlobalTheory.sqrt_neg_l_not_mem_Kur <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulCocycleValuesZeroOnSmallSubgroupStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_mul_cocycle_values_zero_on_small_subgroup : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → κ z = 1 → (∀ g ∈ L, κ g = 1) → ∀ (x : Z1 (repOn (Tgl i s) κ A)) (y : Z1 (repOn ρ κ⁻¹ A)), (∀ h ∈ L, bform (X := X) x.1 y.1 h = 0) → ∀ h ∈ L, ∀ h' ∈ L, ∀ a b, (X.l i : A) ^ nu X i * x.1 h a * y.1 h' b = 0 := by
  first | exact @GlobalTheory.NewPrime.FormVanish.two_mul_values_eq_zero | exact GlobalTheory.NewPrime.FormVanish.two_mul_values_eq_zero | (intros; apply GlobalTheory.NewPrime.FormVanish.two_mul_values_eq_zero <;> assumption)
end

