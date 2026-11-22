import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1270
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteWeilRepEqLatticeIntertwinerMulCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePointSignEqThetaLawSemicharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1854
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalarInertPlaceInvertibleShifts
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertScalarUnit

open GlobalTheory.LatVac

theorem exists_ne_of_cm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra h
  push_neg at h
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : NumberField.ComplexEmbedding.IsReal τ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    have h1 := hσ.2.2.2 τ x
    rw [h x] at h1
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq, starRingEnd_apply]
    exact h1.symm
  exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.2
    (hσ.2.1.isComplex (NumberField.InfinitePlace.mk τ))) ⟨τ, hreal, rfl⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem idem_smul_of_at {M : Type} [AddCommGroup M] [Module (AF F) M] (v : Pl F) (u : M)
    (hu : At (evFin F v) u) : GlobalTheory.LatVac.liftV v (1 : Fv F v) • u = u := by
  have h := hu (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])
  rw [sub_smul, one_smul] at h
  exact (sub_eq_zero.1 h).symm

theorem idem_mul (v : Pl F) (x : AF F) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) * x = GlobalTheory.LatVac.liftV v (evFin F v x) := by
  have h := at_liftV v (1 : Fv F v) (x - GlobalTheory.LatVac.liftV v (evFin F v x)) (by rw [map_sub, evFin_liftV, sub_self])
  have h2 := idem_smul_of_at v _ (at_liftV v (evFin F v x))
  rw [smul_eq_mul] at h h2
  linear_combination h + h2

theorem at_idem_smul {M : Type} [AddCommGroup M] [Module (AF F) M] (v : Pl F) (z : M) :
    At (evFin F v) (GlobalTheory.LatVac.liftV v (1 : Fv F v) • z) := by
  intro u hu
  rw [smul_smul, ← smul_eq_mul, at_liftV v 1 u hu, zero_smul]

theorem idem_smul_eq_zero (v : Pl F) (a : AE F E) (ha : compFin F E v a = 0) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • a = 0 := by
  have key : ∀ a : AE F E, GlobalTheory.LatVac.liftV v (1 : Fv F v) • a =
      (GlobalTheory.LatVac.liftV v).rTensor E (compFin F E v a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul x e =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, idem_mul]
      simp [compFin]
    | add x y hx hy => rw [smul_add, hx, hy, map_add, map_add]
  rw [key, ha, map_zero]

theorem compFin_lift (v : Pl F) (q : Fv F v ⊗[F] E) :
    compFin F E v ((GlobalTheory.LatVac.liftV v).rTensor E q) = q := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul x e => simp [compFin, evFin_liftV]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem exists_inv_at (v : Pl F) {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE F E))
    (h : IsUnit (M.map (compFin F E v)).det) :
    ∃ b : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) b ∧
      b * M = GlobalTheory.LatVac.liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      M * b = GlobalTheory.LatVac.liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
  set Mv := M.map (compFin F E v) with hMv
  set Q : Matrix (Fin n) (Fin n) (AE F E) := Mv⁻¹.map ((GlobalTheory.LatVac.liftV v).rTensor E) with hQdef
  have hQ : Q.map (compFin F E v) = Mv⁻¹ := by
    ext i j
    simp [hQdef, compFin_lift]
  have hz : ∀ N : Matrix (Fin n) (Fin n) (AE F E), N.map (compFin F E v) = 1 →
      GlobalTheory.LatVac.liftV v (1 : Fv F v) • N = GlobalTheory.LatVac.liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    intro N hN
    have h0 : GlobalTheory.LatVac.liftV v (1 : Fv F v) • (N - 1) = 0 := by
      ext i j
      rw [Matrix.smul_apply, Matrix.zero_apply]
      apply idem_smul_eq_zero
      have := congrFun (congrFun hN i) j
      rw [Matrix.map_apply] at this
      rw [Matrix.sub_apply, map_sub, this]
      by_cases hij : i = j
      · subst hij; simp
      · simp [Matrix.one_apply_ne hij]
    rwa [smul_sub, sub_eq_zero] at h0
  refine ⟨GlobalTheory.LatVac.liftV v (1 : Fv F v) • Q, at_idem_smul v Q, ?_, ?_⟩
  · rw [Matrix.smul_mul]
    apply hz
    rw [← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hQ, ← hMv,
      Matrix.nonsing_inv_mul _ h]
  · rw [Matrix.mul_smul]
    apply hz
    rw [← RingHom.mapMatrix_apply, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, hQ, ← hMv,
      Matrix.mul_nonsing_inv _ h]

end GlobalTheory.InertScalarUnit

namespace GlobalTheory.InertScalarUnit

open GlobalTheory.LatVac

theorem exists_scalar_inv_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (g : UA σ J),
    ∃ k : UA σ J, At (evFin F v) (mat k - 1) ∧ ∃ a b : Matrix (Fin n) (Fin n) (AE F E), At (evFin F v) a ∧ At (evFin F v) b ∧
      a * (1 - mat k) = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      (1 - mat k) * a = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      b * (1 - mat (g⁻¹ * k)) = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) ∧
      (1 - mat (g⁻¹ * k)) * b = liftV v (1 : Fv F v) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
  intro F E _ _ _ _ _ σ B hB v w hw n J g
  have hK := GlobalTheory.InertTensorField.isField_tensor_of_isInertAt F E σ B hB v w hw
  haveI : IsDomain (Fv F v ⊗[F] E) := hK.isDomain
  have hunit : ∀ x : Fv F v ⊗[F] E, x ≠ 0 → IsUnit x := fun x hx => by
    obtain ⟨y, hy⟩ := hK.mul_inv_cancel hx
    exact ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
  have hσσ := GlobalTheory.AdelicU.cm_conj_conj hB.cm
  obtain ⟨x₀, hx₀⟩ := exists_ne_of_cm σ hB.cm
  obtain ⟨ξ, hξ, hξ0⟩ : ∃ ξ : E, σ ξ = -ξ ∧ ξ ≠ 0 :=
    ⟨x₀ - σ x₀, by rw [map_sub, hσσ]; ring, sub_ne_zero.2 (Ne.symm hx₀)⟩
  let ι : E →+* Fv F v ⊗[F] E := (Algebra.TensorProduct.includeRight : E →ₐ[F] Fv F v ⊗[F] E).toRingHom
  have hι : Function.Injective ι := ι.injective
  set gv := (mat g).map (compFin F E v) with hgv
  have hp0 : gv.charpoly ≠ 0 := (Matrix.charpoly_monic gv).ne_zero
  have hfin := Polynomial.finite_setOf_isRoot hp0
  have hden : ∀ m : ℕ, (m : E) - ξ ≠ 0 := by
    intro m h
    have h1 : ξ = m := (sub_eq_zero.1 h).symm
    have h2 : σ ξ = m := by rw [h1, map_natCast]
    rw [hξ, h1] at h2
    have h3 : (m : E) = 0 := by linear_combination (-1/2 : E) * h2
    exact hξ0 (h1.trans h3)
  have hnum : ∀ m : ℕ, (m : E) + ξ ≠ 0 := by
    intro m h
    have h2 := congrArg σ h
    rw [map_add, map_natCast, hξ, map_zero, ← sub_eq_add_neg] at h2
    exact hden m h2
  let lam : ℕ → E := fun m => ((m : E) + ξ) / ((m : E) - ξ)
  have hlam : Function.Injective lam := by
    intro a b hab
    simp only [lam] at hab
    rw [div_eq_div_iff (hden a) (hden b)] at hab
    have h1 : ((a : E) - b) * (2 * ξ) = 0 := by linear_combination -hab
    rcases mul_eq_zero.1 h1 with h | h
    · exact_mod_cast sub_eq_zero.1 h
    · exact absurd h (mul_ne_zero two_ne_zero hξ0)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ¬ gv.charpoly.IsRoot (ι (lam m)) := by
    by_contra hcon
    push_neg at hcon
    exact Set.infinite_range_of_injective (hι.comp hlam) (hfin.subset (by rintro _ ⟨m, rfl⟩; exact hcon m))
  set l := lam m with hl
  have hl1 : l ≠ 1 := by
    intro h
    rw [hl, div_eq_one_iff_eq (hden m)] at h
    exact hξ0 (by linear_combination h / 2)
  have hσl : σ l = ((m : E) - ξ) / ((m : E) + ξ) := by
    simp only [hl, lam, map_div₀, map_add, map_sub, map_natCast, hξ]
    ring
  have hlσl : l * σ l = 1 := by
    rw [hσl, hl]
    simp only [lam]
    rw [div_mul_div_comm, mul_comm ((m : E) - ξ), div_self (mul_ne_zero (hnum m) (hden m))]
  set e : AF F := GlobalTheory.LatVac.liftV v (1 : Fv F v) with he
  have hee : e * e = e := by rw [he, idem_mul, evFin_liftV]
  have hev : evFin F v e = 1 := evFin_liftV v 1
  set c : AE F E := (1 - e) ⊗ₜ[F] (1 : E) + e ⊗ₜ[F] l with hc
  set c' : AE F E := (1 - e) ⊗ₜ[F] (1 : E) + e ⊗ₜ[F] σ l with hc'
  have hcc : c * c' = 1 := by
    have h1 : (1 - e) * (1 - e) = 1 - e := by linear_combination hee
    have h2 : (1 - e) * e = 0 := by linear_combination -hee
    have h3 : e * (1 - e) = 0 := by linear_combination -hee
    rw [hc, hc', add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      h1, h2, h3, hee, hlσl]
    simp only [mul_one, TensorProduct.zero_tmul, add_zero, zero_add]
    rw [← TensorProduct.add_tmul, sub_add_cancel, Algebra.TensorProduct.one_def]
  have hcA : cA σ c = c' := by
    simp [hc, hc', cA, Algebra.TensorProduct.map_tmul]
  have hcv : compFin F E v c = ι l := by
    simp [hc, compFin, Algebra.TensorProduct.map_tmul, hev, ι]
  have hc1 : c - 1 = e • ((1 : AF F) ⊗ₜ[F] (l - 1)) := by
    rw [hc, TensorProduct.smul_tmul', smul_eq_mul, mul_one, TensorProduct.tmul_sub, Algebra.TensorProduct.one_def,
      TensorProduct.sub_tmul]
    abel
  let kG : GL (Fin n) (AE F E) := ⟨Matrix.scalar (Fin n) c, Matrix.scalar (Fin n) c',
    by rw [← map_mul, hcc, map_one], by rw [← map_mul, mul_comm, hcc, map_one]⟩
  have hmem : kG ∈ UG (cA σ) (incM F J) := by
    show (Matrix.scalar (Fin n) c)ᵀ * incM F J * (Matrix.scalar (Fin n) c).map (cA σ) = incM F J
    have hT : (Matrix.scalar (Fin n) c)ᵀ = Matrix.scalar (Fin n) c := by
      simp [Matrix.scalar_apply]
    have hM : (Matrix.scalar (Fin n) c).map (cA σ) = Matrix.scalar (Fin n) c' := by
      rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), hcA]
    rw [hT, hM, (Matrix.scalar_commute c (fun r => Commute.all c r) _).eq, Matrix.mul_assoc, ← map_mul, hcc,
      map_one, Matrix.mul_one]
  let k : UA σ J := ⟨kG, hmem⟩
  have hk : mat k = Matrix.scalar (Fin n) c := rfl
  have hSv : (Matrix.scalar (Fin n) c).map (compFin F E v) = Matrix.scalar (Fin n) (ι l) := by
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map (map_zero _), hcv]

  have hAt : At (evFin F v) (mat k - 1) := by
    have : mat k - 1 = e • Matrix.scalar (Fin n) ((1 : AF F) ⊗ₜ[F] (l - 1)) := by
      rw [hk]
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.scalar_apply, hc1]
      · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    rw [this]
    exact at_idem_smul v _

  have hdeta : IsUnit ((1 - mat k).map (compFin F E v)).det := by
    rw [← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply, hk, hSv,
      ← map_one (Matrix.scalar (Fin n) : Fv F v ⊗[F] E →+* _), ← map_sub, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const]
    refine IsUnit.pow _ (hunit _ ?_)
    rw [← map_one ι, ← map_sub]
    exact (map_ne_zero_iff ι hι).2 (sub_ne_zero.2 hl1.symm)

  have hgi : mat g⁻¹ * mat g = 1 := by
    show ((↑(g⁻¹ * g) : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = 1
    rw [inv_mul_cancel]
    rfl
  set hv := (mat g⁻¹).map (compFin F E v) with hhv
  have hhg : hv * gv = 1 := by
    rw [hhv, hgv, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul, hgi, map_one]
  have hdetb : IsUnit ((1 - mat (g⁻¹ * k)).map (compFin F E v)).det := by
    have hmk : mat (g⁻¹ * k) = mat g⁻¹ * mat k := rfl
    rw [hmk, ← RingHom.mapMatrix_apply, map_sub, map_one, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      ← hhv, hk, hSv]
    have hfac : 1 - hv * Matrix.scalar (Fin n) (ι l) = hv * -(Matrix.scalar (Fin n) (ι l) - gv) := by
      rw [neg_sub, Matrix.mul_sub, hhg]
    rw [hfac, Matrix.det_mul, Matrix.det_neg, ← Matrix.eval_charpoly]
    have hd1 : hv.det * gv.det = 1 := by rw [← Matrix.det_mul, hhg, Matrix.det_one]
    exact IsUnit.mul ⟨⟨hv.det, gv.det, hd1, by rw [mul_comm]; exact hd1⟩, rfl⟩
      (IsUnit.mul (IsUnit.pow _ isUnit_one.neg) (hunit _ hm))
  obtain ⟨a, ha, ha1, ha2⟩ := exists_inv_at v (1 - mat k) hdeta
  obtain ⟨b, hb, hb1, hb2⟩ := exists_inv_at v (1 - mat (g⁻¹ * k)) hdetb
  exact ⟨k, hAt, a, b, ha, hb, ha1, ha2, hb1, hb2⟩

end GlobalTheory.InertScalarUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetAwayP
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.CentTorus
open scoped TensorProduct

namespace GlobalTheory.CentTorus.AdelicSplit

section Tmap

variable {A B L : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B] [CommRing L] [Algebra ℚ L]

def tmap (π : A →ₐ[ℚ] B) : L ⊗[ℚ] A →ₐ[ℚ] B ⊗[ℚ] L :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeRight (Algebra.TensorProduct.includeLeft.comp π)
    (fun _ _ => Commute.all _ _)

@[simp] theorem tmap_tmul (π : A →ₐ[ℚ] B) (l : L) (a : A) : tmap π (l ⊗ₜ[ℚ] a) = π a ⊗ₜ[ℚ] l := by
  simp [tmap]

end Tmap

end GlobalTheory.CentTorus.AdelicSplit

namespace GlobalTheory.CentTorus.AdelicSplit

end GlobalTheory.CentTorus.AdelicSplit

namespace GlobalTheory.CentTorus.AdelicSplit

theorem adele_split (p : ℕ) [Fact p.Prime] :
    ∃ (π₁ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] AfP p) (π₂ : FiniteAdeleRing (𝓞 ℚ) ℚ →ₐ[ℚ] ℚ_[p]),
      Continuous π₁ ∧ Continuous π₂ ∧ Function.Bijective (fun a => (π₁ a, π₂ a)) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_continuous_finiteAdele_equiv_rat_int
  obtain ⟨π, hπc, hπb⟩ := GlobalTheory.T.ratFiniteAdeles_split_awayFromPrime_padic p
  let r : FiniteAdeleRing ℤ ℚ →ₐ[ℚ] AfP p := { AfP.restr p with commutes' := fun _ => rfl }
  exact ⟨r.comp e.toAlgHom, π.comp e.toAlgHom, (GlobalTheory.T.continuous_afP_restr p).comp he, hπc.comp he, hπb.comp e.bijective⟩

end GlobalTheory.CentTorus.AdelicSplit

section Final

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

end Final
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartQuadraticPhaseEqCmThetaExp
section
open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SplitPhase

open scoped TensorProduct

theorem phase_eq : ∀ D : D7, ∃ w : 𝓞 D.host.E, w + GlobalTheory.FinWeil.sgO D w = 1 ∧
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E),
  Setup ψ θ S T cc δ r → ∀ z : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
  ψ (-symplOH S T (GlobalTheory.FinWeilO.intA D w • finPt (S := S) (T := T) rfl rfl r z) (finPt (S := S) (T := T) rfl rfl r z)) =
    Formalism.MainNotions.StandardLatticesGL3.wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) := by
  intro D
  have hsq := D.host.sqd_sq
  let b : 𝓞 D.host.E := ⟨(1 + D.host.sqrtMinusD) / 2,
    GlobalTheory.NormSum.isIntegral_half_one_add D.host.d D.host.hyp.2.2.2.1 _ hsq⟩
  have hbv : (b : D.host.E) = (1 + D.host.sqrtMinusD) / 2 := rfl
  have h2s : star (2 : D.host.E) = 2 := by
    have := star_natCast (R := D.host.E) 2
    exact_mod_cast this
  have hbs : star (b : D.host.E) = 1 - (b : D.host.E) := by
    rw [hbv, star_div₀, star_add, star_one, h2s, GlobalTheory.FockCompare.RealChart.star_sqrtMinusD]
    ring
  refine ⟨b, ?_, ?_⟩
  · apply NumberField.RingOfIntegers.ext
    show (b : D.host.E) + ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = 1
    have hc : ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = star (b : D.host.E) := by
      have e1 : ((GlobalTheory.FinWeil.sgO D b : 𝓞 D.host.E) : D.host.E) = D.host.conj (b : D.host.E) := rfl
      rw [e1]
      exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
    rw [hc, hbs]; ring
  · intro ψ θ S T cc δ r hset z
    have hr : r ≠ 0 := GlobalTheory.NormExact.IsScale.ne_zero hset.crv.1.1 hset.scale
    set X : Matrix (Fin T.rank) (Fin S.rank) D.host.E := Matrix.of fun i j => -(r⁻¹ * z i j) with hX
    have hfin : finPt (S := S) (T := T) rfl rfl r z = GlobalTheory.LatVac.finTens 1 X := by
      funext i j; rfl
    have hmap : GlobalTheory.FinWeilO.intA D b • GlobalTheory.LatVac.finTens 1 X =
        GlobalTheory.LatVac.finTens 1 (Matrix.of fun i j => (b : D.host.E) * X i j) := by
      funext i j
      show ((1 : AF D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) * (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (X i j)) =
        pairA D.host.F 0 1 ⊗ₜ[D.host.F] ((b : D.host.E) * X i j)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    set n : D.host.E := ∑ c, ∑ a, star (X c a) * X c a with hn
    have hns : star n = n := by
      rw [hn, star_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [star_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [star_mul', star_star, mul_comm]
    have hR : GlobalTheory.LatVac.hRat S T X X = n := by
      rw [GlobalTheory.LatVac.hRat, hset.gS, hset.gT, inv_one]
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      have e : ∀ x, (∑ x_1, ∑ x_2, if x = x_1 then star (X x_2 x_1) * X x_2 x else 0) =
          ∑ x_2, star (X x_2 x) * X x_2 x := fun x => by
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_comm]
    have hs : symplOH S T (GlobalTheory.FinWeilO.intA D b • finPt (S := S) (T := T) rfl rfl r z)
        (finPt (S := S) (T := T) rfl rfl r z) = pairA D.host.F 0
        (algebraMap D.host.F (Af D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)))) := by
      rw [hfin, hmap, symplOH, GlobalTheory.LatVac.symplO_finTens, GlobalTheory.ThetaSignLat.hRat_smul_left, hR]
      refine Prod.ext (mul_zero _) ?_
      show algebraMap D.host.F (Af D.host.F) (1 / 2) * (1 * 1 * _) = _
      rw [one_mul, one_mul, ← RingHom.map_mul]
      rfl
    have hq := GlobalTheory.ThetaSignLat.trace_val n (b : D.host.E) hns hbv
    set q : D.host.F := 1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * ((b : D.host.E) * n)) with hqdef
    have hneg : -(pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) =
        pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (-q)) := by
      refine Prod.ext ?_ ?_
      · show -(0 : Ainf D.host.F) = 0
        exact neg_zero
      · show -(algebraMap D.host.F (Af D.host.F) q) = _
        rw [map_neg]
        rfl
    rw [hs, hneg, GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap ψ hset.std]
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ∑ τ, tauE D τ n := ⟨_, rfl⟩
    obtain ⟨hxi, hN1, hd1⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_facts D
    have hNR : (Ideal.absNorm D.host.ccK : ℝ) ≠ 0 := by linarith
    have hNC : (Ideal.absNorm D.host.ccK : ℂ) ≠ 0 := by exact_mod_cast hNR
    have hdR : Real.sqrt D.host.d ≠ 0 := by linarith
    have hsumq : ∑ τ, tauE D τ ((-q : D.host.F) : D.host.E) = c / (2 * (Ideal.absNorm D.host.ccK : ℂ)) := by
      have e : ∀ τ, tauE D τ ((-q : D.host.F) : D.host.E) = tauE D τ n / (2 * (Ideal.absNorm D.host.ccK : ℂ)) :=
        fun τ => by
          rw [show ((-q : D.host.F) : D.host.E) = -((q : D.host.F) : D.host.E) from rfl, hq, neg_div, neg_neg,
            map_div₀, map_mul, map_natCast, map_ofNat]
      rw [Finset.sum_congr rfl fun τ _ => e τ, ← Finset.sum_div, hc]
    have hcre : ((c.re : ℝ) : ℂ) = c := by
      have : starRingEnd ℂ c = c := by
        rw [hc, map_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [← GlobalTheory.FockCompare.tauE_star, hns]
      exact Complex.conj_eq_iff_re.1 this
    set Z : VC D S.rank T.rank := fun τ i j => -(embT D τ (X i j)) with hZ
    have hpt : pt D (tor0 D cc δ) δ z = fun τ i j => δ * embT D τ r * Z τ i j := by
      funext τ i j
      have ez : z i j = r * -(X i j) := by
        rw [hX, Matrix.of_apply]
        field_simp
      show δ * embT D τ (z i j) = δ * embT D τ r * -(embT D τ (X i j))
      rw [ez, map_mul, map_neg]
      ring
    have hsum : ∑ τ, ∑ i, ∑ j, Z τ i j * starRingEnd ℂ (Z τ i j) = c := by
      rw [hc]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [hn, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, GlobalTheory.FockCompare.tauE_star, hZ]
      show -(tauE D τ (X i j)) * starRingEnd ℂ (-(tauE D τ (X i j))) = _
      rw [map_neg]
      ring
    rw [Formalism.MainNotions.StandardLatticesGL3.wdPh, Formalism.MainNotions.TaylorLogMetric.qH, hpt, GlobalTheory.NormExact.Hf_scale hset.crv hset.scale, hsum, Formalism.MainNotions.StandardLatticesGL3.ee,
      hsumq]
    have hre : Real.sqrt D.host.d / 2 * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c).re / 2 =
        c.re / (2 * Ideal.absNorm D.host.ccK) := by
      rw [show (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c) = ((2 * Formalism.L2.Pj.xiR D : ℝ) : ℂ) * c by push_cast; ring,
        Complex.re_ofReal_mul, hxi]
      field_simp
    rw [hre]
    congr 1
    push_cast
    rw [hcre]
end GlobalTheory.SplitPhase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorMinorProductOriginEqPeriodsJetStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVector_minorProduct_origin_eq_periods_jet : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Differentiable ℂ G → Reads ψ θ hS hT cc δ r G f → ∀ (n : D.what₂.Tau → ℕ) (t : Tup D a d n),
    pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f
        (MvPolynomial.rename (fun k : Formalism.MainNotions.GL3Theta.Idx D a d => ((k.1, Fin.cast hT.symm k.2.1, Fin.cast hS.symm k.2.2) : FVar D T.rank S.rank))
          (minorPol D t)) 0 =
      (∏ τ, period D δ r τ ^ (a * n τ)) * Formalism.MainNotions.GL3Theta.applyAt0 D (minorPol D t) G := by
  first | exact @GlobalTheory.NormExact.fock_minorPol_zero | exact GlobalTheory.NormExact.fock_minorPol_zero | (intros; apply GlobalTheory.NormExact.fock_minorPol_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardRationalMemUnitaryRationalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameConj_standardRational_mem_unitaryRational : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ γ ∈ GlobalTheory.NormSum.ratG D V.rank, ∃ q ∈ ratFin V, finG V q = GlobalTheory.FrameTransport.frConj fr γ.1 := by
  first | exact @GlobalTheory.FrameTransport.frConj_ratG | exact GlobalTheory.FrameTransport.frConj_ratG | (intros; apply GlobalTheory.FrameTransport.frConj_ratG <;> assumption)
end

