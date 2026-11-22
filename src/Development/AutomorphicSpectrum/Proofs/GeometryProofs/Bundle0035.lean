import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
import ReciprocityTheory.SemistableReduction.Bundle0023
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalIndexFrameLogNorm
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet

section Index

variable {W : Type} [AddCommGroup W]

theorem relIndex_pair (Λ : AddSubgroup W) (M a : W →+ W) (hM : Function.Injective M)
    (hc : ∀ x, a (M x) = M (a x)) (h2 : Λ.map a ≤ Λ) (i2 : (Λ.map a).relIndex Λ ≠ 0)
    (h3 : Λ.map (a.comp M) ≤ Λ) (i3 : (Λ.map (a.comp M)).relIndex Λ ≠ 0) :
    Λ.relIndex (Λ.map M) ≠ 0 ∧ (Λ.map M).relIndex Λ ≠ 0 := by
  have e3 : Λ.map (a.comp M) = (Λ.map a).map M := by
    rw [AddSubgroup.map_map]
    congr 1
    ext x
    exact hc x
  have l1 : Λ.map (a.comp M) ≤ Λ.map M := by rw [e3]; exact AddSubgroup.map_mono h2
  have n1 : (Λ.map (a.comp M)).relIndex (Λ.map M) ≠ 0 := by
    rw [e3, AddSubgroup.relIndex_map_map_of_injective _ _ hM]; exact i2
  have o1 : (Λ.map M).relIndex (Λ.map (a.comp M)) ≠ 0 := by
    rw [AddSubgroup.relIndex_eq_one.2 l1]; exact one_ne_zero
  have o3 : Λ.relIndex (Λ.map (a.comp M)) ≠ 0 := by
    rw [AddSubgroup.relIndex_eq_one.2 h3]; exact one_ne_zero
  exact ⟨AddSubgroup.relIndex_ne_zero_trans o3 n1, AddSubgroup.relIndex_ne_zero_trans o1 i3⟩

end Index

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

noncomputable def mulVecHom (T : Matrix (Fin n) (Fin n) L) : (Fin n → L) →+ (Fin n → L) :=
  AddMonoidHom.mk' (fun x => T *ᵥ x) (Matrix.mulVec_add T)

theorem mulVecHom_apply (T : Matrix (Fin n) (Fin n) L) (x : Fin n → L) : mulVecHom T x = T *ᵥ x := rfl

theorem frame_eq_map (T : Matrix (Fin n) (Fin n) L) :
    (frame T).toAddSubgroup = (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.map (mulVecHom T) := by
  ext x
  rw [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, mem_frame]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, (Submodule.mem_toAddSubgroup _).2 (mem_frame.2 ⟨z, by simp⟩), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := mem_frame.1 ((Submodule.mem_toAddSubgroup _).1 hy)
    exact ⟨z, by simp [mulVecHom_apply]⟩

theorem frame_map_le (D : Matrix (Fin n) (Fin n) (𝓞 L)) :
    frame (D.map (algebraMap (𝓞 L) L)) ≤ frame (1 : Matrix (Fin n) (Fin n) L) := by
  rw [frame, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact mem_frame_one.2 fun i => ⟨D i k, rfl⟩

theorem log_abs_norm (x : 𝓞 L) (hx : x ≠ 0) :
    Real.log ((|Algebra.norm ℤ x| : ℤ) : ℝ) = ∑ σ : L →+* ℂ, Real.log ‖σ (algebraMap (𝓞 L) L x)‖ := by
  have hx' : algebraMap (𝓞 L) L x ≠ 0 := by simpa using hx
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.2 ((map_ne_zero σ).2 hx'))]
  congr 1
  have h1 : ∏ σ : L →+* ℂ, σ (algebraMap (𝓞 L) L x) =
      algebraMap ℚ ℂ (Algebra.norm ℚ (algebraMap (𝓞 L) L x)) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ (algebraMap (𝓞 L) L x)]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _
      (fun σ => by simp [RingHom.equivRatAlgHom_apply])
  rw [← norm_prod, h1, ← Algebra.coe_norm_int x]
  simp

theorem relIndex_frame (D : Matrix (Fin n) (Fin n) (𝓞 L)) (hD : D.det ≠ 0) :
    (((frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup.relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup : ℕ) : ℤ) = |Algebra.norm ℤ D.det| := by
  have hb : LinearIndependent L (fun k j => (1 : Matrix (Fin n) (Fin n) L) j k) := by
    have e : (fun k j => (1 : Matrix (Fin n) (Fin n) L) j k) = ⇑(Pi.basisFun L (Fin n)) := by
      funext k j
      simp [Matrix.one_apply, Pi.single_apply]
    rw [e]
    exact (Pi.basisFun L (Fin n)).linearIndependent
  have h := ReciprocityTheory.MultiplicativeHeights.relIndex_span_comb _ hb D hD
  have e : frame (D.map (algebraMap (𝓞 L) L)) = Submodule.span (𝓞 L)
      (Set.range fun j => ∑ i, D i j • fun l => (1 : Matrix (Fin n) (Fin n) L) l i) := by
    rw [frame]
    congr 2
    funext k j
    simp [Finset.sum_apply, Matrix.one_apply, Algebra.smul_def]
  rw [e]
  exact h

theorem relIndex_frame_ne (D : Matrix (Fin n) (Fin n) (𝓞 L)) (hD : D.det ≠ 0) :
    (frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup.relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 := by
  intro h
  have h1 := relIndex_frame D hD
  rw [h, Nat.cast_zero, eq_comm, abs_eq_zero, Algebra.norm_eq_zero_iff] at h1
  exact hD h1

theorem log_relIndex_frame (D : Matrix (Fin n) (Fin n) (𝓞 L)) (hD : D.det ≠ 0) :
    Real.log (((frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup.relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup : ℕ) : ℝ) =
      ∑ σ : L →+* ℂ, Real.log ‖σ (algebraMap (𝓞 L) L D.det)‖ := by
  rw [← log_abs_norm _ hD, ← relIndex_frame D hD]
  simp

theorem exists_int_matrix (C : Matrix (Fin n) (Fin n) L) :
    ∃ (d : 𝓞 L) (D : Matrix (Fin n) (Fin n) (𝓞 L)), d ≠ 0 ∧
      D.map (algebraMap (𝓞 L) L) = algebraMap (𝓞 L) L d • C := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 L))
    (fun p : Fin n × Fin n => C p.1 p.2)
  choose D hD using hb
  refine ⟨b, Matrix.of fun i j => D (i, j), nonZeroDivisors.ne_zero b.2, ?_⟩
  ext i j
  simpa [Algebra.smul_def] using hD (i, j)

theorem coe_det (D : Matrix (Fin n) (Fin n) (𝓞 L)) :
    algebraMap (𝓞 L) L D.det = (D.map (algebraMap (𝓞 L) L)).det := by
  rw [RingHom.map_det]
  rfl

theorem gIdx_frame : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (C : Matrix (Fin n) (Fin n) L),
    C.det ≠ 0 →
    (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.relIndex (frame C).toAddSubgroup ≠ 0 ∧
    (frame C).toAddSubgroup.relIndex (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 ∧
    gIdx (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup (frame C).toAddSubgroup =
      ∑ σ : L →+* ℂ, Real.log ‖σ C.det‖ := by
  intro L _ _ n C hC
  obtain ⟨d, D, hd, hDC⟩ := exists_int_matrix C
  have hδ : algebraMap (𝓞 L) L d ≠ 0 := by simpa using hd
  obtain ⟨δ, hδe⟩ : ∃ δ, δ = algebraMap (𝓞 L) L d := ⟨_, rfl⟩
  rw [← hδe] at hDC hδ
  obtain ⟨S, hSe⟩ : ∃ S : Matrix (Fin n) (Fin n) (𝓞 L), S = d • 1 := ⟨_, rfl⟩
  have hS : S.map (algebraMap (𝓞 L) L) = δ • 1 := by
    ext i j
    by_cases h : i = j <;> simp [hSe, hδe, Matrix.smul_apply, Matrix.one_apply, h]
  have hSdet : S.det = d ^ n := by simp [hSe, Matrix.det_smul]
  have hDdet : algebraMap (𝓞 L) L D.det = δ ^ n * C.det := by
    rw [coe_det, hDC, Matrix.det_smul, Fintype.card_fin]
  have hS0 : S.det ≠ 0 := by rw [hSdet]; exact pow_ne_zero _ hd
  have hD0 : D.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hDdet
    exact mul_ne_zero (pow_ne_zero _ hδ) hC hDdet.symm
  set Λ := (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup with hΛ
  have ea : Λ.map (mulVecHom (δ • 1)) = (frame (S.map (algebraMap (𝓞 L) L))).toAddSubgroup := by
    rw [hS, frame_eq_map]
  have eM : (mulVecHom (δ • 1)).comp (mulVecHom C) = mulVecHom (D.map (algebraMap (𝓞 L) L)) := by
    refine AddMonoidHom.ext fun x => ?_
    simp [mulVecHom_apply, hDC, Matrix.smul_mulVec]
  have eaM : Λ.map ((mulVecHom (δ • 1)).comp (mulVecHom C)) =
      (frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup := by
    rw [eM, frame_eq_map]
  have hc : ∀ x, mulVecHom (δ • 1) (mulVecHom C x) = mulVecHom C (mulVecHom (δ • 1) x) := by
    intro x
    simp [mulVecHom_apply, Matrix.smul_mulVec, Matrix.mulVec_smul]
  have hinj : Function.Injective (mulVecHom C) :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det C).2 (IsUnit.mk0 _ hC))
  have h2 : Λ.map (mulVecHom (δ • 1)) ≤ Λ := by
    rw [ea]; exact fun x hx => frame_map_le S hx
  have i2 : (Λ.map (mulVecHom (δ • 1))).relIndex Λ ≠ 0 := by
    rw [ea]; exact relIndex_frame_ne S hS0
  have h3 : Λ.map ((mulVecHom (δ • 1)).comp (mulVecHom C)) ≤ Λ := by
    rw [eaM]; exact fun x hx => frame_map_le D hx
  have i3 : (Λ.map ((mulVecHom (δ • 1)).comp (mulVecHom C))).relIndex Λ ≠ 0 := by
    rw [eaM]; exact relIndex_frame_ne D hD0
  obtain ⟨p1, p2⟩ := relIndex_pair Λ _ _ hinj hc h2 i2 h3 i3
  have hf := GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_frac Λ _ _ hinj hc h2 i2 h3 i3
  rw [ea, eaM, log_relIndex_frame S hS0, log_relIndex_frame D hD0] at hf
  have eC : (frame C).toAddSubgroup = Λ.map (mulVecHom C) := frame_eq_map C
  refine ⟨by rw [eC]; exact p1, by rw [eC]; exact p2, ?_⟩
  rw [eC, gIdx_swap, hf]
  have hsum : ∀ σ : L →+* ℂ, Real.log ‖σ (algebraMap (𝓞 L) L D.det)‖ =
      Real.log ‖σ (algebraMap (𝓞 L) L S.det)‖ + Real.log ‖σ C.det‖ := by
    intro σ
    have a1 : ‖σ (algebraMap (𝓞 L) L S.det)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero, hSdet, map_pow, ← hδe]
      exact pow_ne_zero _ hδ
    have a2 : ‖σ C.det‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero]; exact hC
    rw [← Real.log_mul a1 a2, ← norm_mul, ← map_mul, hDdet, hSdet, map_pow, ← hδe]
  simp_rw [hsum]
  rw [Finset.sum_add_distrib]
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateFunctionalUnique
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.HT

private lemma valAt_sub' {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt y U h (a - b) = valAt y U h a - valAt y U h b := by
  simp [valAt, map_sub]

private lemma exists_dual_of_dvd {R : Type} [CommRing R] [IsDomain R] {L : Type} [AddCommGroup L]
    [Module R L] (c : R) (hc : c ≠ 0) (d : Module.Dual R L) (h : ∀ e, c ∣ d e) :
    ∃ u : Module.Dual R L, d = c • u := by
  choose f hf using h
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply mul_left_cancel₀ hc
    rw [mul_add, ← hf, ← hf, ← hf, map_add]
  · intro r x
    apply mul_left_cancel₀ hc
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← hf, map_smul, smul_eq_mul, hf x]
    ring
  · ext e
    show d e = c • f e
    rw [hf e, smul_eq_mul]

theorem isHT_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → (N : R) ≠ 0 → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → (Γ.IsHT i M N χ w' ↔ ∃ u : Module.Dual R L, w' = w + N • u) := by
  intro R _ _ T _ _ Γ S G _ _ x N i hT hsm hN L _ _ M χ w w' hw
  obtain ⟨s, hs, hsv⟩ := hw
  constructor
  · rintro ⟨s', hs', hsv'⟩
    have hss : s' = s := by
      have h0 := GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤ (s' - s) (fun t h => by
        rw [valAt_sub', hs' t, hs t, sub_self])
      exact sub_eq_zero.mp h0
    subst hss
    have hdvd : ∀ e, (N : R) ∣ w' e - w e := by
      intro e
      obtain ⟨v, hv1, hv2, hv3⟩ := hsv e
      obtain ⟨v', hv1', hv2', hv3'⟩ := hsv' e
      have hvv : v' = v := (GlobalTheory.T.existsUnique_tangent_dual_number R T Γ S G x N i hT L M e).unique ⟨hv1', hv2'⟩ ⟨hv1, hv2⟩
      subst hvv
      rw [hv3] at hv3'
      have h1 : Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e) = Ideal.Quotient.mk (Ideal.span {(N : R)}) (w' e) := by
        simpa using congrArg TrivSqZeroExt.snd hv3'
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
      exact h1.symm
    obtain ⟨u, hu⟩ := exists_dual_of_dvd (N : R) hN (w' - w) (fun e => by simpa using hdvd e)
    refine ⟨u, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul R, ← hu]
    abel
  · rintro ⟨u, rfl⟩
    refine ⟨s, hs, fun e => ?_⟩
    obtain ⟨v, hv1, hv2, hv3⟩ := hsv e
    refine ⟨v, hv1, hv2, ?_⟩
    have h0 : Ideal.Quotient.mk (Ideal.span {(N : R)}) ((N • u) e) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, ← Nat.cast_smul_eq_nsmul R,
        LinearMap.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    rw [hv3, LinearMap.add_apply, map_add, h0, add_zero]

end GlobalTheory.CompanionTheory.Ar.BT.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralClosureChartSpan
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace GlobalTheory.CompanionTheory.Ar.IntClGens

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} (x : κ → Ω)

theorem twist_mem {c j : κ} (hc : x c ≠ 0) {b : Ω} (hb : b ∈ chRing o x c) :
    ∃ e : ℕ, ∀ m, e ≤ m → (x c / x j) ^ m * b ∈ chRing o x j := by
  have ht : x c / x j ∈ chRing o x j := Algebra.subset_adjoin ⟨c, rfl⟩
  induction hb using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨l, rfl⟩ := hy
    refine ⟨1, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have key : x c / x j * (x l / x c) = x l / x j := by
      rw [div_mul_div_comm, mul_comm (x j), mul_div_mul_left _ _ hc]
    have : (x c / x j) ^ (1 + k) * (x l / x c) = (x c / x j) ^ k * (x l / x j) := by
      rw [← key]; ring
    rw [this]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ht _) (Algebra.subset_adjoin ⟨l, rfl⟩)
  | algebraMap r =>
    exact ⟨0, fun m _ => Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ht _) (Subalgebra.algebraMap_mem _ r)⟩
  | add y z _ _ hy hz =>
    obtain ⟨e1, h1⟩ := hy
    obtain ⟨e2, h2⟩ := hz
    exact ⟨max e1 e2, fun m hm => by
      rw [mul_add]
      exact Subalgebra.add_mem _ (h1 m (le_of_max_le_left hm)) (h2 m (le_of_max_le_right hm))⟩
  | mul y z _ _ hy hz =>
    obtain ⟨e1, h1⟩ := hy
    obtain ⟨e2, h2⟩ := hz
    refine ⟨e1 + e2, fun m hm => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    have : (x c / x j) ^ (e1 + e2 + k) * (y * z) =
        ((x c / x j) ^ (e1 + k) * y) * ((x c / x j) ^ e2 * z) := by ring
    rw [this]
    exact Subalgebra.mul_mem _ (h1 _ (by omega)) (h2 _ le_rfl)

theorem twist_integral {c j : κ} (hc : x c ≠ 0) {a : Ω} (ha : IsIntegral (chRing o x c) a) :
    ∃ e : ℕ, ∀ m, e ≤ m → IsIntegral (chRing o x j) ((x c / x j) ^ m * a) := by
  have ht : x c / x j ∈ chRing o x j := Algebra.subset_adjoin ⟨c, rfl⟩
  obtain ⟨p, hmon, hp⟩ := ha
  have hE : ∀ i, ∃ e : ℕ, ∀ m, e ≤ m → (x c / x j) ^ m * (p.coeff i : Ω) ∈ chRing o x j :=
    fun i => twist_mem x hc (p.coeff i).2
  choose E hE using hE
  obtain ⟨E0, hE0⟩ : ∃ E0, ∀ i ≤ p.natDegree, E i ≤ E0 :=
    ⟨(Finset.range (p.natDegree + 1)).sup E, fun i hi => Finset.le_sup (Finset.mem_range.2 (by omega))⟩
  have hn' : (p.map (algebraMap (chRing o x c) Ω)).natDegree = p.natDegree := hmon.natDegree_map _
  have hqm : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).Monic :=
    (Polynomial.monic_scaleRoots_iff _).2 (hmon.map _)
  have hq0 : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).eval
      ((x c / x j) ^ E0 * a) = 0 := by
    have h1 : (p.map (algebraMap (chRing o x c) Ω)).eval₂ (RingHom.id Ω) a = 0 := by
      rw [Polynomial.eval₂_map, RingHom.id_comp]; exact hp
    have := Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id Ω) (s := (x c / x j) ^ E0) h1
    simpa [Polynomial.eval₂_id] using this
  have hlift : (p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0) ∈
      Polynomial.lifts (algebraMap (chRing o x j) Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    have hmem : ((p.map (algebraMap (chRing o x c) Ω)).scaleRoots ((x c / x j) ^ E0)).coeff i ∈
        chRing o x j := by
      rw [Polynomial.coeff_scaleRoots, hn', Polynomial.coeff_map]
      rcases lt_trichotomy i p.natDegree with hi | hi | hi
      · have h1 : E i ≤ E0 := hE0 i hi.le
        have h2 : 1 ≤ p.natDegree - i := by omega
        have hle : E i ≤ E0 * (p.natDegree - i) :=
          calc E i ≤ E0 := h1
            _ = E0 * 1 := (mul_one _).symm
            _ ≤ E0 * (p.natDegree - i) := Nat.mul_le_mul_left _ h2
        rw [← pow_mul, mul_comm]
        exact hE i _ hle
      · rw [hi, Nat.sub_self, pow_zero, mul_one, hmon.coeff_natDegree, map_one]
        exact Subalgebra.one_mem _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, map_zero, zero_mul]
        exact Subalgebra.zero_mem _
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨q0, hq0map, -, hq0m⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hqm
  have hint : IsIntegral (chRing o x j) ((x c / x j) ^ E0 * a) :=
    ⟨q0, hq0m, by rw [← Polynomial.eval_map, hq0map]; exact hq0⟩
  refine ⟨E0, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have : (x c / x j) ^ (E0 + k) * a = (x c / x j) ^ k * ((x c / x j) ^ E0 * a) := by ring
  rw [this]
  have htk : IsIntegral (chRing o x j) ((x c / x j) ^ k) :=
    isIntegral_algebraMap (x := (⟨_, Subalgebra.pow_mem _ ht k⟩ : chRing o x j))
  exact htk.mul hint

theorem exists_twisted_gens : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ]
    (x : κ → Ω), (∀ c, x c ≠ 0 → Module.Finite (chRing o x c) (integralClosure (chRing o x c) Ω)) →
    ∃ (d n : ℕ) (z : κ ⊕ Fin n → Ω), (∀ c, z (Sum.inl c) = x c ^ d) ∧ ∀ c, x c ≠ 0 → ∀ a : Ω,
      IsIntegral (chRing o x c) a ↔ a ∈ Submodule.span (chRing o x c) (Set.range fun k => z k / x c ^ d) := by
  intro o _ Ω _ _ κ _ x hfin
  have hgen : ∀ c, ∃ (N : ℕ) (g : Fin N → Ω), (∀ k, x c ≠ 0 ∧ IsIntegral (chRing o x c) (g k)) ∧
      (x c ≠ 0 → ∀ a, IsIntegral (chRing o x c) a → a ∈ Submodule.span (chRing o x c) (Set.range g)) := by
    intro c
    by_cases hc : x c = 0
    · exact ⟨0, Fin.elim0, fun k => k.elim0, fun h => absurd hc h⟩
    · haveI := hfin c hc
      obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin (R := chRing o x c) (M := integralClosure (chRing o x c) Ω)
      refine ⟨N, fun k => ((s k : integralClosure (chRing o x c) Ω) : Ω),
        fun k => ⟨hc, (s k).2⟩, fun _ a ha => ?_⟩
      have hle : Submodule.map (integralClosure (chRing o x c) Ω).val.toLinearMap
          (Submodule.span (chRing o x c) (Set.range s)) ≤
          Submodule.span (chRing o x c) (Set.range fun k => ((s k : integralClosure (chRing o x c) Ω) : Ω)) := by
        rw [Submodule.map_span_le]
        rintro _ ⟨k, rfl⟩
        exact Submodule.subset_span ⟨k, rfl⟩
      rw [hs] at hle
      exact hle (Submodule.mem_map_of_mem (p := ⊤) (f := (integralClosure (chRing o x c) Ω).val.toLinearMap)
        (r := ⟨a, ha⟩) Submodule.mem_top)
  choose N g hg using hgen
  obtain ⟨M, ⟨eI⟩⟩ := Finite.exists_equiv_fin (Σ c, Fin (N c))
  have hD : ∀ (i : Σ c, Fin (N c)) (j : κ), ∃ e : ℕ, ∀ m, e ≤ m →
      IsIntegral (chRing o x j) ((x i.1 / x j) ^ m * g i.1 i.2) :=
    fun i j => twist_integral x ((hg i.1).1 i.2).1 ((hg i.1).1 i.2).2
  choose D hD using hD
  obtain ⟨d, hd⟩ := Finite.exists_le (fun q : (Σ c, Fin (N c)) × κ => D q.1 q.2)
  refine ⟨d, M, Sum.elim (fun c => x c ^ d) (fun k => x (eI.symm k).1 ^ d * g (eI.symm k).1 (eI.symm k).2),
    fun c => rfl, fun c hc a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · refine Submodule.span_mono ?_ ((hg c).2 hc a ha)
    rintro _ ⟨k, rfl⟩
    refine ⟨Sum.inr (eI ⟨c, k⟩), ?_⟩
    have he : eI.symm (eI ⟨c, k⟩) = ⟨c, k⟩ := eI.symm_apply_apply _
    simp only [Sum.elim_inr]
    rw [he]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hc)
  · have hsub : (Set.range fun k => (Sum.elim (fun c => x c ^ d)
        (fun k => x (eI.symm k).1 ^ d * g (eI.symm k).1 (eI.symm k).2) k : Ω) / x c ^ d) ⊆
        ((integralClosure (chRing o x c) Ω).toSubmodule : Set Ω) := by
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
      rcases k with j | k
      · simp only [Sum.elim_inl]
        rw [← div_pow]
        exact isIntegral_algebraMap (x := (⟨_, Subalgebra.pow_mem _
          (Algebra.subset_adjoin ⟨j, rfl⟩ : x j / x c ∈ chRing o x c) d⟩ : chRing o x c))
      · simp only [Sum.elim_inr]
        rw [mul_div_right_comm, ← div_pow]
        exact hD (eI.symm k) c d (hd (eI.symm k, c))
    have := Submodule.span_le.2 hsub ha
    rwa [Subalgebra.mem_toSubmodule, mem_integralClosure_iff] at this

end GlobalTheory.CompanionTheory.Ar.IntClGens
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFinite
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem mem_of_finite_of_closedFibre {R : Type} [CommRing R] [IsLocalRing R]
    {X : Over (Spec (CommRingCat.of R))} (W : X.left.Opens)
    (hW : ∀ x : X.left, X.hom x = IsLocalRing.closedPoint R → x ∈ W)
    (Y : Over (Spec (CommRingCat.of R))) (hY : IsFinite Y.hom) (h : Y ⟶ X) (z : Y.left) :
    h.left z ∈ W := by
  haveI := hY
  haveI : IsIso (⊤ : Y.left.Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  have hfin : IsFinite ((⊤ : Y.left.Opens).ι ≫ Y.hom) := inferInstance
  have hle := GlobalTheory.T.finite_open_le_closed_fibre R Y.left Y.hom ⊤ (h.left ⁻¹ᵁ W) hfin (fun x hx => by
    apply hW
    have hw : h.left ≫ X.hom = Y.hom := Over.w h
    have hc := Scheme.Hom.comp_apply h.left X.hom x
    rw [hw] at hc
    rw [← hc]
    exact hx)
  exact hle (show z ∈ (⊤ : Y.left.Opens) from trivial)

abbrev openOver {S : Scheme.{0}} (X : Over S) (U : X.left.Opens) : Over S := Over.mk (U.ι ≫ X.hom)

abbrev openIncl {S : Scheme.{0}} (X : Over S) (U : X.left.Opens) : openOver X U ⟶ X := Over.homMk U.ι rfl

theorem exists_factor_openIncl {S : Scheme.{0}} {X Y : Over S} (U : X.left.Opens) (x : Y ⟶ X)
    (hx : ∀ z, x.left z ∈ U) : ∃ x' : Y ⟶ openOver X U, x' ≫ openIncl X U = x := by
  have hr : Set.range x.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    exact hx z
  have hc : IsOpenImmersion.lift U.ι x.left hr ≫ U.ι = x.left := IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk (IsOpenImmersion.lift U.ι x.left hr) ?_, ?_⟩
  · simp only [Over.mk_hom]
    rw [← Category.assoc, hc]
    exact Over.w x
  · ext1
    exact hc

theorem QFGroup.isFinOpenSub_of_closedFibre :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (T : Type) [CommGroup T] (Γ : QFGroup R T)
      (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) →
      (∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) → Γ.IsFinOpenSub U := by
  intro R _ _ _ T _ Γ U hfin hU
  haveI := hfin
  have hV : IsFinite (openOver Γ.G U).hom := hfin
  haveI := hV
  refine ⟨hfin, ?_, ?_, ?_⟩
  · intro x
    refine mem_of_finite_of_closedFibre U hU (𝟙_ _) ?_ η[Γ.G] x
    show IsFinite (𝟙 _)
    infer_instance
  · intro S x y hx hy z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    obtain ⟨y', rfl⟩ := exists_factor_openIncl U y hy
    have hP : IsFinite (openOver Γ.G U ⊗ openOver Γ.G U).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    have key := mem_of_finite_of_closedFibre U hU _ hP
      ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U))
    have heq : x' ≫ openIncl Γ.G U * y' ≫ openIncl Γ.G U =
        lift x' y' ≫ ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U)) := by
      rw [comp_mul]
      simp
    rw [heq]
    simpa using key ((lift x' y').left z)
  · intro S x hx z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    have key := mem_of_finite_of_closedFibre U hU _ hV (openIncl Γ.G U)⁻¹
    have heq : (x' ≫ openIncl Γ.G U)⁻¹ = x' ≫ (openIncl Γ.G U)⁻¹ := by
      simp [Hom.inv_def]
    rw [heq]
    simpa using key (x'.left z)

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalExtensionProjectiveModuleStatement
section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_extension_projective_module : ∀ (L : Type) [Field L] [NumberField L] (B : Type) [AddCommGroup B] [Module (𝓞 L) B] [Module.Finite (𝓞 L) B] [Module.Projective (𝓞 L) B] (I : Ideal (𝓞 L)), I ≠ ⊥ → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (y : 𝓞 L'), I.map (algebraMap (𝓞 L) (𝓞 L')) = Ideal.span {y} ∧ ∀ (B' : Type) [AddCommGroup B'] [Module (𝓞 L') B'] [Module.Finite (𝓞 L') B'] [Module.Projective (𝓞 L') B'] (io : B →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] B'), Submodule.span (𝓞 L') (Set.range io) = ⊤ → Module.finrank (𝓞 L') B' = Module.finrank (𝓞 L) B → ∃ e : Fin (Module.finrank (𝓞 L') B') → B', LinearIndependent (𝓞 L') e ∧ Submodule.span (𝓞 L') (Set.range e) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension | exact GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension | (intros; apply GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension <;> assumption)
end

