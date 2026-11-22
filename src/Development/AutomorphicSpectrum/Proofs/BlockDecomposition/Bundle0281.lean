import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorFieldOrSplitIdempotent
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SaGen.Dichotomy

section Core

variable {K R : Type} [Field K] [CommRing R] [Algebra K R]

theorem core (s : R →+* R) (T : R) (D : K) (hT : T * T = algebraMap K R D) (hD : D ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsK : ∀ x, s (algebraMap K R x) = algebraMap K R x) (hsT : s T = -T)
    (hspan : ∀ z : R, ∃ x y : K, z = algebraMap K R x + algebraMap K R y * T)
    (hind : ∀ x y : K, algebraMap K R x + algebraMap K R y * T = 0 → x = 0 ∧ y = 0) :
    IsField R ∨ ∃ e : R, e * e = e ∧ e + s e = 1 ∧ e * s e = 0 := by
  by_cases hsq : ∃ t : K, t * t = D
  · obtain ⟨t, ht⟩ := hsq
    have ht0 : t ≠ 0 := by
      rintro rfl
      exact hD (by rw [← ht, mul_zero])
    right
    have hw : (algebraMap K R t⁻¹ * T) * (algebraMap K R t⁻¹ * T) = 1 := by
      calc (algebraMap K R t⁻¹ * T) * (algebraMap K R t⁻¹ * T)
          = algebraMap K R t⁻¹ * algebraMap K R t⁻¹ * (T * T) := by ring
        _ = algebraMap K R (t⁻¹ * t⁻¹ * D) := by rw [hT, map_mul, map_mul]
        _ = 1 := by
          have : t⁻¹ * t⁻¹ * D = 1 := by
            rw [← ht]
            field_simp
          rw [this, map_one]
    have hh : algebraMap K R 2⁻¹ * 2 = 1 := by
      have h : algebraMap K R 2 = 2 := map_ofNat _ 2
      rw [← h, ← map_mul, inv_mul_cancel₀ h2, map_one]
    have hs : s (algebraMap K R 2⁻¹ * (1 + algebraMap K R t⁻¹ * T)) =
        algebraMap K R 2⁻¹ * (1 - algebraMap K R t⁻¹ * T) := by
      rw [map_mul, map_add, map_mul, hsK, hsK, hsT, map_one]
      ring
    refine ⟨algebraMap K R 2⁻¹ * (1 + algebraMap K R t⁻¹ * T), ?_, ?_, ?_⟩
    · generalize algebraMap K R t⁻¹ * T = w at hw
      generalize algebraMap K R 2⁻¹ = h at hh
      linear_combination h ^ 2 * hw + h * (1 + w) * hh
    · rw [hs]
      generalize algebraMap K R t⁻¹ * T = w
      generalize algebraMap K R 2⁻¹ = h at hh
      linear_combination hh
    · rw [hs]
      generalize algebraMap K R t⁻¹ * T = w at hw
      generalize algebraMap K R 2⁻¹ = h at hh
      linear_combination (-h ^ 2) * hw
  · left
    have h10 : (1 : R) ≠ 0 := fun h =>
      one_ne_zero (hind 1 0 (by rw [map_one, map_zero, zero_mul, add_zero, h])).1
    refine ⟨⟨1, 0, h10⟩, mul_comm, ?_⟩
    intro z hz
    obtain ⟨x, y, rfl⟩ := hspan z
    have hn : x * x - D * (y * y) ≠ 0 := by
      intro h0
      by_cases hy : y = 0
      · subst hy
        have hx : x = 0 := by simpa using h0
        exact hz (by rw [hx, map_zero, zero_mul, add_zero])
      · refine hsq ⟨x / y, ?_⟩
        field_simp
        linear_combination h0
    refine ⟨algebraMap K R (x * (x * x - D * (y * y))⁻¹) - algebraMap K R (y * (x * x - D * (y * y))⁻¹) * T, ?_⟩
    have hni : algebraMap K R (x * x - D * (y * y)) * algebraMap K R (x * x - D * (y * y))⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hn, map_one]
    have hnn : algebraMap K R (x * x - D * (y * y)) =
        algebraMap K R x * algebraMap K R x - algebraMap K R D * (algebraMap K R y * algebraMap K R y) := by
      simp only [map_sub, map_mul]
    rw [map_mul, map_mul]
    generalize algebraMap K R (x * x - D * (y * y))⁻¹ = N at hni ⊢
    generalize algebraMap K R (x * x - D * (y * y)) = n at hni hnn
    generalize algebraMap K R x = X at hnn ⊢
    generalize algebraMap K R y = Y at hnn ⊢
    generalize algebraMap K R D = D' at hT hnn
    linear_combination (-(Y * Y * N)) * hT + hni - N * hnn

end Core

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_moved {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hreal : ComplexEmbedding.IsReal τ := ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => by
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := h.2.2.2 τ x
    rw [hc x] at this
    exact this.symm)
  have hcx := h.2.1.isComplex (InfinitePlace.mk τ)
  exact (InfinitePlace.isComplex_mk_iff.1 hcx) hreal

theorem exists_theta {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (θ : E) (d : F) (B : Module.Basis (Fin 2) F E), θ ≠ 0 ∧ d ≠ 0 ∧ σ θ = -θ ∧ θ * θ = algebraMap F E d ∧
      B 0 = 1 ∧ B 1 = θ := by
  obtain ⟨y, hy⟩ := exists_moved h
  have hE2 : (2 : E) ≠ 0 := two_ne_zero
  have hσθ : σ (y - σ y) = -(y - σ y) := by
    rw [map_sub, sigma_sigma h]
    ring
  have hθ : y - σ y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  generalize y - σ y = θ at hσθ hθ
  have hli : LinearIndependent F ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    simp only [Algebra.smul_def, mul_one] at hst
    have h1 := congrArg σ hst
    simp only [map_add, map_mul, AlgHom.commutes, hσθ, map_zero] at h1
    have hs : (2 : E) * algebraMap F E s = 0 := by
      linear_combination hst + h1
    have ht : (2 : E) * (algebraMap F E t * θ) = 0 := by
      linear_combination hst - h1
    have hs0 : s = 0 := by
      have := (mul_eq_zero.1 hs).resolve_left hE2
      exact (map_eq_zero _).1 this
    have ht0 : t = 0 := by
      have := ((mul_eq_zero.1 ((mul_eq_zero.1 ht).resolve_left hE2))).resolve_right hθ
      exact (map_eq_zero _).1 this
    exact ⟨hs0, ht0⟩
  let B : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [h.2.2.1, Fintype.card_fin])
  have hB0 : B 0 = 1 := by simp [B]
  have hB1 : B 1 = θ := by simp [B]
  have hsum := B.sum_repr (θ * θ)
  rw [Fin.sum_univ_two, hB0, hB1] at hsum
  generalize B.repr (θ * θ) 0 = a at hsum
  generalize B.repr (θ * θ) 1 = b at hsum
  have hsum' : algebraMap F E a + algebraMap F E b * θ = θ * θ := by
    simpa only [Algebra.smul_def, mul_one] using hsum
  have hconj := congrArg σ hsum'
  simp only [map_add, map_mul, AlgHom.commutes, hσθ] at hconj
  have hb : (2 : E) * (algebraMap F E b * θ) = 0 := by
    linear_combination hsum' - hconj
  have hb0 : algebraMap F E b = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 hb).resolve_left hE2)).resolve_right hθ
  have hsq : θ * θ = algebraMap F E a := by
    rw [← hsum', hb0, zero_mul, add_zero]
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hsq
    exact hθ (mul_self_eq_zero.1 hsq)
  exact ⟨θ, a, B, hθ, ha, hσθ, hsq, hB0, hB1⟩

end CM

theorem field_or_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K],
    IsField (K ⊗[F] E) ∨ ∃ e : K ⊗[F] E, e * e = e ∧ e + sigR K σ e = 1 ∧ e * sigR K σ e = 0 := by
  intro F E _ _ _ _ _ σ h K _ _
  obtain ⟨θ, d, B, hθ, hd, hσθ, hsq, hB0, hB1⟩ := exists_theta h
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let C : Module.Basis (Fin 2) K (K ⊗[F] E) := Algebra.TensorProduct.basis K B
  have hC0 : C 0 = 1 := by
    simp only [C, Algebra.TensorProduct.basis_apply, hB0]
    rfl
  have hC1 : C 1 = (1 : K) ⊗ₜ[F] θ := by
    simp only [C, Algebra.TensorProduct.basis_apply, hB1]
  refine core (K := K) (sigR K σ) ((1 : K) ⊗ₜ[F] θ) (algebraMap F K d) ?_ ?_ two_ne_zero ?_ ?_ ?_ ?_
  · rw [Algebra.TensorProduct.tmul_mul_tmul, hsq, mul_one, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.tmul_smul, Algebra.algebraMap_eq_smul_one (A := K),
      TensorProduct.smul_tmul']
    simp [Algebra.algebraMap_eq_smul_one]
  · exact fun h0 => hd ((map_eq_zero _).1 h0)
  · intro x
    change Algebra.TensorProduct.map (AlgHom.id F K) σ (algebraMap K (K ⊗[F] E) x) = _
    simp [Algebra.TensorProduct.algebraMap_apply]
  · change Algebra.TensorProduct.map (AlgHom.id F K) σ ((1 : K) ⊗ₜ[F] θ) = _
    rw [Algebra.TensorProduct.map_tmul, hσθ, TensorProduct.tmul_neg]
    rfl
  · intro z
    have hz := C.sum_repr z
    rw [Fin.sum_univ_two, hC0, hC1, Algebra.smul_def, Algebra.smul_def, mul_one] at hz
    exact ⟨_, _, hz.symm⟩
  · intro x y hxy
    have hl := Fintype.linearIndependent_iff.1 C.linearIndependent ![x, y] (by
      rw [Fin.sum_univ_two, hC0, hC1]
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one] using hxy)
    exact ⟨hl 0, hl 1⟩

end GlobalTheory.CompanionTheory.SaGen.Dichotomy
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerPropertiesResidueStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_properties_residue : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
    2 ≤ qOf π ∧ l ∣ qOf π ∧ π ∣ (l : ↥(OL K)) ∧
      ‖(((π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 ∧ ∀ μ : ↥K.1 →ₐ[ℚ_[l]] Om l, ‖((μ (π : ↥K.1) : Om l) : ℂ_[l])‖ < 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTPer.uniformiser_facts | exact GlobalTheory.CompanionTheory.LTPer.uniformiser_facts | (intros; apply GlobalTheory.CompanionTheory.LTPer.uniformiser_facts <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftDetOneApproxPair
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.LiftPlane

section Ring

variable {R : Type} [CommRing R] {M : ℕ}

private theorem hform_eq_dotProduct_mulVec (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a z : Fin M → R) :
    (fun j => ∑ i, c (a i) * Jm i j) ⬝ᵥ z = Formalism.UG.hform c Jm a z := by
  simp only [Formalism.UG.hform, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

private theorem smul_vecMulVec_left (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k : R) :
    k • Matrix.vecMulVec a (fun j => ∑ i, c (a i) * Jm i j) =
      Matrix.vecMulVec (k • a) (fun j => ∑ i, c (a i) * Jm i j) := by
  ext i j
  simp [Matrix.vecMulVec_apply, mul_assoc]

theorem det_qr (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a : Fin M → R) (k : R) :
    (qr c Jm a k).det = 1 + k * Formalism.UG.hform c Jm a a := by
  rw [qr, smul_vecMulVec_left, Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow,
    dotProduct_smul, smul_eq_mul, hform_eq_dotProduct_mulVec]

theorem qr_mulVec (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R) (a z : Fin M → R) (k : R) :
    (qr c Jm a k).mulVec z = z + (k * Formalism.UG.hform c Jm a z) • a := by
  rw [qr, Matrix.add_mulVec, Matrix.one_mulVec, smul_vecMulVec_left, Matrix.vecMulVec_mulVec, hform_eq_dotProduct_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
  ring

end Ring

section Lift

variable {F E K : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [Field K] [Algebra F K]
  [TopologicalSpace K]

theorem iB_mul_one_tmul (P : PlaceMap F K) (y : K ⊗[F] E) (s : E) :
    iB P y * ((1 : AF F) ⊗ₜ[F] s) = iB P (y * inclR K s) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul k e =>
    simp [iB, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.tmul_mul_tmul]
  | add y₁ y₂ h₁ h₂ => rw [map_add, add_mul, h₁, h₂, add_mul, map_add]

theorem sigR_incl (σ : E →ₐ[F] E) (e : E) : sigR K σ (inclR K e) = inclR K (σ e) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem hform_incV (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (a t : Fin M → E) :
    Formalism.UG.hform (sigR K σ) (JR K J) (incV K a) (incV K t) = inclR K (hf σ J a t) := by
  simp only [Formalism.UG.hform, incV, JR, Sa2.hf, Matrix.map_apply, sigR_incl, map_sum, map_mul]

end Lift

theorem lift_plane : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → (∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1)) → ∀ (a b : Fin M → E) (x : HA K σ J), IsQPairOf (sigR K σ) (JR K J) (incV K a) (incV K b) ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) → L x ∈ PlaneSupp σ J (P.inj 1) a b := by
  intro F E _ _ _ _ _ σ _ M J _ K _ _ P L hL hSU a b x hx
  obtain ⟨l, ka, kb, -, -, hl, hka, hkb, hX⟩ := hx
  have hdet : ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 := by
    rw [hX, Matrix.det_mul, det_qr, det_qr, hka, hkb]
    simpa using hl
  refine ⟨hSU x hdet, ?_⟩
  intro v hav hbv
  have hfix : ∀ (c : Fin M → E) (k : K ⊗[F] E), hf σ J c v = 0 →
      (qr (sigR K σ) (JR K J) (incV K c) k).mulVec (incV K v) = incV K v := by
    intro c k hc
    rw [qr_mulVec, hform_incV, hc, map_zero, mul_zero, zero_smul, add_zero]
  have hXv : ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).mulVec (incV K v) = incV K v := by
    rw [hX, ← Matrix.mulVec_mulVec, hfix b kb hbv, hfix a ka hav]
  have hsub : (((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1).mulVec (vA v) = 0 := by
    funext i
    have hterm : ∀ j, (((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j * vA v j =
        iB P ((((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1) i j * inclR K (v j)) := by
      intro j
      rw [hL x i j, ← iB_mul_one_tmul]
      rfl
    have hsum : ∑ j, (((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1) i j * inclR K (v j) =
        ((((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1).mulVec (incV K v)) i := rfl
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), ← map_sum]
    have h0 : ((((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) - 1).mulVec (incV K v)) = 0 := by
      rw [Matrix.sub_mulVec, hXv, Matrix.one_mulVec, sub_self]
    rw [hsum, h0, Pi.zero_apply, map_zero]
  calc ((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).mulVec (vA v)
      = (((HA.mat (AF F) σ J (L x)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1).mulVec (vA v) +
          (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).mulVec (vA v) := by
        rw [← Matrix.add_mulVec, sub_add_cancel]
    _ = vA v := by rw [hsub, Matrix.one_mulVec, zero_add]

end GlobalTheory.CompanionTheory.SaGen.LiftPlane

end
end

