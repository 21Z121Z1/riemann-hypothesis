import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0196
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0104
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockKsetPreservesHomogeneousDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0201
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0202
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyHermitianIntegrallyCongruentCmExt
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.HermCongAlmostAll

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigR_sigR_of {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (v : HeightOneSpectrum (𝓞 F))
    (y : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem exists_norm_eq_at {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (v : HeightOneSpectrum (𝓞 F)) (a : E)
    (ha : σ a = -a) (ha0 : a ≠ 0) (hai : 1 ⊗ₜ[F] a ∈ intLoc F E v) (hinv : 1 ⊗ₜ[F] (2 * a)⁻¹ ∈ intLoc F E v)
    (x : intLoc F E v) (hx : sigR (Fv F v) σ x = x) (hu : IsUnit x) :
    ∃ c : intLoc F E v, c.1 * sigR (Fv F v) σ c.1 = x.1 := by
  let O := intLoc F E v
  let _ := (intLocMap E v).toAlgebra
  have : Module.Finite (v.adicCompletionIntegers F) O := finite_intLocMap v
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have : Finite (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  have := GlobalTheory.InertNorm.isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  have := GlobalTheory.InertNorm.finite_quotient_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  let s : O →+* O := (sigR (Fv F v) σ).restrict O O fun _ => sigR_mem_intLoc σ
  have hs : ∀ y : O, s (s y) = y := fun y => Subtype.ext (sigR_sigR_of hσ v y.1)
  have hk : ∀ c, s (algebraMap (v.adicCompletionIntegers F) O c) = algebraMap (v.adicCompletionIntegers F) O c :=
    fun c => Subtype.ext (by
      change sigR (Fv F v) σ ((c : Fv F v) ⊗ₜ[F] (1 : E)) = (c : Fv F v) ⊗ₜ[F] (1 : E)
      simp [sigR])
  let I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).map (algebraMap (v.adicCompletionIntegers F) O)
  have hI : I ≤ I.comap s := Ideal.map_le_iff_le_comap.2 fun c hc => by
    rw [Ideal.mem_comap, Ideal.mem_comap, hk]
    exact Ideal.mem_map_of_mem _ hc
  have hω : IsUnit ((⟨_, hai⟩ : O) - s ⟨_, hai⟩) := by
    refine IsUnit.of_mul_eq_one (⟨_, hinv⟩ : O) (Subtype.ext ?_)
    change (inclR (Fv F v) a - inclR (Fv F v) (σ a)) * inclR (Fv F v) (2 * a)⁻¹ = 1
    rw [← map_sub, ← map_mul, ha, sub_neg_eq_add, ← two_mul, mul_inv_cancel₀ (mul_ne_zero two_ne_zero ha0), map_one]
  obtain ⟨c, hc⟩ := GlobalTheory.HenselianNorm.exists_norm_eq O I s hs (fun y hy => hI hy) ⟨_, hω⟩ x (Subtype.ext hx) hu
  exact ⟨c, congrArg Subtype.val hc⟩

end GlobalTheory.HermCongAlmostAll

namespace GlobalTheory.HermCongAlmostAll

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IntM (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) : Prop :=
  ∀ i j, X i j ∈ intLoc F E v

theorem intM_mul {v : HeightOneSpectrum (𝓞 F)} {X Y : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hX : IntM v X) (hY : IntM v Y) : IntM v (X * Y) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)

theorem intM_diagonal {v : HeightOneSpectrum (𝓞 F)} {c : Fin n → Fv F v ⊗[F] E}
    (hc : ∀ i, c i ∈ intLoc F E v) : IntM v (Matrix.diagonal c) := fun i j => by
  rw [Matrix.diagonal_apply]
  split_ifs
  exacts [hc i, zero_mem _]

theorem mulVec_mem {v : HeightOneSpectrum (𝓞 F)} {X : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)} (hX : IntM v X)
    {y : Fin n → Fv F v ⊗[F] E} (hy : ∀ i, y i ∈ intLoc F E v) : ∀ i, (X *ᵥ y) i ∈ intLoc F E v := fun i => by
  rw [Matrix.mulVec, dotProduct]
  exact sum_mem fun k _ => mul_mem (hX i k) (hy k)

theorem eventually_intM_JR (X : Matrix (Fin n) (Fin n) E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, IntM v (JR (Fv F v) X) :=
  eventually_all.2 fun i => eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (X i j)

theorem JR_mul (R : Type) [CommRing R] [Algebra F R] (X Y : Matrix (Fin n) (Fin n) E) :
    JR (F := F) R (X * Y) = JR R X * JR R Y := Matrix.map_mul

theorem JR_one (R : Type) [CommRing R] [Algebra F R] : JR (F := F) R (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem JR_diagonal (R : Type) [CommRing R] [Algebra F R] (d : Fin n → E) :
    JR (F := F) R (Matrix.diagonal d) = Matrix.diagonal fun i => inclR R (d i) :=
  Matrix.diagonal_map (map_zero _)

theorem cT_JR (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] (X : Matrix (Fin n) (Fin n) E) :
    Formalism.UG.cT (sigR R σ) (JR R X) = JR R (Formalism.UG.cT (σ : E →+* E) X) := rfl

theorem cT_diagonal {A : Type} [CommRing A] (s : A →+* A) (c : Fin n → A) :
    Formalism.UG.cT s (Matrix.diagonal c) = Matrix.diagonal fun i => s (c i) := by
  unfold Formalism.UG.cT
  rw [Matrix.diagonal_map (map_zero s), Matrix.diagonal_transpose]

end GlobalTheory.HermCongAlmostAll

namespace GlobalTheory.HermCongAlmostAll

theorem eventually_congr_int : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J J' : Matrix (Fin n) (Fin n) E), IsHermND σ J → IsHermND σ J' →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ u : GL (Fin n) (Fv F v ⊗[F] E),
      Formalism.UG.cT (sigR (Fv F v) σ) u.1 * JR (Fv F v) J * u.1 = JR (Fv F v) J' ∧
      ∀ y, u.1 *ᵥ y ∈ latLoc F (stdLattice E n) v ↔ y ∈ latLoc F (stdLattice E n) v := by
  intro F E _ _ _ _ _ σ h n J J' hJ hJ'
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])
  have diag : ∀ {G : Matrix (Fin n) (Fin n) E}, IsHermND σ G → ∃ (Q Q' : Matrix (Fin n) (Fin n) E) (d : Fin n → E),
      Q * Q' = 1 ∧ Q' * Q = 1 ∧ Formalism.UG.cT (σ : E →+* E) Q * G * Q = Matrix.diagonal d ∧
      (∀ i, σ (d i) = d i) ∧ ∀ i, d i ≠ 0 := by
    intro G hG
    obtain ⟨P, d, hP, hd, hdσ, hd0⟩ :=
      GlobalTheory.HermDiag.exists_congr_diagonal (c := (σ : E →+* E)) two_ne_zero hσ (G := G) (fun a b => hG.1 b a)
    have hu : IsUnit (P.map (σ : E →+* E)).det := by
      rw [show (P.map (σ : E →+* E)).det = (σ : E →+* E) P.det from (RingHom.map_det _ P).symm]
      exact ((map_ne_zero (σ : E →+* E)).2 hP).isUnit
    have hc : Formalism.UG.cT (σ : E →+* E) (P.map (σ : E →+* E)) = Pᵀ := by
      ext i j
      simp [Formalism.UG.cT, hσ]
    refine ⟨P.map (σ : E →+* E), (P.map (σ : E →+* E))⁻¹, d, Matrix.mul_nonsing_inv _ hu,
      Matrix.nonsing_inv_mul _ hu, ?_, hdσ, hd0 hG.2⟩
    rw [hc]
    exact hd
  obtain ⟨Q, Qi, d, hQ1, hQ2, hQd, hdσ, hd0⟩ := diag hJ
  obtain ⟨R, Ri, e, hR1, hR2, hRe, heσ, he0⟩ := diag hJ'
  obtain ⟨a, ha0, ha⟩ := exists_integer_conj_eq_neg h
  have ha0' : (a : E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ha0
  filter_upwards [eventually_intM_JR (F := F) Q, eventually_intM_JR (F := F) Qi, eventually_intM_JR (F := F) R,
    eventually_intM_JR (F := F) Ri,
    eventually_all.2 fun i => eventually_one_tmul_mem_intLoc (F := F) (e i / d i),
    eventually_all.2 fun i => eventually_one_tmul_mem_intLoc (F := F) (d i / e i),
    eventually_one_tmul_mem_intLoc (F := F) (2 * (a : E))⁻¹] with v h1 h2 h3 h4 h5 h6 h7
  have hed : ∀ i, e i / d i * (d i / e i) = 1 := fun i => by
    rw [div_mul_div_comm, mul_comm (e i), div_self (mul_ne_zero (hd0 i) (he0 i))]
  have hc : ∀ i, ∃ c : intLoc F E v, c.1 * sigR (Fv F v) σ c.1 = inclR (Fv F v) (e i / d i) := fun i =>
    exists_norm_eq_at hσ v a ha ha0' (tmul_mem_intLoc (one_mem _) a) h7 ⟨_, h5 i⟩
      (by
        change inclR (Fv F v) (σ (e i / d i)) = inclR (Fv F v) (e i / d i)
        rw [map_div₀, hdσ, heσ])
      (IsUnit.of_mul_eq_one (⟨_, h6 i⟩ : intLoc F E v) (Subtype.ext (by
        change inclR (Fv F v) (e i / d i) * inclR (Fv F v) (d i / e i) = 1
        rw [← map_mul, hed, map_one])))
  choose c hc using hc
  set s := sigR (Fv F v) σ with hs
  let C : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := Matrix.diagonal fun i => (c i).1
  let C' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) :=
    Matrix.diagonal fun i => s (c i).1 * inclR (Fv F v) (d i / e i)
  have hCC : C * C' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← mul_assoc, hc i, ← map_mul, hed, map_one]
  have hC'C : C' * C = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm, ← mul_assoc, hc i, ← map_mul, hed, map_one]
  let u := JR (Fv F v) Q * C * JR (Fv F v) Ri
  let u' := JR (Fv F v) R * C' * JR (Fv F v) Qi
  have huu : u * u' = 1 := by
    calc u * u' = JR (Fv F v) Q * C * (JR (Fv F v) (Ri * R)) * C' * JR (Fv F v) Qi := by
          simp only [u, u', JR_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [hR2, JR_one, Matrix.mul_one, Matrix.mul_assoc (JR (Fv F v) Q), hCC, Matrix.mul_one, ← JR_mul, hQ1,
            JR_one]
  have huu' : u' * u = 1 := by
    calc u' * u = JR (Fv F v) R * C' * (JR (Fv F v) (Qi * Q)) * C * JR (Fv F v) Ri := by
          simp only [u, u', JR_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [hQ2, JR_one, Matrix.mul_one, Matrix.mul_assoc (JR (Fv F v) R), hC'C, Matrix.mul_one, ← JR_mul, hR1,
            JR_one]
  have hCint : IntM v C := intM_diagonal fun i => (c i).2
  have hC'int : IntM v C' := intM_diagonal fun i => mul_mem (sigR_mem_intLoc σ (c i).2) (h6 i)
  have hui : IntM v u := intM_mul (intM_mul h1 hCint) h4
  have hu'i : IntM v u' := intM_mul (intM_mul h3 hC'int) h2
  have eC : Formalism.UG.cT s C * Matrix.diagonal (fun i => inclR (Fv F v) (d i)) * C =
      Matrix.diagonal fun i => inclR (Fv F v) (e i) := by
    rw [cT_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [show s (c i).1 * inclR (Fv F v) (d i) * (c i).1 = (c i).1 * s (c i).1 * inclR (Fv F v) (d i) by ring, hc i,
      ← map_mul, div_mul_cancel₀ _ (hd0 i)]
  refine ⟨⟨u, u', huu, huu'⟩, ?_, fun y => ?_⟩
  · change Formalism.UG.cT s u * JR (Fv F v) J * u = JR (Fv F v) J'
    have k1 : Formalism.UG.cT s u * JR (Fv F v) J * u = JR (Fv F v) (Formalism.UG.cT (σ : E →+* E) Ri) *
        (Formalism.UG.cT s C * JR (Fv F v) (Formalism.UG.cT (σ : E →+* E) Q * J * Q) * C) * JR (Fv F v) Ri := by
      simp only [u, Formalism.UG.cT_mul, hs, cT_JR, JR_mul, Matrix.mul_assoc]
    rw [k1, hQd, JR_diagonal, eC, ← JR_diagonal, ← hRe, ← JR_mul, ← JR_mul]
    congr 1
    calc Formalism.UG.cT (σ : E →+* E) Ri * (Formalism.UG.cT (σ : E →+* E) R * J' * R) * Ri =
        (Formalism.UG.cT (σ : E →+* E) Ri * Formalism.UG.cT (σ : E →+* E) R) * J' * (R * Ri) := by
          simp only [Matrix.mul_assoc]
      _ = J' := by rw [← Formalism.UG.cT_mul, hR1, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  · change u *ᵥ y ∈ latLoc F (stdLattice E n) v ↔ y ∈ latLoc F (stdLattice E n) v
    rw [mem_latLoc_stdLattice, mem_latLoc_stdLattice]
    refine ⟨fun hy => ?_, fun hy => mulVec_mem hui hy⟩
    have := mulVec_mem hu'i hy
    rwa [Matrix.mulVec_mulVec, huu', Matrix.one_mulVec] at this

end GlobalTheory.HermCongAlmostAll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAdjoinRootLinearEquivOfCharpolyEq
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrEll

theorem exists_linearEquiv_mulVec_of_charpoly (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (P : PPol σ n) (A : Matrix (Fin n) (Fin n) E) (hA : A.charpoly = P.1) :
    ∃ φ : Fld P ≃ₗ[E] (Fin n → E), ∀ y, A *ᵥ φ y = φ (alpha P * y) := by

  let ψ : Fld P →ₐ[E] Matrix (Fin n) (Fin n) E :=
    Ideal.Quotient.liftₐ (Ideal.span {P.1}) (Polynomial.aeval A) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul, ← hA, Matrix.aeval_self_charpoly, mul_zero])
  have hψα : ψ (alpha P) = A := by
    change Polynomial.aeval A Polynomial.X = A
    exact Polynomial.aeval_X A

  have hdim : Module.finrank E (Fld P) = n := by
    have h1 := (AdjoinRoot.powerBasis P.2.2.1.ne_zero).finrank
    rw [AdjoinRoot.powerBasis_dim] at h1
    exact h1.trans P.2.2.2.1
  have hpos : 0 < n := hdim ▸ Module.finrank_pos
  haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : Fin n → E)
  let f : Fld P →ₗ[E] (Fin n → E) :=
    { toFun := fun y => ψ y *ᵥ v
      map_add' := fun y z => by simp [Matrix.add_mulVec]
      map_smul' := fun c y => by simp [Matrix.smul_mulVec] }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hne
    apply hv
    have h1 : ψ y⁻¹ * ψ y = 1 := by rw [← map_mul, inv_mul_cancel₀ hne, map_one]
    have h2 : ψ y *ᵥ v = 0 := hy
    calc v = (ψ y⁻¹ * ψ y) *ᵥ v := by rw [h1, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h2, Matrix.mulVec_zero]
  refine ⟨LinearMap.linearEquivOfInjective f hinj (by rw [hdim, Module.finrank_fin_fun]), fun y => ?_⟩
  simp only [LinearMap.linearEquivOfInjective_apply]
  change A *ᵥ (ψ y *ᵥ v) = ψ (alpha P * y) *ᵥ v
  rw [map_mul, hψα, Matrix.mulVec_mulVec]

end GlobalTheory.TrEll
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContractionIsometricDiscreteSeriesFock
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.CoverContr

theorem inner_map_of_norm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : H →L[ℂ] H)
    (hA : ∀ x, ‖A x‖ = ‖x‖) (x y : H) : inner ℂ (A x) (A y) = inner ℂ x y := by
  let L : H →ₗᵢ[ℂ] H := ⟨A.toLinearMap, hA⟩
  exact L.inner_map_map x y

private theorem inner_unitary_apply_eq_inner_inv {G E : Type} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : G →* E →L[ℂ] E) (hU : ∀ g x, ‖U g x‖ = ‖x‖) (g : G) (v w : E) :
    inner ℂ (U g v) w = inner ℂ v (U g⁻¹ w) := by
  have h1 : U g (U g⁻¹ w) = w := by
    have h := congrArg (fun f : E →L[ℂ] E => f w) (map_mul U g g⁻¹)
    simpa using h.symm
  conv_lhs => rw [← h1]
  exact inner_map_of_norm (U g) (hU g) v (U g⁻¹ w)

theorem exists_isCoverIt : ∀ (p q r s : ℕ) (T₀ : GrpData (p * r + q * s) (p * s + q * r)) (T₁ : GrpData p q) (T₂ : GrpData r s) (F : FockData T₀ T₁ T₂) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (Tm : R₁.U.H →L[ℂ] R₂.U.H →L[ℂ] F.H), (∀ x x' y y', inner ℂ (Tm x y) (Tm x' y') = inner ℂ x x' * inner ℂ y y') → (∀ g h x y, F.π (g, h) (Tm x y) = Tm (R₁.U.π g x) (R₂.U.π h y)) → ∃ B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H, IsCoverIt R₁ R₂ B := by
  intro p q r s T₀ T₁ T₂ F R₁ R₂ Tm hTm hEq

  have hnorm : ∀ x y, ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
    intro x y
    have h := hTm x x y y
    simp only [inner_self_eq_norm_sq_to_K] at h
    have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
      rw [mul_pow]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero).1 h2
  have hflip : ∀ y, ‖Tm.flip y‖ ≤ ‖y‖ := fun y =>
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y) fun x => by
      rw [ContinuousLinearMap.flip_apply, hnorm, mul_comm]

  have hsrc : ∀ (g : T₁.G) (y : R₂.U.H) (v : F.H),
      R₁.U.π g (ContinuousLinearMap.adjoint (Tm.flip y) v) =
        ContinuousLinearMap.adjoint (Tm.flip y) (F.π (g, 1) v) := by
    intro g y v
    apply ext_inner_right ℂ
    intro x
    rw [inner_unitary_apply_eq_inner_inv R₁.U.π R₁.U.isom, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.flip_apply]
    have e1 : Tm (R₁.U.π g⁻¹ x) y = F.π (g⁻¹, 1) (Tm x y) := by
      rw [hEq]; simp
    have e2 : F.π (g, 1) v = F.Om (F.emb (g, 1)) v := rfl
    have e3 : F.π (g⁻¹, 1) (Tm x y) = F.Om (F.emb (g, 1))⁻¹ (Tm x y) := by
      have : ((g⁻¹, 1) : T₁.G × T₂.G) = (g, 1)⁻¹ := by simp
      show F.Om (F.emb (g⁻¹, 1)) (Tm x y) = _
      rw [this, map_inv]
    rw [e1, e2, e3, inner_unitary_apply_eq_inner_inv F.Om F.isom]

  have htgt : ∀ (h : T₂.G) (y : R₂.U.H) (v : F.H),
      ContinuousLinearMap.adjoint (Tm.flip (R₂.U.π h y)) v =
        ContinuousLinearMap.adjoint (Tm.flip y) (F.π (1, h⁻¹) v) := by
    intro h y v
    apply ext_inner_right ℂ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
    have e1 : Tm x (R₂.U.π h y) = F.π (1, h) (Tm x y) := by
      rw [hEq]; simp
    have e2 : F.π (1, h⁻¹) v = F.Om (F.emb (1, h⁻¹)) v := rfl
    have e3 : F.π (1, h) (Tm x y) = F.Om (F.emb (1, h⁻¹))⁻¹ (Tm x y) := by
      have : ((1, h) : T₁.G × T₂.G) = (1, h⁻¹)⁻¹ := by simp
      show F.Om (F.emb (1, h)) (Tm x y) = _
      rw [this, map_inv]
    rw [e1, e2, e3, inner_unitary_apply_eq_inner_inv F.Om F.isom]
  let B : Pol p q r s →ₗ[ℂ] R₂.U.H →ₛₗ[starRingEnd ℂ] R₁.U.H :=
    { toFun := fun P =>
        { toFun := fun y => ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P)
          map_add' := fun y y' => by simp
          map_smul' := fun c y => by
            rw [map_smul, LinearIsometryEquiv.map_smulₛₗ, ContinuousLinearMap.smul_apply] }
      map_add' := fun P P' => by ext y; simp
      map_smul' := fun c P => by ext y; simp }
  have hB : ∀ P y, B P y = ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P) := fun _ _ => rfl
  refine ⟨B, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro P
    refine ⟨‖F.ι P‖, fun y => ?_⟩
    rw [hB]
    calc ‖ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P)‖
        ≤ ‖ContinuousLinearMap.adjoint (Tm.flip y)‖ * ‖F.ι P‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Tm.flip y‖ * ‖F.ι P‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ ‖y‖ * ‖F.ι P‖ := by gcongr; exact hflip y
      _ = ‖F.ι P‖ * ‖y‖ := mul_comm _ _
  · intro P y
    rw [R₁.ι_range, hB]
    unfold KFin
    have hk := (GlobalTheory.FockKFin.kfin_fock p q r s T₀ T₁ T₂ F
      (GlobalTheory.FockDegree.Om_Kset_homog p q r s T₀ T₁ T₂ F) P).1
    unfold KFin at hk
    haveI := hk
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.map
      (ContinuousLinearMap.adjoint (Tm.flip y)).toLinearMap
      (Submodule.span ℂ (Set.range fun k : ↥T₁.Kset => F.π ((k : T₁.G), 1) (F.ι P)))) ?_
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, (hsrc _ y _).symm⟩
  · intro y hy
    by_contra hcon
    push_neg at hcon
    haveI := R₁.nontriv
    obtain ⟨x, hx⟩ := exists_ne (0 : R₁.U.H)
    have hz : (fun v : F.H => inner ℂ v (Tm x y)) = fun _ => 0 := by
      refine Continuous.ext_on F.dense (continuous_id.inner continuous_const) continuous_const ?_
      rintro _ ⟨P, rfl⟩
      have h0 : ContinuousLinearMap.adjoint (Tm.flip y) (F.ι P) = 0 := by rw [← hB]; exact hcon P
      have := ContinuousLinearMap.adjoint_inner_left (Tm.flip y) x (F.ι P)
      rw [h0, inner_zero_left, ContinuousLinearMap.flip_apply] at this
      exact this.symm
    have h1 : Tm x y = 0 := inner_self_eq_zero.1 (congrFun hz (Tm x y))
    have h2 := hnorm x y
    rw [h1, norm_zero] at h2
    exact mul_ne_zero (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy) h2.symm
  · intro Z hZ P y
    have hd := (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T₀ T₁ T₂ F).2.1 Z hZ P
    have hc := ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
    have e : (fun t : ℝ => R₁.U.π (T₁.expt (t • Z)) (B P y)) =
        (ContinuousLinearMap.adjoint (Tm.flip y)) ∘
          (fun t : ℝ => F.π (T₁.expt (t • Z), 1) (F.ι P)) := by
      funext t
      rw [hB, Function.comp_apply, hsrc]
    rw [e, hB]
    exact hc
  · intro Z hZ P y
    have hone : T₂.expt ((0 : ℝ) • Z) = 1 := by
      have h := T₂.expt_add Z hZ 0 0
      rw [add_zero] at h
      have h' := congrArg (· * (T₂.expt ((0 : ℝ) • Z))⁻¹) h
      simpa [mul_assoc] using h'.symm
    have hinv : ∀ t : ℝ, (T₂.expt (t • Z))⁻¹ = T₂.expt ((-t) • Z) := by
      intro t
      have h := T₂.expt_add Z hZ (-t) t
      rw [neg_add_cancel, hone] at h
      exact (eq_inv_of_mul_eq_one_left h.symm).symm
    have hd := (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T₀ T₁ T₂ F).2.2 Z hZ P
    have hd' : HasDerivAt (fun u : ℝ => F.π (1, T₂.expt (u • Z)) (F.ι P))
        (F.ι (fockAct2 p q r s Z P)) (-(0 : ℝ)) := by rw [neg_zero]; exact hd
    have hn := hd'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
    have hc := ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hn
    have e : (fun t : ℝ => B P (R₂.U.π (T₂.expt (t • Z)) y)) =
        (ContinuousLinearMap.adjoint (Tm.flip y)) ∘
          ((fun u : ℝ => F.π (1, T₂.expt (u • Z)) (F.ι P)) ∘ fun t : ℝ => -t) := by
      funext t
      rw [hB, htgt, hinv]
      rfl
    have hval : ((ContinuousLinearMap.adjoint (Tm.flip y)).restrictScalars ℝ)
        ((-1 : ℝ) • F.ι (fockAct2 p q r s Z P)) =
        -(ContinuousLinearMap.adjoint (Tm.flip y)) (F.ι (fockAct2 p q r s Z P)) := by
      rw [neg_one_smul, map_neg]
      rfl
    rw [e, hB, ← hval]
    exact hc

end GlobalTheory.Chain.CoverContr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteAdeleOfSplitPlacesIdempotentSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.IdemSumFinAdele

theorem exists_finAdele_of_idemSum : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∃ σ : Af D.host.F, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 σ) = e + cA D e ∧ (∀ w : HeightOneSpectrum (𝓞 D.host.F), (∀ PP ∈ P, HeightOneSpectrum.under (𝓞 D.host.F) PP ≠ w) → evalV D.host.F w σ = 0) ∧ ∀ PP ∈ P, evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) σ = 1 := by
  intro D P e he
  have he' := he
  obtain ⟨⟨es, hes, rfl⟩, hz⟩ := he
  have hex : ∀ PP ∈ P, ∃ α : Af D.host.F,
      algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = es PP + cA D (es PP) ∧
      evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) α = 1 ∧
      ∀ v', v' ≠ HeightOneSpectrum.under (𝓞 D.host.F) PP → evalV D.host.F v' α = 0 := by
    intro PP hPP
    obtain ⟨⟨a1, a2, v, ε, hε, a3⟩, -⟩ := hes PP hPP
    have hv := GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP v ε (hes PP hPP) hε a3
    obtain ⟨α, rfl, h1, h2⟩ := hε
    exact ⟨α, a3.symm, hv ▸ h1, hv ▸ h2⟩
  choose! α hα using hex
  have hsum : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (∑ PP ∈ P, α PP)) =
      ∑ PP ∈ P, es PP + cA D (∑ PP ∈ P, es PP) := by
    have hp : pairA D.host.F 0 (∑ PP ∈ P, α PP) = ∑ PP ∈ P, pairA D.host.F 0 (α PP) := by
      have hadd : ∀ a b : Af D.host.F, pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b :=
        fun a b => Prod.ext (add_zero 0).symm rfl
      exact map_sum (AddMonoidHom.mk' (pairA D.host.F 0) hadd) α P
    rw [hp, map_sum, map_sum (cA D), ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun PP hPP => (hα PP hPP).1
  refine ⟨∑ PP ∈ P, α PP, hsum, ?_, ?_⟩
  · intro w hw
    rw [map_sum]
    exact Finset.sum_eq_zero fun PP hPP => (hα PP hPP).2.2 w (hw PP hPP).symm
  · intro PP hPP
    have h1 := GlobalTheory.CompFinIdemSum.compFin_add_cA_eq_one P _ he' PP hPP
    rw [← hsum] at h1
    have h2 : (evalV D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP) (∑ PP ∈ P, α PP)) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (1 : Fv D.host.F _ ⊗[D.host.F] D.host.E) := h1
    haveI : Module.Free D.host.F (Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) :=
      Module.Free.of_divisionRing _ _
    haveI : Module.Flat D.host.F (Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) := Module.Flat.of_free
    have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F)
      (A := Fv D.host.F (HeightOneSpectrum.under (𝓞 D.host.F) PP)) (B := D.host.E) (algebraMap D.host.F D.host.E).injective
    apply hinj
    rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeLeft_apply, h2]
    rfl

end GlobalTheory.IdemSumFinAdele

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityLeviCharGeometricLemmaCeStatement
section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jordanHolderMultiplicity_leviChar_geometricLemmaCell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], CellSemisimplification k → ∀ (α β : Type) [Fintype α] [LinearOrder α] [Fintype β] [LinearOrder β] (m : α → Type) [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (c : α → β → Type) [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ Unit) (X : α → Type) [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)] (ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)), (∀ i, IsSmooth (ρ i)) → (∀ i, HasFiniteLength (ρ i)) → ∀ χ : β → kˣ →* ℂˣ, (∀ j, IsSmoothChar (χ j)) → jhMult (ofChar (leviChar (fun _ : β => Unit) χ)) (cellFunctor (m' := fun _ : β => Unit) f g (piTensor ρ)) = ∏ i, jhMult (ofChar (leviChar (c i) χ)) (jac (f i) (ρ i)) := by
  first | exact @GlobalTheory.SmGL.Exponents.jhMult_leviChar_cellFunctor | exact GlobalTheory.SmGL.Exponents.jhMult_leviChar_cellFunctor | (intros; apply GlobalTheory.SmGL.Exponents.jhMult_leviChar_cellFunctor <;> assumption)
end

