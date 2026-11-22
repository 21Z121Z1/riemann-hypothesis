import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.LeviFormGbPotOne

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.FlagPsLine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open Polynomial Matrix

noncomputable section

theorem sum_fin_split_castLE {M : Type*} [AddCommMonoid M] {i N : ℕ} (hi : i ≤ N)
    (f : Fin N → M) :
    ∑ c, f c = ∑ c : Fin i, f (Fin.castLE hi c) + ∑ c, if i ≤ c.val then f c else 0 := by
  have h1 : (Finset.univ.filter fun c : Fin N => c.val < i) =
      Finset.univ.map (Fin.castLEEmb hi) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro h; exact ⟨⟨c.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨c', rfl⟩; exact c'.isLt
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c : Fin N => c.val < i), h1,
    Finset.sum_map, Finset.sum_filter]
  simp only [Fin.castLEEmb_apply, not_lt]

theorem contDiff_det_of_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Type*} [Fintype m] [DecidableEq m] {M : E → Matrix m m ℂ}
    (h : ∀ a b, ContDiff ℝ 2 fun x => M x a b) : ContDiff ℝ 2 fun x => (M x).det := by
  simp only [Matrix.det_apply]
  refine ContDiff.sum fun σ _ => ?_
  exact (contDiff_prod fun a _ => h _ _).const_smul _

variable {N : ℕ}

def sigSign (p : ℕ) (a : Fin N) : ℝ := if a.val < p then 1 else -1

theorem signatureForm_eq (p : ℕ) :
    signatureForm N p = diagonal fun a => ((sigSign p a : ℝ) : ℂ) := by
  unfold signatureForm
  congr 1
  funext a
  unfold sigSign
  split_ifs <;> simp

def tailSum (p i : ℕ) (L : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ b : Fin N, ∑ c : Fin N,
    if b.val < i ∧ i ≤ c.val then sigSign p b * sigSign p c * ‖L c b‖ ^ 2 else 0

section Poly

variable (p i : ℕ) (hi : i ≤ N) (L : Matrix (Fin N) (Fin N) ℂ)

def colPoly : Matrix (Fin N) (Fin i) ℂ[X] :=
  Matrix.of fun c b => (if c = Fin.castLE hi b then 1 else 0) + X * C (L c (Fin.castLE hi b))

def rowPoly : Matrix (Fin i) (Fin N) ℂ[X] :=
  Matrix.of fun a c =>
    (if c = Fin.castLE hi a then 1 else 0) + X * C (star (L c (Fin.castLE hi a)))

def topPoly : Matrix (Fin i) (Fin i) ℂ[X] := (colPoly i hi L).submatrix (Fin.castLE hi) id

def topPoly' : Matrix (Fin i) (Fin i) ℂ[X] := (rowPoly i hi L).submatrix id (Fin.castLE hi)

def sigTop : Matrix (Fin i) (Fin i) ℂ :=
  diagonal fun a => ((sigSign p (Fin.castLE hi a) : ℝ) : ℂ)

def tailForm : Matrix (Fin i) (Fin i) ℂ :=
  Matrix.of fun a b => ∑ c : Fin N, if i ≤ c.val then
    star (L c (Fin.castLE hi a)) * ((sigSign p c : ℝ) : ℂ) * L c (Fin.castLE hi b) else 0

def kerPoly : Matrix (Fin i) (Fin i) ℂ[X] :=
  (sigTop p i hi).map C * (topPoly' i hi L).adjugate * (tailForm p i hi L).map C *
    (topPoly i hi L).adjugate

theorem gram_eq : rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L =
    topPoly' i hi L * (sigTop p i hi).map C * topPoly i hi L +
      (X ^ 2 : ℂ[X]) • (tailForm p i hi L).map C := by
  rw [signatureForm_eq]
  refine Matrix.ext fun a b => ?_
  rw [Matrix.add_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply]
  simp only [Matrix.diagonal_map (map_zero C), Matrix.mul_diagonal]
  rw [sum_fin_split_castLE hi]
  congr 1
  · rw [sigTop, Matrix.diagonal_map (map_zero C), Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    rfl
  · simp only [tailForm, Matrix.of_apply, map_sum, Finset.mul_sum, smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs with hc
    · have h1 : ∀ a : Fin i, c ≠ Fin.castLE hi a := fun a h => by
        have := congrArg Fin.val h
        simp at this
        omega
      simp only [rowPoly, colPoly, Matrix.of_apply, h1, if_false, zero_add, map_mul]
      ring
    · simp

theorem sigTop_mul_self : sigTop p i hi * sigTop p i hi = 1 := by
  rw [sigTop, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  unfold sigSign
  split_ifs <;> simp

variable {L}

theorem det_topPoly (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) : (topPoly i hi L).det = 1 := by
  rw [det_of_isLowerTriangular _ ?_]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [topPoly, colPoly, hL _ _ (lt_irrefl _)]
  · intro a b hab
    have hab' : a < b := by simpa using hab
    have h1 : Fin.castLE hi a ≠ Fin.castLE hi b := fun h =>
      (ne_of_lt hab') (Fin.castLE_injective hi h)
    have h2 : L (Fin.castLE hi a) (Fin.castLE hi b) = 0 :=
      hL _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; exact fun h => absurd hab' (by
        rw [Fin.lt_def]; omega))
    simp [topPoly, colPoly, h1, h2]

theorem det_topPoly' (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) : (topPoly' i hi L).det = 1 := by
  rw [det_of_isUpperTriangular ?_]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [topPoly', rowPoly, hL _ _ (lt_irrefl _)]
  · intro a b hab
    have hab' : b < a := by simpa using hab
    have h1 : Fin.castLE hi b ≠ Fin.castLE hi a := fun h =>
      (ne_of_lt hab') (Fin.castLE_injective hi h)
    have h2 : L (Fin.castLE hi b) (Fin.castLE hi a) = 0 :=
      hL _ _ (by simp only [Fin.lt_def, Fin.val_castLE]; exact fun h => absurd hab' (by
        rw [Fin.lt_def]; omega))
    simp [topPoly', rowPoly, h1, h2]

theorem det_gram (hL : ∀ a b : Fin N, ¬ b < a → L a b = 0) :
    (rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L).det =
      C (sigTop p i hi).det * (1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi L).det := by
  have hSS : (sigTop p i hi).map C * (sigTop p i hi).map C = 1 := by
    rw [← Matrix.map_mul, sigTop_mul_self]; simp
  have hK : topPoly' i hi L * (sigTop p i hi).map C * kerPoly p i hi L * topPoly i hi L =
      (tailForm p i hi L).map C := by
    calc topPoly' i hi L * (sigTop p i hi).map C * kerPoly p i hi L * topPoly i hi L
        = (topPoly' i hi L * ((sigTop p i hi).map C * (sigTop p i hi).map C) *
            (topPoly' i hi L).adjugate) * (tailForm p i hi L).map C *
            ((topPoly i hi L).adjugate * topPoly i hi L) := by
          simp only [kerPoly, Matrix.mul_assoc]
      _ = (tailForm p i hi L).map C := by
          rw [hSS, Matrix.mul_one, Matrix.mul_adjugate, Matrix.adjugate_mul, det_topPoly i hi hL,
            det_topPoly' i hi hL, one_smul, Matrix.one_mul, Matrix.mul_one]
  have hfac : rowPoly i hi L * (signatureForm N p).map C * colPoly i hi L =
      topPoly' i hi L * (sigTop p i hi).map C * (1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi L) *
        topPoly i hi L := by
    rw [gram_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul,
      Matrix.smul_mul, hK]
  rw [hfac, det_mul, det_mul, det_mul, det_topPoly i hi hL, det_topPoly' i hi hL, one_mul,
    mul_one]
  rw [show ((sigTop p i hi).map C).det = C (sigTop p i hi).det from
    ((C : ℂ →+* ℂ[X]).map_det _).symm]

end Poly

theorem coeff_det_one_add_X_sq_smul {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ[X]) :
    (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 0 = 1 ∧ (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 1 = 0 ∧
      (1 + (X ^ 2 : ℂ[X]) • K).det.coeff 2 = K.trace.coeff 0 := by
  rw [det_one_add_smul]
  refine ⟨?_, ?_, ?_⟩ <;> simp [coeff_one, ← pow_mul, coeff_mul_X_pow']

end

end GroundTheory.Heights₂.Heights.FourB
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.HypImp
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

def CoverMass2.Hyp {D : ℕ} (M Z : Set (Fin D → ℂ)) (z : (Fin D → ℂ) → (Fin D → ℂ)) (δ : ℕ) :
    Prop :=
  IsOpen M ∧ volume Z = 0 ∧ DifferentiableOn ℂ z M ∧ Set.MapsTo z M Zᶜ ∧
    IsCoveringMapOn (fun x : M => z x) Zᶜ ∧ ∀ w ∉ Z, Set.encard {x | x ∈ M ∧ z x = w} = δ

def CoverMass2.Statement : Prop :=
  ∀ (D : ℕ) (M Z : Set (Fin D → ℂ)) (z : (Fin D → ℂ) → (Fin D → ℂ)) (δ : ℕ),
    CoverMass2.Hyp M Z z δ →
      ∫⁻ x in M, ENNReal.ofReal (topDens (fun y => Real.log (1 + ∑ i, ‖z y i‖ ^ 2)) x) = δ

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.Imports
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem DetMono.equiv :
    FourB.HermitianDetMono.Statement ↔ IndefiniteRowSideFullHecke.FourB.DetMono.Statement := by
  constructor
  · intro h n A A' hA
    exact h n A A' hA.1 hA.2
  · intro h n A B hB hAB
    exact h n A B ⟨hB, hAB⟩

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.NormLeOneIffIsIntegralElemOfEquiv
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open IsDedekindDomain NumberField Polynomial Rat.HeightOneSpectrum

theorem isIntegralElem_comp_ringEquiv {A B S : Type*} [CommRing A] [CommRing B] [CommRing S]
    (φ : A ≃+* B) (f : B →+* S) (x : S) :
    (f.comp (φ : A →+* B)).IsIntegralElem x ↔ f.IsIntegralElem x := by
  constructor
  · rintro ⟨q, hq, hx⟩
    exact ⟨q.map (φ : A →+* B), hq.map _, by rwa [eval₂_map]⟩
  · rintro ⟨q, hq, hx⟩
    refine ⟨q.map (φ.symm : B →+* A), hq.map _, ?_⟩
    rw [eval₂_map, RingHom.comp_assoc]
    have : (φ : A →+* B).comp (φ.symm : B →+* A) = RingHom.id B :=
      RingHom.ext fun b => by simp
    rwa [this, RingHom.comp_id]

theorem norm_le_one_iff_isIntegralElem_padicInt (p : ℕ) [Fact p.Prime] {K : Type*}
    [NormedField K] [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] (x : K) :
    ‖x‖ ≤ 1 ↔ ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).IsIntegralElem x := by
  have hx : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  rw [NormedAlgebra.norm_eq_spectralNorm ℚ_[p] x, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic hx)]
  let : Algebra ℤ_[p] K := ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])).toAlgebra
  have : IsScalarTower ℤ_[p] ℚ_[p] K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  constructor
  · intro h
    have hl : minpoly ℚ_[p] x ∈ Polynomial.lifts (algebraMap ℤ_[p] ℚ_[p]) := by
      rw [lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hmon⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hx)
    refine ⟨q, hmon, ?_⟩
    have h0 : eval₂ (algebraMap ℚ_[p] K) x (q.map (algebraMap ℤ_[p] ℚ_[p])) = 0 := by
      rw [hq]; exact minpoly.aeval ℚ_[p] x
    rwa [eval₂_map] at h0
  · intro h n
    have hxZ : IsIntegral ℤ_[p] x := h
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[p] hxZ, coeff_map,
      PadicInt.algebraMap_apply]
    exact PadicInt.norm_le_one _

theorem norm_le_one_iff_isIntegralElem_of_equiv (p : ℕ) [Fact p.Prime] {E O K : Type*} [Field E]
    [CommRing O] [NormedField K] [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    [Algebra E K] (ι : O →+* E) (e : ℚ_[p] →+* E) (ψ : ℤ_[p] ≃+* O)
    (hψ : ∀ z, ι (ψ z) = e (algebraMap ℤ_[p] ℚ_[p] z))
    (he : algebraMap ℚ_[p] K = (algebraMap E K).comp e) (x : K) :
    ‖x‖ ≤ 1 ↔ ((algebraMap E K).comp ι).IsIntegralElem x := by
  rw [norm_le_one_iff_isIntegralElem_padicInt p, ← isIntegralElem_comp_ringEquiv ψ]
  have : (algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p]) =
      ((algebraMap E K).comp ι).comp (ψ : ℤ_[p] →+* O) :=
    RingHom.ext fun z => by simp [he, hψ]
  rw [this]

theorem finiteDimensional_of_ringEquiv {E₁ E₂ L : Type*} [Field E₁] [Field E₂] [Field L]
    [Algebra E₁ L] [Algebra E₂ L] (e : E₂ ≃+* E₁)
    (he : algebraMap E₂ L = (algebraMap E₁ L).comp (e : E₂ →+* E₁)) [FiniteDimensional E₁ L] :
    FiniteDimensional E₂ L := by
  let : Algebra E₂ E₁ := (e : E₂ →+* E₁).toAlgebra
  have : IsScalarTower E₂ E₁ L := IsScalarTower.of_algebraMap_eq fun z => by rw [he]; rfl
  have : Module.Finite E₂ E₁ := Module.Finite.of_surjective (Algebra.linearMap E₂ E₁) e.surjective
  exact Module.Finite.trans E₁ L

def IntegralOnModelRat : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 ℚ) R] [Module.Flat (𝓞 ℚ) R]
    [Algebra.FiniteType (𝓞 ℚ) R] [IsIntegrallyClosed R] (r g : R) (s : 𝓞 ℚ),
    FourB.IntegralOnModel.Hyp ℚ R r g s → ∃ r' : R, r = algebraMap (𝓞 ℚ) R s * r'

theorem Normality.of_rat (hA : IntegralOnModelRat) : Normality.Statement := by
  intro A _ h a N ⟨hft, hdom, hic, htf, hh, hN, hint⟩
  let _ : Algebra (𝓞 ℚ) A :=
    ((Int.castRingHom A).comp (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)).toAlgebra
  have : IsDomain A := hdom
  have : Algebra.FiniteType (𝓞 ℚ) A := Algebra.FiniteType.of_restrictScalars_finiteType ℤ (𝓞 ℚ) A
  have hmap : ∀ c : 𝓞 ℚ, c ≠ 0 → algebraMap (𝓞 ℚ) A c ≠ 0 := fun c hc =>
    htf _ fun h0 => hc (Rat.ringOfIntegersEquiv.injective (by simpa using h0))
  have : Module.IsTorsionFree (𝓞 ℚ) A := ⟨fun c hc x y hxy => by
    have hc0 : c ≠ 0 := hc.ne_zero
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ (hmap c hc0) hxy⟩
  have hNQ : (N : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  suffices hH : FourB.IntegralOnModel.Hyp ℚ A a h (N : 𝓞 ℚ) by
    obtain ⟨r', hr'⟩ := hA A a h (N : 𝓞 ℚ) hH
    exact ⟨r', by rw [hr', map_natCast]⟩
  refine ⟨hNQ, hh, fun v L _ _ _ y _ hyint hyg => ?_⟩
  let P := primesEquiv v
  have : Fact (P : ℕ).Prime := ⟨P.2⟩
  let e : ℚ_[P] ≃+* v.adicCompletion ℚ := (adicCompletion.padicEquiv v).symm.toAlgEquiv.toRingEquiv
  let _ : Algebra ℚ_[P] L :=
    ((algebraMap (v.adicCompletion ℚ) L).comp (e : ℚ_[P] →+* v.adicCompletion ℚ)).toAlgebra
  have : FiniteDimensional ℚ_[P] L := finiteDimensional_of_ringEquiv e rfl
  have : Algebra.IsAlgebraic ℚ_[P] L := inferInstance
  let _ : NormedField L := spectralNorm.normedField ℚ_[P] L
  let _ : NormedAlgebra ℚ_[P] L := spectralNorm.normedAlgebra ℚ_[P] L
  have key : ∀ x : L, ‖x‖ ≤ 1 ↔ ((algebraMap (v.adicCompletion ℚ) L).comp
      (v.adicCompletionIntegers ℚ).subtype).IsIntegralElem x := fun x =>
    norm_le_one_iff_isIntegralElem_of_equiv (P : ℕ) (v.adicCompletionIntegers ℚ).subtype
      (e : ℚ_[P] →+* v.adicCompletion ℚ) (adicCompletionIntegers.padicIntEquiv v).symm.toAlgEquiv.toRingEquiv
      (fun z => adicCompletionIntegers.coe_padicIntEquiv_symm_apply v z) rfl x
  have hle := hint (P : ℕ) L y (fun b => (key _).2 (hyint b)) hyg
  rw [← key, map_natCast, map_natCast, norm_div]
  have hpos : 0 < ‖(N : L)‖ := by
    rw [← map_natCast (algebraMap ℚ_[P] L), norm_algebraMap', norm_pos_iff]
    exact_mod_cast hN.ne'
  exact (div_le_one hpos).2 hle

theorem Normality.of_integralOnModel (hA : FourB.IntegralOnModel.Statement) :
    Normality.Statement :=
  Normality.of_rat fun R _ _ _ _ _ _ r g s hH => hA ℚ R r g s hH

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.PDegreeRatio
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

theorem one_sub_prod_le_sum {ι : Type*} (s : Finset ι) (g h : ι → ℝ)
    (hg0 : ∀ i, 0 ≤ g i) (hg1 : ∀ i, g i ≤ 1) (hgh : ∀ i, 1 - g i ≤ h i) :
    1 - ∏ i ∈ s, g i ≤ ∑ i ∈ s, h i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hP0 : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg fun i _ => hg0 i
    have hP1 : ∏ i ∈ s, g i ≤ 1 := Finset.prod_le_one (fun i _ => hg0 i) fun i _ => hg1 i
    have key : 1 - g a * ∏ i ∈ s, g i = (1 - ∏ i ∈ s, g i) + (1 - g a) * ∏ i ∈ s, g i := by ring
    have h1 : (1 - g a) * ∏ i ∈ s, g i ≤ 1 - g a :=
      mul_le_of_le_one_right (by linarith [hg1 a]) hP1
    linarith [hgh a]

theorem raiseSmall_factor {f : ℕ} (N j' : ℕ) (x : Fin f → Fin N → ℝ) (δ : ℝ)
    (hx : ∀ τ (i l : Fin N), i < l → x τ l < x τ i) (τ : Fin f) (i l : Fin N) :
    (if i < l then raiseSmall N j' δ x τ i - raiseSmall N j' δ x τ l else 1) =
      (if i < l then x τ i - x τ l else 1) *
        (if Across N j' i l then 1 - δ / (x τ i - x τ l) else 1) := by
  by_cases hil : i < l
  · have hpos : 0 < x τ i - x τ l := sub_pos.mpr (hx τ i l hil)
    have hlt : i.val < l.val := hil
    simp only [if_pos hil, raiseSmall]
    by_cases hA : Across N j' i l
    · obtain ⟨h1, h2⟩ := hA
      have hi : ¬ N - j' ≤ i.val := by omega
      rw [if_neg hi, if_pos h2, if_pos (show Across N j' i l from ⟨h1, h2⟩)]
      field_simp
      ring
    · rw [if_neg hA, mul_one]
      simp only [Across, not_and, not_le] at hA
      by_cases hi : N - j' ≤ i.val
      · rw [if_pos hi, if_pos (show N - j' ≤ l.val by omega)]; ring
      · have hl := hA (by omega)
        rw [if_neg hi, if_neg (show ¬ N - j' ≤ l.val by omega)]
  · have hA : ¬ Across N j' i l := by
      rintro ⟨h1, h2⟩
      exact hil (Fin.lt_def.mpr (by omega))
    simp [hil, hA]

theorem DegreeRatio.proof : DegreeRatio.Statement := by
  intro f N j' x δ ⟨hδ, hx, hacross⟩
  set P : Fin f → Fin N → Fin N → ℝ :=
    fun τ i l => if Across N j' i l then 1 - δ / (x τ i - x τ l) else 1 with hPdef
  set H : Fin f → Fin N → Fin N → ℝ :=
    fun τ i l => if Across N j' i l then δ / (x τ i - x τ l) else 0 with hHdef

  have hfac : ∀ τ (i l : Fin N), 0 < (if i < l then x τ i - x τ l else 1) := by
    intro τ i l
    split_ifs with h
    · exact sub_pos.mpr (hx τ i l h)
    · exact one_pos
  have hdeg : 0 < weightDegree x :=
    Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l _ => hfac τ i l

  have hP0 : ∀ τ i l, 0 < P τ i l := by
    intro τ i l
    simp only [hPdef]
    split_ifs with hA
    · have hd := hacross τ i l hA
      have hpos : 0 < x τ i - x τ l := by linarith
      have : δ / (x τ i - x τ l) < 1 := (div_lt_one hpos).mpr hd
      linarith
    · exact one_pos
  have hP1 : ∀ τ i l, P τ i l ≤ 1 := by
    intro τ i l
    simp only [hPdef]
    split_ifs with hA
    · have hd := hacross τ i l hA
      have : 0 ≤ δ / (x τ i - x τ l) := div_nonneg hδ (by linarith)
      linarith
    · exact le_rfl
  have hPH : ∀ τ i l, 1 - P τ i l ≤ H τ i l := by
    intro τ i l
    simp only [hPdef, hHdef]
    split_ifs <;> simp

  have hratio : weightDegree (raiseSmall N j' δ x) / weightDegree x = ∏ τ, ∏ i, ∏ l, P τ i l := by
    rw [div_eq_iff hdeg.ne']
    simp only [weightDegree, raiseSmall_factor N j' x δ hx, Finset.prod_mul_distrib, hPdef]
    ring
  rw [hratio]
  have hin0 : ∀ τ i, 0 ≤ ∏ l, P τ i l := fun τ i => Finset.prod_nonneg fun l _ => (hP0 τ i l).le
  have hin1 : ∀ τ i, ∏ l, P τ i l ≤ 1 :=
    fun τ i => Finset.prod_le_one (fun l _ => (hP0 τ i l).le) fun l _ => hP1 τ i l
  have hmid0 : ∀ τ, 0 ≤ ∏ i, ∏ l, P τ i l := fun τ => Finset.prod_nonneg fun i _ => hin0 τ i
  have hmid1 : ∀ τ, ∏ i, ∏ l, P τ i l ≤ 1 :=
    fun τ => Finset.prod_le_one (fun i _ => hin0 τ i) fun i _ => hin1 τ i
  refine ⟨rfl, ?_, ?_, ?_⟩
  · exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Finset.prod_pos fun l _ => hP0 τ i l
  · exact Finset.prod_le_one (fun τ _ => hmid0 τ) fun τ _ => hmid1 τ
  · refine one_sub_prod_le_sum _ _ _ hmid0 hmid1 fun τ => ?_
    refine one_sub_prod_le_sum _ _ _ (hin0 τ) (hin1 τ) fun i => ?_
    exact one_sub_prod_le_sum _ _ _ (fun l => (hP0 τ i l).le) (hP1 τ i) (hPH τ i)

end GroundTheory.Heights₂.Heights.FourB
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.PFlagRootProduct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

theorem FlagRootProduct.rootPairing_eq_abs {N p : ℕ} {lam : Fin N → ℝ}
    (hd : IsSplitDominant N p lam) (q : LowerPair N) :
    rootPairing N p lam q = |lam q.1.1 - lam q.1.2| := by
  obtain ⟨⟨a, b⟩, hba⟩ := q
  have hba' : b.val < a.val := hba
  have ha := a.isLt
  have hb := b.isLt
  unfold rootPairing
  dsimp only
  by_cases h : b.val < p ∧ p ≤ a.val
  · rw [if_pos h]
    have hle : lam b ≤ lam a := hd a b (by
      unfold splitRank
      rw [if_pos h.2, if_neg (by omega)]
      omega)
    rw [abs_of_nonneg (by linarith)]
  · rw [if_neg h]
    have hle : lam a ≤ lam b := hd b a (by
      unfold splitRank
      split_ifs <;> omega)
    rw [abs_of_nonpos (by linarith)]
    ring

theorem FlagRootProduct.proof : FlagRootProduct.Statement := by
  intro N p lam hd
  have h := fun q => FlagRootProduct.rootPairing_eq_abs (N := N) (p := p) hd q
  exact ⟨h, Finset.prod_congr rfl fun q _ => h q⟩

end GroundTheory.Heights₂.Heights.FourB
end

