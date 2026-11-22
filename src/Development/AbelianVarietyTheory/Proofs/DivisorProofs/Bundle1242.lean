import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TotalDegreeBindLeOfLinear
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1203
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankReducedLetterMatrixEqRankModMaximal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyAveragesFiniteWeightStableSubspace
section
noncomputable section

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap
open Formalism.REAL (KG toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev)

namespace GlobalTheory.PsCo.PcEF

theorem polyAverages_finiteWeightStableSubspace : PolyAvg := by
  classical
  intro n ε d
  set Wm : Set (Fin n → ℝ) := wtM '' {m : EntIdx n →₀ ℕ | (m.sum fun _ e => e) ≤ d}
  refine ⟨Wm, (finite_monomials_of_degree_le d).image _, fun H _ _ _ σ hσ u => ?_⟩
  have hemb : Topology.IsEmbedding (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) :=
    (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  set φ : Formalism.REAL.KG ε → Matrix (Fin n) (Fin n) ℂ := fun k => Formalism.REAL.toMK k with hφdef
  have hφc : Continuous φ := hemb.continuous
  have hφK : ∀ g, φ g ∈ Kset ε := fun g => g.2
  have hφ1 : φ 1 = 1 := rfl
  have hφm : ∀ a b, φ (a * b) = φ a * φ b := fun a b => rfl
  have hφs : ∀ m ∈ Kset ε, ∃ g, φ g = m := by
    intro m hm
    have : m ∈ Set.range (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) := by
      rw [Formalism.REAL.range_toMK]
      exact hm
    obtain ⟨g, hg⟩ := this
    exact ⟨g, hg⟩
  have hinUJ : ∀ g, φ g ∈ UJset ε := fun g => smd_inUJ_of_Kset (hφK g)
  have horb : ∀ u : H, Continuous fun k => σ (φ k) u := fun u => (hσ.2.2 u).comp_continuous hφc hinUJ
  have hentc : Continuous fun k => entVar (φ k) := by
    refine continuous_pi fun i => ?_
    rcases i with x | x
    · exact (continuous_apply x.2).comp ((continuous_apply x.1).comp hφc)
    · exact continuous_star.comp ((continuous_apply x.2).comp ((continuous_apply x.1).comp hφc))
  have hpolyc : ∀ Q : MvPolynomial (EntIdx n) ℂ, Continuous fun k => eval (entVar (φ k)) Q :=
    fun Q => (MvPolynomial.continuous_eval Q).comp hentc
  have hint : ∀ (Q : MvPolynomial (EntIdx n) ℂ) (u : H),
      Integrable (fun k => eval (entVar (φ k)) Q • σ (φ k) u) (muK ε) := fun Q u =>
    ((hpolyc Q).smul (horb u)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let Xu : H → MvPolynomial (EntIdx n) ℂ →ₗ[ℂ] H := fun u =>
    { toFun := fun Q => ∫ k, eval (entVar (φ k)) Q • σ (φ k) u ∂(muK ε)
      map_add' := fun Q R => by
        simp only [map_add, add_smul]
        exact integral_add (hint Q u) (hint R u)
      map_smul' := fun c Q => by
        simp only [smul_eval, mul_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have hXu : ∀ u Q, Xu u Q = ∫ k, eval (entVar (φ k)) Q • σ (φ k) u ∂(muK ε) := fun _ _ => rfl
  have htr : ∀ u Q g, σ (φ g) (Xu u Q) = Xu u (bind₁ (trF (φ g⁻¹)) Q) := by
    intro u Q g
    rw [hXu, hXu, ← (σ (φ g)).integral_comp_comm (hint Q u)]
    have e2 : ∫ k, σ (φ g) (eval (entVar (φ k)) Q • σ (φ k) u) ∂(muK ε) =
        ∫ k, eval (entVar (φ (g⁻¹ * (g * k)))) Q • σ (φ (g * k)) u ∂(muK ε) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [map_smul, inv_mul_cancel_left]
      rw [hφm g k, hσ.1.2 _ (hinUJ g) _ (hinUJ k)]
      rfl
    rw [e2, integral_mul_left_eq_self (fun k => eval (entVar (φ (g⁻¹ * k))) Q • σ (φ k) u) g]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hφm, eval_mul_eq_bind₁]
  have hmono : ∀ (u : H) (m : EntIdx n →₀ ℕ),
      Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ (wtM m) (Xu u (monomial m 1)) := by
    intro u m θ hθ
    rw [mir_Kset_eq] at hθ
    obtain ⟨g, hg⟩ := hφs _ hθ
    have hginv : φ g⁻¹ = star (φ g) := by
      have h1 : φ g * star (φ g) = 1 := Unitary.mul_star_self_of_mem (hφK g).1
      calc φ g⁻¹ = φ g⁻¹ * (φ g * star (φ g)) := by rw [h1, Matrix.mul_one]
        _ = star (φ g) := by rw [← Matrix.mul_assoc, ← hφm, inv_mul_cancel, hφ1, Matrix.one_mul]
    rw [← hg, htr, hXu, hXu, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [← eval_mul_eq_bind₁, hginv, hg, show Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) =
      dTor θ from rfl, eval_monomial_tor, mul_smul]
  let Sd : Submodule ℂ H := (restrictTotalDegree (EntIdx n) ℂ d).map (Xu u)
  refine ⟨Sd, Module.Finite.map _ _, ?_, ?_, ?_⟩
  · intro k hk x hx
    rw [mir_Kset_eq] at hk
    obtain ⟨g, rfl⟩ := hφs k hk
    obtain ⟨Q, hQ, rfl⟩ := hx
    rw [htr]
    refine Submodule.mem_map_of_mem ?_
    rw [SetLike.mem_coe, mem_restrictTotalDegree] at hQ
    rw [mem_restrictTotalDegree]
    exact (totalDegree_bind_le_of_linear _ (trF_totalDegree _) Q).trans hQ
  · intro P hP
    exact Submodule.mem_map_of_mem ((mem_restrictTotalDegree _ _ P).2 hP)
  · rintro μ s ⟨Q, hQ, rfl⟩ hs0 hsw
    by_contra hμ
    rw [SetLike.mem_coe, mem_restrictTotalDegree] at hQ
    have hsum : Xu u Q = ∑ m ∈ Q.support, coeff m Q • Xu u (monomial m 1) := by
      conv_lhs => rw [Q.as_sum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← map_smul, smul_monomial, smul_eq_mul, mul_one]
    have horth : ∀ m ∈ Q.support, inner ℂ (Xu u Q) (Xu u (monomial m 1)) = 0 := by
      intro m hm
      refine kfin_wt_orth hσ hsw (hmono u m) fun h => hμ ?_
      exact ⟨m, (le_totalDegree hm).trans hQ, h.symm⟩
    apply hs0
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    calc inner ℂ (Xu u Q) (Xu u Q) = inner ℂ (Xu u Q) (∑ m ∈ Q.support, coeff m Q • Xu u (monomial m 1)) := by
          rw [← hsum]
      _ = 0 := by
          rw [inner_sum]
          exact Finset.sum_eq_zero fun m hm => by rw [inner_smul_right, horth m hm, mul_zero]

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceGLConjMaxCompactIff
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.CongConj

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {m : ℕ}

theorem v_le_one_of_mem_KGL {c : GLw m w} (hc : c ∈ GlobalTheory.LFun.KGL w m) (i j : Fin m) :
    Valued.v (c.val i j) ≤ 1 := by
  obtain ⟨a, rfl⟩ := hc
  exact (a.val i j).2

theorem v_mul_left_le {A B : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {γ : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ 1) (hB : ∀ i j, Valued.v (B i j) ≤ γ) (i j : Fin m) :
    Valued.v ((A * B) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le (hA i l) (hB l j)

theorem v_mul_right_le {A B : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {γ : WithZero (Multiplicative ℤ)}
    (hA : ∀ i j, Valued.v (A i j) ≤ γ) (hB : ∀ i j, Valued.v (B i j) ≤ 1) (i j : Fin m) :
    Valued.v ((A * B) i j) ≤ γ := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact mul_le_of_le_of_le_one (hA i l) (hB l j)

theorem conj_imp (k : ℕ) {c N : GLw m w} (hc : c ∈ GlobalTheory.LFun.KGL w m)
    (hN : N ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v (N.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(k : ℤ))) :
    c⁻¹ * N * c ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v ((c⁻¹ * N * c).val i j -
      (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)) := by
  refine ⟨mul_mem (mul_mem (inv_mem hc) hN.1) hc, fun i j => ?_⟩
  have hid : (c⁻¹ * N * c).val - 1 = (c⁻¹).val * (N.val - 1) * c.val := by
    have h1 : (c⁻¹).val * c.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have := v_mul_right_le (v_mul_left_le (B := N.val - 1) (v_le_one_of_mem_KGL (inv_mem hc)) (fun a b => by
    rw [Matrix.sub_apply]; exact hN.2 a b)) (v_le_one_of_mem_KGL hc) i j
  rw [← hid, Matrix.sub_apply] at this
  exact this

end GlobalTheory.CongConj

theorem GlobalTheory.congConj_iff : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (m k : ℕ) (c N : GLw m w), c ∈ GlobalTheory.LFun.KGL w m → ((c⁻¹ * N * c ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v ((c⁻¹ * N * c).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ (N ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v (N.val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ)))) := by
  intro E _ _ w m k c N hc
  constructor
  · intro h
    have h2 := GlobalTheory.CongConj.conj_imp k (inv_mem hc) h
    simpa [mul_assoc] using h2
  · exact GlobalTheory.CongConj.conj_imp k hc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLevelIffLatticeStable
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat.Lv

open IsDedekindDomain.HeightOneSpectrum

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

def col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j : Fin m) : B.A := ∑ i, e.symm (Z i j) • b i

theorem repr_col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j i : Fin m) :
    b.repr (col e b Z j) i = e.symm (Z i j) := by
  rw [col, Module.Basis.repr_sum_self]

theorem repr_sum_smul_col (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (c : Fin m → K.E) (i : Fin m) :
    b.repr (∑ l, c l • col e b Z l) i = e.symm ((Z *ᵥ fun l => e (c l)) i) := by
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, repr_col,
    smul_eq_mul, Matrix.mulVec, dotProduct, map_mul, RingEquiv.symm_apply_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem mul_col (a : B.A) (Z : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (j : Fin m) :
    a * col e b Z j = col e b (GlobalTheory.TwLat.mulMat e b a * Z) j := by
  apply b.repr.injective
  ext i
  rw [repr_col]
  have h2 := congrFun (LinearMap.toMatrix_mulVec_repr b b (LinearMap.mulLeft K.E a) (col e b Z j)) i
  simp only [LinearMap.mulLeft_apply] at h2
  rw [← h2]
  simp only [Matrix.mulVec, dotProduct, GlobalTheory.TwLat.mulMat, Matrix.mul_apply, Matrix.map_apply, repr_col, map_sum,
    map_mul, RingEquiv.symm_apply_apply]

theorem mulMat_one_add (t : K.E) (x : B.A) :
    GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.E B.A t * x) = 1 + e t • GlobalTheory.TwLat.mulMat e b x := by
  ext i j
  simp only [GlobalTheory.TwLat.mulMat, Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, add_mul, one_mul,
    mul_assoc, ← Algebra.smul_def, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, map_mul,
    Matrix.add_apply, Matrix.smul_apply, Module.Basis.repr_self, Matrix.one_apply, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem sum_smul_col_inj (g : GLw m w) (c c' : Fin m → K.E)
    (h : ∑ l, c l • col e b g.val l = ∑ l, c' l • col e b g.val l) : c = c' := by
  have h1 : g.val *ᵥ (fun l => e (c l)) = g.val *ᵥ (fun l => e (c' l)) := by
    funext i
    have := congrArg (fun x => b.repr x i) h
    simp only [repr_sum_smul_col] at this
    exact e.symm.injective this
  have h2 := congrArg (fun v => (g⁻¹).val *ᵥ v) h1
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at h2
  funext l
  exact e.injective (congrFun h2 l)

theorem mul_le_self_iff (a b : WithZero (Multiplicative ℤ)) (ha : a ≠ 0) : a * b ≤ a ↔ b ≤ 1 := by
  constructor
  · intro h
    have : a⁻¹ * (a * b) ≤ a⁻¹ * a := by gcongr
    rwa [← mul_assoc, inv_mul_cancel₀ ha, one_mul] at this
  · intro h
    exact mul_le_of_le_one_right' h

end GlobalTheory.TwLat.Lv

namespace GlobalTheory.TwLat.Lv

open IsDedekindDomain.HeightOneSpectrum

theorem valued_uniformizerPower_completion_eq_exp_neg {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
    (e : K.E ≃+* w.adicCompletion E) (hval : ∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) (t : K.O) (k : ℕ)
    (ht : t ≠ 0) (hk : GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k) :
    Valued.v (e (algebraMap K.O K.E t)) = WithZero.exp (-(k : ℤ)) := by
  have hne : e (algebraMap K.O K.E t) ≠ 0 := by
    intro h
    apply ht
    have h1 : algebraMap K.O K.E t = 0 := e.injective (h.trans (map_zero e).symm)
    exact IsFractionRing.injective K.O K.E (h1.trans (map_zero _).symm)
  have hv : Valued.v (e (algebraMap K.O K.E t)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hne
  rw [hval, ordL, dif_neg hv] at hk
  rw [← WithZero.coe_unzero hv, WithZero.exp]
  congr 1
  rw [← ofAdd_toAdd (WithZero.unzero hv)]
  congr 1
  omega

theorem level_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (t : K.O) (k : ℕ), K.Small t → GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k → ∀ g N : GLw m w, N.val = GlobalTheory.TwLat.mulMat e b (1 + algebraMap K.O B.A t * B.g) → ((g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w m ∧ ∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))) ↔ ∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) := by
  intro E _ _ _ _ w _ K e he hint hval B m b t k hs hk g N hN
  have hv := valued_uniformizerPower_completion_eq_exp_neg e hval t k hs.1 hk
  obtain ⟨c, hc⟩ : ∃ c, c = e (algebraMap K.O K.E t) := ⟨_, rfl⟩
  rw [← hc] at hv
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin m) (Fin m) (w.adicCompletion E),
      Y = (g⁻¹).val * GlobalTheory.TwLat.mulMat e b B.g * g.val := ⟨_, rfl⟩
  have hA : (g⁻¹ * N * g).val = 1 + c • Y := by
    rw [Units.val_mul, Units.val_mul, hN, IsScalarTower.algebraMap_apply K.O K.E B.A, mulMat_one_add, ← hc, hY,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one]
  have hent : ∀ i j, (g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j = c * Y i j := by
    intro i j
    rw [hA]
    simp
  have hexp : WithZero.exp (-(k : ℤ)) ≠ 0 := WithZero.exp_ne_zero
  have hcoef : (∀ i j, Valued.v ((g⁻¹ * N * g).val i j - (1 : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) ≤
      WithZero.exp (-(k : ℤ))) ↔ ∀ i j, Valued.v (Y i j) ≤ 1 := by
    simp only [hent, map_mul, hv]
    exact forall_congr' fun i => forall_congr' fun j => mul_le_self_iff _ _ hexp

  have hgY : g.val * Y = GlobalTheory.TwLat.mulMat e b B.g * g.val := by
    rw [hY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hgcol : ∀ j, B.g * col e b g.val j = ∑ l, e.symm (Y l j) • col e b g.val l := by
    intro j
    rw [mul_col, ← hgY]
    apply b.repr.injective
    ext i
    rw [repr_sum_smul_col, repr_col]
    simp only [RingEquiv.apply_symm_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply]
  have hlat : (∀ y ∈ GlobalTheory.TwLat.lat e b g, B.g * y ∈ GlobalTheory.TwLat.lat e b g) ↔ ∀ i j, Valued.v (Y i j) ≤ 1 := by
    constructor
    · intro hst i j
      have hmem : B.g * col e b g.val j ∈ GlobalTheory.TwLat.lat e b g :=
        hst _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun K.O).mp hmem
      have ho' : ∑ l, algebraMap K.O K.E (o l) • col e b g.val l = ∑ l, e.symm (Y l j) • col e b g.val l := by
        rw [← hgcol j, ← ho]
        exact Finset.sum_congr rfl fun l _ => algebraMap_smul K.E (o l) _
      have := congrFun (sum_smul_col_inj e b g _ _ ho') i
      have hi := (hint (algebraMap K.O K.E (o i))).mp ⟨o i, rfl⟩
      rw [this, RingEquiv.apply_symm_apply] at hi
      exact hi
    · intro hYi y hy
      have hle : GlobalTheory.TwLat.lat e b g ≤ (GlobalTheory.TwLat.lat e b g).comap (LinearMap.mulLeft K.O B.g) := by
        rw [GlobalTheory.TwLat.lat, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        show B.g * col e b g.val j ∈ GlobalTheory.TwLat.lat e b g
        rw [hgcol j]
        refine Submodule.sum_mem _ fun l _ => ?_
        obtain ⟨o, ho⟩ := (hint (e.symm (Y l j))).mpr (by rw [RingEquiv.apply_symm_apply]; exact hYi l j)
        rw [← ho, algebraMap_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
      exact hle hy

  have hK : (∀ i j, Valued.v (Y i j) ≤ 1) → g⁻¹ * N * g ∈ GlobalTheory.LFun.KGL w m := by
    intro hYi
    haveI : IsLocalRing (Ov E w) := inferInstanceAs (IsLocalRing (w.adicCompletionIntegers E))
    have hcS : c ∈ Ov E w := by
      show c ∈ w.adicCompletionIntegers E
      rw [mem_adicCompletionIntegers, hv]
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
    let c' : Ov E w := ⟨c, hcS⟩
    let Y' : Matrix (Fin m) (Fin m) (Ov E w) := fun i j =>
      ⟨Y i j, by show Y i j ∈ w.adicCompletionIntegers E; rw [mem_adicCompletionIntegers]; exact hYi i j⟩
    let A' : Matrix (Fin m) (Fin m) (Ov E w) := 1 + c' • Y'
    have hmap : A'.map (Ov E w).subtype = (g⁻¹ * N * g).val := by
      rw [hA]
      ext i j
      simp only [A', Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
        map_add, map_mul]
      split_ifs <;> simp [c', Y']
    have hc'nu : ¬ IsUnit c' := by
      rintro ⟨u, hu⟩
      have h1 : c * ((u⁻¹ : (Ov E w)ˣ) : Ov E w) = 1 := by
        have := congrArg Subtype.val (Units.mul_inv u)
        rw [hu] at this
        exact this
      obtain ⟨o, ho⟩ := (hint (e.symm ((u⁻¹ : (Ov E w)ˣ) : Ov E w))).mpr (by
        rw [RingEquiv.apply_symm_apply]
        exact (mem_adicCompletionIntegers _ _ _).mp ((u⁻¹ : (Ov E w)ˣ) : Ov E w).2)
      have h2 : algebraMap K.O K.E (t * o) = 1 := by
        apply e.injective
        rw [map_mul, map_mul, ho, RingEquiv.apply_symm_apply, ← hc, h1, map_one]
      have h3 : t * o = 1 := IsFractionRing.injective K.O K.E (h2.trans (map_one _).symm)
      exact (IsLocalRing.mem_maximalIdeal t).mp hs.2.1 ⟨⟨t, o, h3, by rw [mul_comm]; exact h3⟩, rfl⟩
    have hres0 : IsLocalRing.residue (Ov E w) c' = 0 :=
      (IsLocalRing.residue_eq_zero_iff c').mpr ((IsLocalRing.mem_maximalIdeal c').mpr hc'nu)
    have hdet : IsUnit A'.det := by
      apply (isUnit_map_iff (IsLocalRing.residue (Ov E w)) _).mp
      rw [RingHom.map_det]
      have : (IsLocalRing.residue (Ov E w)).mapMatrix A' = 1 := by
        ext i j
        simp [A', hres0, Matrix.one_apply]
      rw [this, Matrix.det_one]
      exact isUnit_one
    have hU : IsUnit A' := (Matrix.isUnit_iff_isUnit_det A').mpr hdet
    refine ⟨hU.unit, ?_⟩
    apply Units.ext
    rw [← hmap]
    rfl
  constructor
  · rintro ⟨-, h⟩
    exact hlat.2 (hcoef.1 h)
  · intro h
    have h' := hlat.1 h
    exact ⟨hK h', hcoef.2 h'⟩

end GlobalTheory.TwLat.Lv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAdjoinRootAlgebrasGeneratedByPair
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.KapLat

theorem fits_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K)
    (u₁ : B₁.A) (u₂ : B₂.A), (Q₁ * Q₂).Separable → Fits w e B₁ Q₁ u₁ → Fits w e B₂ Q₂ u₂ →
    Fits w e (B₁.prod B₂) (Q₁ * Q₂) ((u₁, u₂) : B₁.A × B₂.A) := by
  intro E _ _ _ w K e Q₁ Q₂ B₁ B₂ u₁ u₂ hsep h₁ h₂
  obtain ⟨ha₁, hr₁, hd₁, hs₁⟩ := h₁
  obtain ⟨ha₂, hr₂, hd₂, hs₂⟩ := h₂
  have hne : Q₁ * Q₂ ≠ 0 := hsep.ne_zero
  have hQ₁ : Q₁ ≠ 0 := left_ne_zero_of_mul hne
  have hQ₂ : Q₂ ≠ 0 := right_ne_zero_of_mul hne
  have hcop : IsCoprime (Q₁.map e.symm.toRingHom) (Q₂.map e.symm.toRingHom) :=
    hsep.isCoprime.map (Polynomial.mapRingHom e.symm.toRingHom)
  have hfst : ∀ p : K.E[X], (aeval ((u₁, u₂) : B₁.A × B₂.A) p).1 = aeval u₁ p := fun p => by
    simpa using (Polynomial.aeval_algHom_apply (AlgHom.fst K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) p).symm
  have hsnd : ∀ p : K.E[X], (aeval ((u₁, u₂) : B₁.A × B₂.A) p).2 = aeval u₂ p := fun p => by
    simpa using (Polynomial.aeval_algHom_apply (AlgHom.snd K.E B₁.A B₂.A) ((u₁, u₂) : B₁.A × B₂.A) p).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Algebra.adjoin K.E {((u₁, u₂) : B₁.A × B₂.A)} = ⊤
    obtain ⟨a, b, hab⟩ := hcop
    have e₁ : aeval u₁ b * aeval u₁ (Q₂.map e.symm.toRingHom) = 1 := by
      have := congrArg (aeval u₁) hab
      rw [map_add, map_mul, map_mul, hr₁, mul_zero, zero_add, map_one] at this
      exact this
    have e₂ : aeval u₂ a * aeval u₂ (Q₁.map e.symm.toRingHom) = 1 := by
      have := congrArg (aeval u₂) hab
      rw [map_add, map_mul, map_mul, hr₂, mul_zero, add_zero, map_one] at this
      exact this
    rw [eq_top_iff]
    rintro ⟨y, z⟩ -
    have hy : y ∈ (aeval u₁ : K.E[X] →ₐ[K.E] B₁.A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ha₁]; trivial
    have hz : z ∈ (aeval u₂ : K.E[X] →ₐ[K.E] B₂.A).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval, ha₂]; trivial
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨r, rfl⟩ := hz
    have key : ((aeval u₁ p, aeval u₂ r) : B₁.A × B₂.A) =
        aeval ((u₁, u₂) : B₁.A × B₂.A) (b * Q₂.map e.symm.toRingHom * p + a * Q₁.map e.symm.toRingHom * r) := by
      refine Prod.ext ?_ ?_
      · rw [hfst, map_add, map_mul, map_mul, map_mul, map_mul, hr₁, mul_zero, zero_mul, add_zero, e₁, one_mul]
      · rw [hsnd, map_add, map_mul, map_mul, map_mul, map_mul, hr₂, mul_zero, zero_mul, zero_add, e₂, one_mul]
    exact key ▸ Polynomial.aeval_mem_adjoin_singleton K.E _
  · show aeval ((u₁, u₂) : B₁.A × B₂.A) ((Q₁ * Q₂).map e.symm.toRingHom) = 0
    rw [Polynomial.map_mul]
    refine Prod.ext ?_ ?_
    · rw [hfst, map_mul, hr₁, zero_mul]; rfl
    · rw [hsnd, map_mul, hr₂, mul_zero]; rfl
  · show Module.finrank K.E (B₁.A × B₂.A) = (Q₁ * Q₂).natDegree
    rw [Module.finrank_prod, hd₁, hd₂, natDegree_mul hQ₁ hQ₂]
  · exact Prod.ext hs₁ hs₂

end GlobalTheory.KapLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupportStatement
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport : GlobalTheory.PsCo.Pc1.StShape := by
  first | exact @GlobalTheory.ShapeSmoothFinite.stShape | exact GlobalTheory.ShapeSmoothFinite.stShape | (intros; apply GlobalTheory.ShapeSmoothFinite.stShape <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorBaseLevelTwistedModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_goodProjector_baseLevel_twistedModel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → R.toRealDat.LUnif → ∀ i, LinearMap.range ((R.toCx3 F).w0C false i) = Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) ⊓ typeSubspace A3 (R.toCx3 F) i (R.gWx F i) F.P0 F.ψ0⁻¹ := by
  first | exact @GlobalTheory.WType.range_w0C_type | exact GlobalTheory.WType.range_w0C_type | (intros; apply GlobalTheory.WType.range_w0C_type <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankReducedLetterMatrixEqRankModMaximalStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_reduced_letter_matrix_eq_rank_mod_maximal : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL) (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' : ℕ) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(((HW l).W K 1 LL hA.2.2).N T')) (g : LatHom T.L T'.L) (A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n) (e : Module.Basis (Fin n) ↥(OL LL) ↥T.L.T) (e' : Module.Basis (Fin n') ↥(OL LL) ↥T'.L.T) (a : Mx ↥(OL LL) n' n), IsCrys ((D.loc l).PD K) T.ρ → IsCrys ((D.loc l).PD K) T'.ρ → IsMapMat ((HW l).W K 1 LL hA.2.2) g b b' A → (∀ k, g.f (e k : T.V) = ∑ m, ((a m k : ↥(OL LL)) : ↥LL.1) • (e' m : T'.V)) → ∀ i, lrank ((A i).map (PowerSeries.map (residue ↥(OL LL)))) = (a.map (residue ↥(OL LL))).rank := by
  first | exact @GlobalTheory.WachRank.main | exact GlobalTheory.WachRank.main | (intros; apply GlobalTheory.WachRank.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankResidueBasisMatrixSuccOfAdjoinVectorStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_residue_basis_matrix_succ_of_adjoin_vector : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (n : ℕ) (ϖ : O) (Ac As : Matrix (Fin n) (Fin n) O) (x : Fin n → O), Irreducible ϖ → (∀ y : Fin n → O, ∃ u, Ac *ᵥ u = fun a => ϖ * y a) → (∀ w, ∃ u c, As *ᵥ w = Ac *ᵥ u + fun a => c * x a) → (∃ w, As *ᵥ w = x) → (∀ u, ∃ w, As *ᵥ w = Ac *ᵥ u) → (¬ ∃ u, Ac *ᵥ u = x) → (As.map (residue O)).rank = (Ac.map (residue O)).rank + 1 := by
  first | exact @GlobalTheory.rank_residue_succ_of_adjoin | exact GlobalTheory.rank_residue_succ_of_adjoin | (intros; apply GlobalTheory.rank_residue_succ_of_adjoin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalHomHermitianTraceFormSelfEqFrameNormSumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalHomHermitianTraceForm_self_eq_frame_normSum : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.LatVac.hRat S T v v = ∑ a, ∑ b, star (((frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1) a b) * ((frT⁻¹ : GL (Fin T.rank) D.host.E).1 * v * frS.1) a b := by
  first | exact @GlobalTheory.HRatFrame.hRat_frame | exact GlobalTheory.HRatFrame.hRat_frame | (intros; apply GlobalTheory.HRatFrame.hRat_frame <;> assumption)
end

