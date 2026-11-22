import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0006
import Formalism.LatticeRigidity.HeightMinimum.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductContinuousOnLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalCharacterSum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0041
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfAMemAdjoinLow
section
open GlobalTheory.SmoothForms

noncomputable section

open GlobalTheory.SmoothForms.PermWord

namespace GlobalTheory.SmoothForms.GelfGen

theorem exists_eig {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {n : ℕ} (Y : Matrix (Fin n) (Fin n) K) :
    ∃ l : Fin n → K, ∀ j : ℕ, (Y ^ j).trace = ∑ i, l i ^ j := by
  classical
  set f : Module.End K (Fin n → K) := Matrix.toLin' Y
  have htr : ∀ j, (Y ^ j).trace = ∑ μ ∈ (Formalism.SA.P.finite_eig f).toFinset,
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
    intro j
    rw [← Formalism.SA.P.trace_pow_eq_sum, ← Matrix.toLin'_pow, LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin n)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  set S := (Formalism.SA.P.finite_eig f).toFinset
  let d : K → ℕ := fun μ => Module.finrank K (f.maxGenEigenspace μ)
  let σ := Σ μ : S, Fin (d μ)
  have hsum : ∀ j, ∑ x : σ, (x.1 : K) ^ j = (Y ^ j).trace := by
    intro j
    rw [htr, Fintype.sum_sigma, ← Finset.sum_coe_sort S]
    simp [d]
  have hcard : Fintype.card σ = n := by
    have := hsum 0
    simp at this
    exact_mod_cast this
  let e := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨fun i => ((e i).1 : K), fun j => by rw [← hsum, ← e.sum_comp]⟩

theorem newton_closure {K : Type} [Field K] [Algebra ℂ K] {n : ℕ} (l : Fin n → K) (P : ℕ → K → Prop)
    (h1 : P 0 1) (h0 : ∀ j, P j 0) (hadd : ∀ j x y, P j x → P j y → P j (x + y))
    (hsmul : ∀ j (c : ℂ) x, P j x → P j (c • x)) (hmul : ∀ i j x y, P i x → P j y → P (i + j) (x * y))
    (hbase : ∀ j, 1 ≤ j → j ≤ n → P j (∑ i, l i ^ j)) : ∀ j, 1 ≤ j → P j (∑ i, l i ^ j) := by
  classical
  let Q : ℕ → MvPolynomial (Fin n) ℂ → Prop := fun j p => P j (MvPolynomial.aeval l p)
  have hps : ∀ j, MvPolynomial.aeval l (MvPolynomial.psum (Fin n) ℂ j) = ∑ i, l i ^ j := by
    intro j; simp [MvPolynomial.psum]
  have qadd : ∀ j x y, Q j x → Q j y → Q j (x + y) := fun j x y hx hy => by
    simpa [Q] using hadd j _ _ hx hy
  have qC : ∀ j (c : ℂ) x, Q j x → Q j (MvPolynomial.C c * x) := fun j c x hx => by
    rw [MvPolynomial.C_mul']; simpa [Q] using hsmul j c _ hx
  have qmul : ∀ i j x y, Q i x → Q j y → Q (i + j) (x * y) := fun i j x y hx hy => by
    simpa [Q] using hmul i j _ _ hx hy
  have qsign : ∀ j m x, Q j x → Q j ((-1) ^ m * x) := fun j m x hx => by
    have : ((-1 : MvPolynomial (Fin n) ℂ)) ^ m = MvPolynomial.C ((-1) ^ m) := by simp
    rw [this]; exact qC j _ x hx
  have qsub : ∀ j x y, Q j x → Q j y → Q j (x - y) := fun j x y hx hy => by
    rw [sub_eq_add_neg, neg_eq_neg_one_mul, ← pow_one (-1 : MvPolynomial (Fin n) ℂ)]
    exact qadd j _ _ hx (qsign j 1 y hy)
  have qsum : ∀ j (s : Finset (ℕ × ℕ)) (g : ℕ × ℕ → MvPolynomial (Fin n) ℂ), (∀ a ∈ s, Q j (g a)) →
      Q j (∑ a ∈ s, g a) := fun j s g hg =>
    Finset.sum_induction _ (Q j) (qadd j) (by simpa [Q] using h0 j) hg
  have qbase : ∀ j, 1 ≤ j → j ≤ n → Q j (MvPolynomial.psum (Fin n) ℂ j) := fun j h1 h2 => by
    simpa [Q, hps] using hbase j h1 h2
  have hesymm : ∀ k, Q k (MvPolynomial.esymm (Fin n) ℂ k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa [Q] using h1
      by_cases hkn : n < k
      · have : MvPolynomial.esymm (Fin n) ℂ k = 0 := by
          simp only [MvPolynomial.esymm]
          rw [Finset.powersetCard_eq_empty.2 (by rw [Finset.card_univ, Fintype.card_fin]; exact hkn), Finset.sum_empty]
        rw [this]; simpa [Q] using h0 k
      have hm := MvPolynomial.mul_esymm_eq_sum (Fin n) ℂ k
      have hQ : Q k ((k : MvPolynomial (Fin n) ℂ) * MvPolynomial.esymm (Fin n) ℂ k) := by
        rw [hm]
        refine qsign _ _ _ (qsum _ _ _ fun a ha => ?_)
        rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
        rw [mul_assoc]
        refine qsign _ _ _ ?_
        have := qmul _ _ _ _ (ih a.1 ha.2) (qbase a.2 (by omega) (by omega))
        rwa [ha.1] at this
      have := qC k ((k : ℂ)⁻¹) _ hQ
      rwa [← mul_assoc, ← map_natCast MvPolynomial.C k, ← map_mul,
        inv_mul_cancel₀ (by exact_mod_cast hk.ne'), map_one, one_mul] at this
  have hpsum : ∀ k, 1 ≤ k → Q k (MvPolynomial.psum (Fin n) ℂ k) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      by_cases hkn : k ≤ n
      · exact qbase k hk hkn
      rw [MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin n) ℂ k (by omega)]
      refine qsub _ _ _ ?_ (qsum _ _ _ fun a ha => ?_)
      · rw [mul_assoc, ← map_natCast MvPolynomial.C k]
        exact qsign _ _ _ (qC _ _ _ (hesymm k))
      · rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Set.mem_Ioo] at ha
        rw [mul_assoc]
        refine qsign _ _ _ ?_
        have := qmul _ _ _ _ (hesymm a.1) (ih a.2 (by omega) (by omega))
        rwa [ha.1] at this
  intro j hj
  simpa [Q, hps] using hpsum j hj

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem trace_symb (E : Fin n → Fin n → A) (k : ℕ) :
    ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val),
      (((Matrix.of (gen n)) ^ (k + 1)).trace, c) ∈ symb E (k + 1) := by
  set C := Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val)
  let R := MvPolynomial (Fin n × Fin n) ℂ
  let K := AlgebraicClosure (FractionRing R)
  have hinj : Function.Injective (algebraMap R K) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) K]
    exact (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective _ _)
  obtain ⟨l, hl⟩ := exists_eig ((Matrix.of (gen n)).map (algebraMap R K))
  have htr : ∀ j, algebraMap R K ((Matrix.of (gen n)) ^ j).trace = ∑ i, l i ^ j := by
    intro j
    rw [← hl, ← Matrix.map_pow]
    simp [Matrix.trace, map_sum]
  let P : ℕ → K → Prop := fun j p => ∃ q : R, ∃ c ∈ C, algebraMap R K q = p ∧ (q, c) ∈ symb E j
  have key := newton_closure l P
    ⟨1, 1, one_mem _, map_one _, Submodule.subset_span ⟨[], rfl, by simp [wd]⟩⟩
    (fun j => ⟨0, 0, zero_mem _, map_zero _, zero_mem _⟩)
    (by
      rintro j _ _ ⟨q, c, hc, rfl, h⟩ ⟨q', c', hc', rfl, h'⟩
      exact ⟨q + q', c + c', add_mem hc hc', map_add _ _ _, by simpa using add_mem h h'⟩)
    (by
      rintro j a _ ⟨q, c, hc, rfl, h⟩
      refine ⟨a • q, a • c, Subalgebra.smul_mem _ hc a, ?_, by simpa using Submodule.smul_mem _ a h⟩
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def])
    (by
      rintro i j _ _ ⟨q, c, hc, rfl, h⟩ ⟨q', c', hc', rfl, h'⟩
      exact ⟨q * q', c * c', mul_mem hc hc', map_mul _ _ _, by simpa using symb_mul E h h'⟩)
    (by
      intro j hj1 hjn
      obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      refine ⟨_, gelfA E k, Algebra.subset_adjoin ⟨⟨k, by omega⟩, rfl⟩, htr _, ?_⟩
      rw [trace_pow_eq]
      unfold gelfA
      exact sum_mem_symb E (fun idx : Fin (k + 1) → Fin n => idx) fun idx a => idx (a + 1))
    (k + 1) (by omega)
  obtain ⟨q, c, hc, hq, h⟩ := key
  rw [← htr] at hq
  rw [hinj hq] at h
  exact ⟨c, hc, h⟩

theorem exists_symb_low (E : Fin n → Fin n → A) (d : ℕ)
    (π : Equiv.Perm (Fin d)) : ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val),
      (∑ K : Fin d → Fin n, (List.ofFn fun a => gen n (K (π a)) (K a)).prod, c) ∈ symb E d := by
  have key := perm_sum_mem (Matrix.of (gen n))
    (fun j p => ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val), (p, c) ∈ symb E j)
    ⟨1, one_mem _, Submodule.subset_span ⟨[], rfl, by simp [wd]⟩⟩
    (by
      rintro k j p ⟨c, hc, h⟩
      obtain ⟨c', hc', h'⟩ := trace_symb E k
      exact ⟨c' * c, mul_mem hc' hc, by rw [← Prod.mk_mul_mk]; exact symb_mul E h' h⟩)
    d π (fun _ => 0)
  simp only [zero_add, pow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
    Matrix.of_apply] at key
  simp only [List.prod_ofFn]
  exact key

theorem permWord_low {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) (d : ℕ) (π : Equiv.Perm (Fin d)) :
    ∃ c ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val),
      wordMap E d (permMat n d π) - c ∈ filt E d := by
  obtain ⟨c, hc, h⟩ := exists_symb_low E d π
  refine ⟨c, hc, shorter_le_filt E d ?_⟩
  have h2 := symb_sub hE (sum_mem_symb E (fun (K : Fin d → Fin n) a => K (π a)) fun K => K)
  have h1 := symb_sub hE h
  have h3 := sub_mem h2 h1
  rw [sub_sub_sub_cancel_right] at h3
  rw [wordMap_permMat]
  exact h3

theorem low_le (E : Fin n → Fin n → A) :
    Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) ≤ Algebra.adjoin ℂ (Set.range (gelfA E)) :=
  Algebra.adjoin_mono (by rintro _ ⟨k, rfl⟩; exact ⟨k.val, rfl⟩)

theorem central_of_filt_low {E : Fin n → Fin n → A} (hE : Formalism.REAL.GlRel E) (d : ℕ) :
    ∀ z ∈ filt E d, (∀ a b, E a b * z = z * E a b) →
      z ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) := by
  induction d with
  | zero =>
    intro z hz _
    have : filt E 0 ≤ ⊥ := iSup₂_le fun k hk => absurd hk (Nat.not_lt_zero k)
    rw [(Submodule.mem_bot ℂ).1 (this hz)]
    exact zero_mem _
  | succ d ih =>
    intro z hz hc
    obtain ⟨_, ⟨M, rfl⟩, y, hy, rfl⟩ := Submodule.mem_sup.1 (filt_succ d hz)
    obtain ⟨M₀, h1, h2⟩ := GlobalTheory.T.commutant_lift_mod_stable_selfAdjoint _ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2)
      ((filt E d).comap (wordMap E d))
      (by rintro _ ⟨p, rfl⟩; exact ⟨(p.2, p.1), (polar_conjTranspose d p.1 p.2).symm⟩)
      (by
        rintro _ ⟨p, rfl⟩ N hN
        rw [Submodule.mem_comap, ← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
        exact filt_ad hE d _ _ hN) M
      (by
        rintro _ ⟨p, rfl⟩
        rw [Submodule.mem_comap, ← GlobalTheory.T.commutator_glGenerator_tensorWordMapMatrixUnits A n E hE]
        have h3 := neg_mem (filt_ad hE d p.1 p.2 hy)
        have h4 := hc p.1 p.2
        rw [mul_add, add_mul] at h4
        convert h3 using 1
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, h4, add_comm])
    have h3 : M₀ ∈ Submodule.span ℂ (Set.range (permMat n d)) := by
      refine GlobalTheory.T.bicommutant_tensorFactorPerm_mem_span n d M₀ fun T hT => ?_
      have : Algebra.adjoin ℂ (Set.range fun p : Fin n × Fin n => polar n d p.1 p.2) ≤
          Subalgebra.centralizer ℂ {M₀} := by
        refine Algebra.adjoin_le ?_
        rintro x hx _ rfl
        exact (h2 x hx).symm
      exact this (GlobalTheory.T.mem_adjoin_glAction_of_commute_tensorPerm n d T hT) _ rfl
    have h4 : Submodule.span ℂ (Set.range (permMat n d)) ≤
        (Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val)) ⊔
          filt E d).comap (wordMap E d) := by
      rw [Submodule.span_le]
      rintro _ ⟨π, rfl⟩
      obtain ⟨c, hc1, hc2⟩ := permWord_low hE d π
      exact Submodule.mem_sup.2 ⟨c, hc1, _, hc2, by abel⟩
    obtain ⟨c, hc1, u, hu, hcu⟩ := Submodule.mem_sup.1 (h4 h3)
    have h5 : wordMap E d M + y - c ∈ filt E d := by
      have h6 : wordMap E d (M - M₀) ∈ filt E d := h1
      have := add_mem (add_mem h6 hu) hy
      convert this using 1
      rw [map_sub, ← hcu]; abel
    have h7 := ih _ h5 fun a b => by
      rw [mul_sub, sub_mul, hc, gelf_adjoin_comm hE (low_le E hc1)]
    simpa using add_mem h7 hc1

theorem gelfA_mem_filt (E : Fin n → Fin n → A) (m : ℕ) : gelfA E m ∈ filt E (m + 2) := by
  refine shorter_le_filt E _ (Submodule.sum_mem _ fun idx _ => ?_)
  rw [← wd_ofFn E (fun a : Fin (m + 1) => idx a) fun a => idx (a + 1)]
  exact wd_mem_shorter E (by simp)

end GlobalTheory.SmoothForms.GelfGen

theorem GlobalTheory.SmoothForms.gelfA_mem_adjoin_low : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A),
    Formalism.REAL.GlRel E → ∀ m : ℕ, gelfA E m ∈ Algebra.adjoin ℂ (Set.range fun k : Fin n => gelfA E k.val) := by
  intro A _ _ n E hE m
  exact GlobalTheory.SmoothForms.GelfGen.central_of_filt_low hE (m + 2) _ (GlobalTheory.SmoothForms.GelfGen.gelfA_mem_filt E m)
    (GlobalTheory.T.commute_gelfandInvariantMatrixUnits_of_glRel A n E hE m)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductContinuousOnLatticeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianEichlerProduct_continuous_on_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (X u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (he : ∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) (Λ : Submodule L.O (Fin N → E)) (hΛ : IsLat L Λ) (c : Fˣ), ∃ d : Fˣ, ∀ (u' : Fin r → Fin N → E) (s' : Fin r → E) (e' : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i v, e' i v = eich L Hm (X i) (u' i) (s' i) v) → (∀ i j, ∃ o ∈ L.O, u' i j - u i j = algebraMap F E d * o) → (∀ i, ∃ o ∈ L.O, s' i - s i = algebraMap F E d * o) → ∀ x ∈ Λ, ∃ y ∈ Λ, ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x = algebraMap F E c • y := by
  first | exact @GlobalTheory.HL.EichCont.prod_eich_cont | exact GlobalTheory.HL.EichCont.prod_eich_cont | (intros; apply GlobalTheory.HL.EichCont.prod_eich_cont <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerDataStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFramePairCoordinates_transport_innerData : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : Coord P S), Function.Injective c.dat ∧ (∀ g ∈ P.UW0, ∀ d d', LocNG.Datum.Moves g d d' ↔ c.grp g • c.dat d = c.dat d') ∧ (∀ d d', LocNG.Datum.Rel d d' ↔ ∃ h ∈ S.H0, h • c.dat d = c.dat d') ∧ (∀ d g, g ∈ LocNG.Datum.Stab d ↔ c.grp g ∈ S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) ∧ ∀ d0 d, LocNG.Datum.wt d0 d = invVol (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d0)) (S.H0 ⊓ MulAction.stabilizer S.GLV (c.dat d)) := by
  first | exact @GlobalTheory.HL.CoordDatum.transport | exact GlobalTheory.HL.CoordDatum.transport | (intros; apply GlobalTheory.HL.CoordDatum.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalCharacterSumStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_local_character_sum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ψ : AddChar F ℂ), (∀ x : F, ‖ψ x‖ = 1) → (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) → ∀ (UU : Submodule L.O (Fin n → E)), (∀ x ∈ UU, ∀ y ∈ UU, hf L Hm x y ∈ L.O) → ∀ (ρ : ℕ) (e : Fin ρ → Fin n → E), (∀ a, e a ∈ UU) → (∀ a b, hf L Hm (e a) (e b) = if a = b then 1 else 0) → ∀ (π : E) (j N : ℕ), π ∈ L.O → π * L.cj π = algebraMap F E ((ϖ : F) ^ j) → (∃ c ∈ L.O, algebraMap F E ((ϖ : F) ^ N) = π * c) → ∀ (R : Finset (Fin n → E)) (nrm : (Fin n → E) → F), (∀ u, algebraMap F E (nrm u) = hf L Hm u u) → (∀ u ∈ R, u ∈ UU) → (∀ u ∈ UU, ∃! w, w ∈ R ∧ ∃ y ∈ UU, u - w = algebraMap F E ((ϖ : F) ^ N) • y) → ((R.filter fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c).card : ℝ) = (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) ∧ ∀ (i : ℕ), i ≤ N → ∀ (t : F) (u₀ : (𝒪[F])ˣ), t * (ϖ : F) ^ i = ((u₀ : 𝒪[F]) : F) → ‖∑ u ∈ R.filter (fun u => ∀ a, ∃ c ∈ L.O, hf L Hm u (e a) = π * c), ψ (t * nrm u)‖ ≤ (R.card : ℝ) * (resQ ϖ : ℝ) ^ (-(j * ρ : ℤ)) * (resQ ϖ : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ)) := by
  first | exact @GlobalTheory.HL.DivisibleGauss.share_and_gauss_sum | exact GlobalTheory.HL.DivisibleGauss.share_and_gauss_sum | (intros; apply GlobalTheory.HL.DivisibleGauss.share_and_gauss_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralEqMeanOverRepresentativesStatement
section
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexMeasureIntegral_eq_mean_over_representatives : ∀ {W : Type} [AddCommGroup W] (A B : AddSubgroup W) (φ : W → ℂ) (R : Finset W), B ≤ A → (∀ w, ∀ b ∈ B, φ (w + b) = φ w) → (∀ w, w ∉ A → φ w = 0) → (∀ w ∈ R, w ∈ A) → (∀ w ∈ A, ∃! x, x ∈ R ∧ w - x ∈ B) → Fine A φ B ∧ (R.card : ℕ) = B.relIndex A ∧ cint A φ = (∑ w ∈ R, φ w) / (R.card : ℂ) := by
  first | exact @GlobalTheory.IdxInt.cint_eq_mean_reps | exact GlobalTheory.IdxInt.cint_eq_mean_reps | (intros; apply GlobalTheory.IdxInt.cint_eq_mean_reps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralLinearPositiveNormBoundStatement
section
open GlobalTheory.IdxInt
open scoped Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound : ∀ {W : Type} [AddCommGroup W] (A : AddSubgroup W), (∀ φ ψ : W → ℂ, Nice A φ → Nice A ψ → Nice A (φ + ψ) ∧ cint A (φ + ψ) = cint A φ + cint A ψ ∧ ((∀ w, ‖φ w‖ ≤ (ψ w).re) → ‖cint A φ‖ ≤ (cint A ψ).re)) ∧ (∀ (c : ℂ) (φ : W → ℂ), Nice A φ → Nice A (fun w => c * φ w) ∧ cint A (fun w => c * φ w) = c * cint A φ) ∧ (∀ P : W → Prop, 0 ≤ (cint A (ind P)).re ∧ (cint A (ind P)).im = 0) ∧ ∀ (ι : Type) (s : Finset ι) (φ : ι → W → ℂ), (∀ i ∈ s, Nice A (φ i)) → Nice A (fun w => ∑ i ∈ s, φ i w) ∧ cint A (fun w => ∑ i ∈ s, φ i w) = ∑ i ∈ s, cint A (φ i) := by
  first | exact @GlobalTheory.IdxInt.Lin.main | exact GlobalTheory.IdxInt.Lin.main | (intros; apply GlobalTheory.IdxInt.Lin.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntCastIsUnitCompletionAlmostAllPlaces
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.PlacesInt

theorem intCast_isUnit_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (D : ℤ), D ≠ 0 → {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (D : (A.loc p).Fp)}.Finite := by
  intro F E _ _ _ _ _ sig A D hD
  have hDF : (D : F) ≠ 0 := Int.cast_ne_zero.2 hD
  refine (HeightOneSpectrum.Support.finite (𝓞 F) ((D : F)⁻¹)).subset fun p hp => ?_
  by_contra hs
  apply hp
  have hs' : p.valuation F ((D : F)⁻¹) ≤ 1 := by
    have := hs
    simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at this
    exact this
  have h1 : p.valuation F (D : F) ≤ 1 := by
    have := p.valuation_le_one (K := F) (D : 𝓞 F)
    simpa using this
  have m1 := ((integers_local A).2.2.1 (D : F) p).2 h1
  have m2 := ((integers_local A).2.2.1 ((D : F)⁻¹) p).2 hs'
  have hne : (A.loc p).ιF (D : F) ≠ 0 := by
    rw [map_ne_zero]; exact hDF
  refine ⟨⟨⟨_, m1⟩, ⟨_, m2⟩, ?_, ?_⟩, ?_⟩
  · apply Subtype.ext
    change (A.loc p).ιF (D : F) * (A.loc p).ιF ((D : F)⁻¹) = 1
    rw [← map_mul, mul_inv_cancel₀ hDF, map_one]
  · apply Subtype.ext
    change (A.loc p).ιF ((D : F)⁻¹) * (A.loc p).ιF (D : F) = 1
    rw [← map_mul, inv_mul_cancel₀ hDF, map_one]
  · change (A.loc p).ιF (D : F) = _
    exact map_intCast _ D

end GlobalTheory.HL.PlacesInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfIntegralAllQuadraticCompletions
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.GlueInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}

theorem nonempty_place' : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)⟩⟩

theorem nontrivial_Ep (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) : Nontrivial (A.loc p).Ep :=
  Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)

theorem sig_sig (A : Places F E sig) (y : E) : sig (sig y) = y := by
  obtain ⟨p⟩ := nonempty_place' (F := F)
  haveI := nontrivial_Ep A p
  apply (A.loc p).ιE.injective
  rw [← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]

theorem sig_ne_id (A : Places F E sig) : ¬ ∀ y, sig y = y := by
  intro h
  obtain ⟨p⟩ := nonempty_place' (F := F)
  have hcj : (A.L p).cj.toLinearMap = LinearMap.id :=
    LinearMap.ext_on_range (A.loc p).span fun y => by
      simp [A.L_cj, (A.loc p).cj_ιE, h]
  have hall : ∀ z : (A.loc p).Ep, ∃ c : (A.loc p).Fp, c • (1 : (A.loc p).Ep) = z := fun z => by
    obtain ⟨a, ha⟩ := ((A.L p).cj_fix z).1 (by simpa using LinearMap.congr_fun hcj z)
    exact ⟨a, by rw [← ha, Algebra.algebraMap_eq_smul_one]⟩
  have := finrank_le_one (1 : (A.loc p).Ep) hall
  rw [(A.loc p).rank] at this
  norm_num at this

theorem fix_mem (A : Places F E sig) (s : E) (hs : sig s = s) : ∃ t : F, algebraMap F E t = s := by
  by_contra hno
  push_neg at hno
  apply sig_ne_id A
  have hli : LinearIndependent F ![(1 : E), s] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      simp at hab
      exact ⟨hab, rfl⟩
    · exfalso
      have hb' : algebraMap F E b ≠ 0 := (map_ne_zero _).2 hb
      have hab' : algebraMap F E a + algebraMap F E b * s = 0 := by
        rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hab; exact hab
      apply hno (-a / b)
      rw [map_div₀, map_neg, div_eq_iff hb']
      linear_combination (-1 : E) * hab'
  have hspan : Submodule.span F (Set.range ![(1 : E), s]) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hli, A.quad]
    simp
  have hid : sig.toLinearMap = LinearMap.id :=
    LinearMap.ext_on_range hspan fun i => by
      fin_cases i <;> simp [hs]
  exact fun y => LinearMap.congr_fun hid y

theorem int_of_loc (A : Places F E sig) (t : F)
    (h : ∀ p, (A.loc p).ιE (algebraMap F E t) ∈ (A.L p).O) : t ∈ (algebraMap (𝓞 F) F).range := by
  apply HeightOneSpectrum.mem_integers_of_valuation_le_one
  intro p
  haveI := nontrivial_Ep A p
  have h1 := h p
  rw [(A.loc p).compat, (A.L p).O_def] at h1
  have h2 : IsIntegral 𝒪[(A.loc p).Fp] ((A.loc p).ιF t) :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(A.loc p).Fp] (A.loc p).Fp (A.loc p).Ep)
      (algebraMap (A.loc p).Fp (A.loc p).Ep).injective).1 h1
  have h3 := (Valuation.integer.integers (valuation (A.loc p).Fp)).mem_of_integral h2
  have h4 : (A.loc p).ιF t ≤ᵥ (A.loc p).ιF 1 := by
    rw [map_one]
    exact (Valuation.Compatible.vle_iff_le (v := valuation (A.loc p).Fp) _ _).2 (by rw [map_one]; exact (Valuation.mem_integer_iff _ _).1 h3)
  simpa using ((A.loc p).val t 1).1 h4

theorem sig_mem (A : Places F E sig) (y : E) (p : HeightOneSpectrum (𝓞 F))
    (hy : (A.loc p).ιE y ∈ (A.L p).O) : (A.loc p).ιE (sig y) ∈ (A.L p).O := by
  rw [← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).O_def]
  exact (((A.L p).O_def _).1 hy).map ((A.L p).cj.toAlgHom.restrictScalars 𝒪[(A.loc p).Fp])

theorem isIntegral_of_quadratic (y a b : E) (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b)
    (h : y ^ 2 - a * y + b = 0) : IsIntegral ℤ y := by
  have hR : IsIntegral (integralClosure ℤ E) y := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (⟨a, ha⟩ : integralClosure ℤ E) * Polynomial.X +
      Polynomial.C (⟨b, hb⟩ : integralClosure ℤ E), by monicity!, ?_⟩
    simpa [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul] using h
  exact isIntegral_trans y hR

end GlobalTheory.HL.GlueInt

open GlobalTheory.HL.GlueInt in

theorem GlobalTheory.HL.isIntegral_of_forall_mem_O : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (y : E), (∀ p, (A.loc p).ιE y ∈ (A.L p).O) →
    IsIntegral ℤ y := by
  intro F E _ _ _ _ _ sig A y hy
  obtain ⟨a, ha⟩ := fix_mem A (y + sig y) (by rw [map_add, sig_sig A, add_comm])
  obtain ⟨b, hb⟩ := fix_mem A (y * sig y) (by rw [map_mul, sig_sig A, mul_comm])
  obtain ⟨a0, rfl⟩ := int_of_loc A a fun p => by
    rw [ha, map_add]; exact (A.L p).O.add_mem (hy p) (sig_mem A y p (hy p))
  obtain ⟨b0, rfl⟩ := int_of_loc A b fun p => by
    rw [hb, map_mul]; exact (A.L p).O.mul_mem (hy p) (sig_mem A y p (hy p))
  refine isIntegral_of_quadratic y _ _ ((RingOfIntegers.isIntegral_coe a0).map (algebraMap F E).toIntAlgHom)
    ((RingOfIntegers.isIntegral_coe b0).map (algebraMap F E).toIntAlgHom) ?_
  change y ^ 2 - algebraMap F E (algebraMap (𝓞 F) F a0) * y + algebraMap F E (algebraMap (𝓞 F) F b0) = 0
  rw [ha, hb]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeOfSqueezedBetweenNatMultiples
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.glue_latt_isLattice {E : Type} [Field E] [NumberField E] (n : ℕ) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (hN : N ≠ 0)
    (hlow : ∀ x : Fin n → E, (∀ i, IsIntegral ℤ (x i)) → (N : E) • x ∈ Γ)
    (hup : ∀ x ∈ Γ, ∀ i, IsIntegral ℤ ((N : E) * x i)) : Submodule.IsLattice E Γ := by
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let f : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) :=
    ((N : E)⁻¹ • (LinearMap.pi fun i => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i)))
  have hle : Γ ≤ LinearMap.range f := by
    intro x hx
    refine ⟨fun i => ⟨(N : E) * x i, hup x hx i⟩, ?_⟩
    ext i
    change (N : E)⁻¹ * ((N : E) * x i) = x i
    rw [← mul_assoc, inv_mul_cancel₀ hNE, one_mul]
  refine ⟨?_, ?_⟩
  · rw [← Submodule.map_comap_eq_self hle]
    exact (IsNoetherian.noetherian _).map f
  · rw [eq_top_iff]
    intro y _
    rw [pi_eq_sum_univ y]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hmem : (N : E) • (fun j => if i = j then (1 : E) else 0) ∈ Γ := by
      apply hlow
      intro j
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    have : (fun j => if i = j then (1 : E) else 0) = (N : E)⁻¹ • ((N : E) • (fun j => if i = j then (1 : E) else 0)) := by
      rw [smul_smul, inv_mul_cancel₀ hNE, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
end

