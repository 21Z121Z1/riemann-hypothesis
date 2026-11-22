import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0373
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1328
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChiDetSplitCentre
section
noncomputable section

open NumberField MeasureTheory Matrix Polynomial Formalism.L2.Host
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspRep.Central
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.IdeleCovolume

namespace GlobalTheory.CuspQuot

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def HasCuspImage (f : Sm E a) : Prop :=
  ∃ (W : Submodule ℂ (Sm E a)) (τ : CuspSub E a) (p : Sm E a →ₗ[ℂ] τ.V),
    f ∈ W ∧ IsStable W ∧ p f ≠ 0 ∧ ∀ (o : Op E a), ∀ g ∈ W, p (act o g) = τ.op o (p g)

theorem HasCuspImage.of_commute {Q : Module.End ℂ (Sm E a)} (hQ : ∀ o, Commute Q (act o)) {f : Sm E a}
    (h : HasCuspImage (Q f)) : HasCuspImage f := by
  obtain ⟨W, τ, p, h1, h2, h3, h4⟩ := h
  have e : ∀ o g, Q (act o g) = act o (Q g) := fun o g => LinearMap.congr_fun (hQ o).eq g
  refine ⟨W.comap Q, τ, p ∘ₗ Q, h1, fun o g hg => ?_, h3, fun o g hg => ?_⟩
  · change Q _ ∈ W
    rw [e]; exact h2 o _ hg
  · change p (Q _) = _
    rw [e]; exact h4 o _ hg

theorem HasCuspImage.mulChi {f : Sm E a} (h : HasCuspImage f) (χ : HChar E) : HasCuspImage (mulChi a χ f) := by
  obtain ⟨W, τ, p, h1, h2, h3, h4⟩ := h
  refine ⟨W.map (CuspRep.mulChi a χ).toLinearMap, τ.twist χ,
    (τ.toTwist χ).toLinearMap ∘ₗ p ∘ₗ (CuspRep.mulChi a χ).symm.toLinearMap, ⟨f, h1, rfl⟩, ?_, ?_, ?_⟩
  · rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, add_mem (W.smul_mem _ (h2 o φ hφ)) (W.smul_mem _ hφ), (act_mulChi χ o φ).symm⟩
  · simpa using h3
  · rintro o _ ⟨φ, hφ, rfl⟩
    simp only [LinearEquiv.coe_coe, LinearMap.comp_apply, act_mulChi, LinearEquiv.symm_apply_apply,
      CuspSub.op_toTwist, map_add p, map_smul p, h4 o φ hφ]

theorem commute_Zalg {T : Module.End ℂ (Sm E a)} (hT : ∀ X, Commute T (lie E a X)) {z : Module.End ℂ (Sm E a)}
    (hz : z ∈ Zalg E a) : Commute T z := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Subalgebra.centralizer ℂ {T}
  have hS : ∀ {z}, z ∈ S ↔ Commute T z := by
    intro z
    simp [S, Subalgebra.mem_centralizer_iff, Commute, SemiconjBy]
  have hV : ∀ X, lie E a X ∈ S := fun X => hS.2 (hT X)
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hV _) (S.smul_mem (hV _) _)) _
  refine hS.1 ((Algebra.adjoin_le (S := S) ?_) hz)
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem isCuspForm_rs_sub {f : Sm E a} (h : IsCuspForm f) (z : (Ad E)ˣ) (c : ℂ) :
    IsCuspForm ((rs a z - algebraMap ℂ _ c) f) := by
  set Q : Module.End ℂ (Sm E a) := rs a z - algebraMap ℂ _ c
  have hQ : ∀ o, Commute Q (act o) := fun o => (rs_act z o).sub_left (Algebra.commutes c _)
  have ev : ∀ g, (Q f).1 g = f.1 (g * GeneralLinearGroup.scalar (Fin a) z) - c * f.1 g := fun g => rfl
  have hc := ContAut.continuous_of_isOpen_stab E a f h.1.level
  refine ⟨⟨fun γ g => by rw [ev, ev, mul_assoc, h.1.left, h.1.left], ?_, ?_, ?_, fun g => ?_⟩, ?_⟩
  · refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.1.level.mem_nhds (by simp)) fun k hk => ?_)
    exact (LinearMap.congr_fun (hQ (.fin k)).eq f).symm.trans (congrArg Q hk)
  · have := h.1.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k f)).map Q)
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, LinearMap.congr_fun (hQ (.cpt k)).eq f⟩
  · have := h.1.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z f) ''
      Zalg E a)).map Q) (Submodule.span_le.2 ?_)
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨y, hy, rfl⟩, LinearMap.congr_fun (commute_Zalg (fun X => hQ (.lie X)) hy).eq f⟩
  · obtain ⟨C, N, h1⟩ := h.1.growth (g * GeneralLinearGroup.scalar (Fin a) z)
    obtain ⟨C', N', h2⟩ := h.1.growth g
    refine ⟨|C| + ‖c‖ * |C'|, N + N', fun y => ?_⟩
    have h0 := one_le_height y
    have e1 : ‖f.1 (g * infGL E a y * GeneralLinearGroup.scalar (Fin a) z)‖ ≤ |C| * height y ^ (N + N') := by
      rw [mul_assoc, ← CuspRep.scalar_comm, ← mul_assoc]
      exact (h1 y).trans (mul_le_mul (le_abs_self _) (pow_le_pow_right₀ h0 (by omega)) (by positivity) (abs_nonneg _))
    have e2 : ‖f.1 (g * infGL E a y)‖ ≤ |C'| * height y ^ (N + N') :=
      (h2 y).trans (mul_le_mul (le_abs_self _) (pow_le_pow_right₀ h0 (by omega)) (by positivity) (abs_nonneg _))
    rw [ev, add_mul, mul_assoc ‖c‖]
    refine (norm_sub_le _ _).trans (add_le_add e1 ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left e2 (norm_nonneg _)
  · intro r h0 h1 _ _ ν 𝓕 hν h𝓕 g
    simp only [ev, mul_assoc]
    rw [integral_sub (integrableOn_unip hc h.1.left ν h𝓕 _) ((integrableOn_unip hc h.1.left ν h𝓕 _).const_mul c),
      integral_const_mul, h.2 r h0 h1 ν 𝓕 hν h𝓕, h.2 r h0 h1 ν 𝓕 hν h𝓕, mul_zero, sub_zero]

abbrev dSplit (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) : Module.End ℂ (Sm E a) :=
  lie E a (scL a 1)

theorem exists_aeval_eq_zero {f : Sm E a} (h : IsAutForm f) : ∃ p : ℂ[X], p ≠ 0 ∧ aeval (dSplit E a) p f = 0 := by
  have := h.zfin
  let L : ℂ[X] →ₗ[ℂ] Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z f) '' Zalg E a) :=
    LinearMap.codRestrict _ (LinearMap.applyₗ f ∘ₗ (aeval (dSplit E a)).toLinearMap) fun p =>
      Submodule.subset_span ⟨_, (Algebra.adjoin_le (S := Zalg E a) (Set.singleton_subset_iff.2 (lie_mem_Zalg 1)))
        (Polynomial.aeval_mem_adjoin_singleton ℂ _), rfl⟩
  by_contra! hc
  have hi : Function.Injective L := (injective_iff_map_eq_zero L).2 fun p hp => by
    by_contra h0
    exact hc p h0 (congrArg Subtype.val hp)
  exact Polynomial.not_finite (Module.Finite.of_injective L hi)

theorem hasCuspImage_of_eigen (H : ∀ (f : Sm E a) (c : ℂ), IsCuspForm f → f ≠ 0 →
    (∀ (t : ℝ) g, f.1 (splitCentre E a t * g) = Complex.exp (c * t) * f.1 g) → HasCuspImage f)
    {f : Sm E a} (h : IsCuspForm f) (h0 : f ≠ 0) : HasCuspImage f := by
  obtain ⟨p, hp, hf⟩ := exists_aeval_eq_zero h.1
  induction hn : p.natDegree generalizing p f with
  | zero =>
    rw [eq_C_of_natDegree_eq_zero hn] at hp hf
    exact absurd (by simpa using hf) (not_or.2 ⟨by simpa using hp, h0⟩)
  | succ n ih =>
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_root p (by
      rw [degree_eq_natDegree hp, hn]; exact_mod_cast n.succ_ne_zero)
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.2 hc
    have hq : q ≠ 0 := right_ne_zero_of_mul hp
    have hqn : q.natDegree = n := by
      rw [natDegree_mul (X_sub_C_ne_zero c) hq, natDegree_X_sub_C] at hn; omega
    have e1 : dSplit E a (aeval (dSplit E a) q f) = c • aeval (dSplit E a) q f := by
      rw [map_mul, Module.End.mul_apply] at hf
      simpa [sub_eq_zero] using hf
    let Q : ℝ → Module.End ℂ (Sm E a) := fun t =>
      rs a (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) - algebraMap ℂ _ (Complex.exp (c * t))
    have hQ : ∀ t o, Commute (Q t) (act o) := fun t o => (rs_act _ o).sub_left (Algebra.commutes _ _)
    by_cases hz : ∀ t, Q t f = 0
    · refine H f c h h0 fun t g => ?_
      rw [splitCentre_comm, splitCentre_eq_scalar]
      exact sub_eq_zero.1 (congrFun (congrArg Subtype.val (hz t)) g)
    · obtain ⟨t, ht⟩ := not_forall.1 hz
      refine HasCuspImage.of_commute (hQ t) (ih (f := Q t f) (isCuspForm_rs_sub h _ _) ht q hq ?_ hqn)
      have e2 : Commute (Q t) (aeval (dSplit E a) q) := by
        refine commute_Zalg (fun X => hQ t (.lie X)) ?_
        exact (Algebra.adjoin_le (S := Zalg E a) (Set.singleton_subset_iff.2 (lie_mem_Zalg 1)))
          (Polynomial.aeval_mem_adjoin_singleton ℂ _)
      rw [← Module.End.mul_apply, ← e2.eq, Module.End.mul_apply]
      have e3 : scL a (fun _ : InfinitePlace E => (t : ℂ)) = t • scL (E := E) a 1 := by
        ext i j w
        by_cases hij : i = j <;> simp [hij]
      have := rs_exp (fun _ : InfinitePlace E => (t : ℂ)) (c * t) (aeval (dSplit E a) q f) (by
        rw [e3, map_smul, LinearMap.smul_apply, e1, mul_comm, mul_smul, Complex.coe_smul])
      exact sub_eq_zero.2 this

variable (E) in

def cpowChar (s : ℂ) : HChar E :=
  ⟨MonoidHom.toHomUnits
      { toFun := fun x => Complex.exp (s * Real.log (ideleNorm (E := E) x))
        map_one' := by simp
        map_mul' := fun x y => by
          rw [map_mul, Real.log_mul (ideleNorm_ne_zero _) (ideleNorm_ne_zero _), ← Complex.exp_add]
          push_cast; ring_nf },
    Units.isEmbedding_val₀.continuous_iff.2 (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_ideleNorm.log fun _ => ideleNorm_ne_zero _)))),
    fun k => Units.ext (by
      have h := ideleNorm_principalIdele (E := E) k
      exact (congrArg (fun r : ℝ => Complex.exp (s * Real.log r)) h).trans (by simp))⟩

theorem exists_chiDet_splitCentre (ha : 0 < a) (c : ℂ) :
    ∃ χ : HChar E, ∀ t : ℝ, ((chiDet a χ (splitCentre E a t) : ℂˣ) : ℂ) = Complex.exp (c * t) := by
  let D : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun t => Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a t)))) fun x y => by
      rw [splitCentre_add, map_mul, map_mul, Real.log_mul (ideleNorm_ne_zero _) (ideleNorm_ne_zero _)]
  have hD : Continuous D :=
    (continuous_ideleNorm.comp (GeneralLinearGroup.continuous_det.comp
      GlobalTheory.OneRep.SplitTwist.continuous_splitCentre)).log fun _ => ideleNorm_ne_zero _
  have hDt : ∀ t, D t = t * D 1 := fun t => by simpa using map_real_smul D hD t 1
  have hD1 : 0 < D 1 := by
    change 0 < Real.log (ideleNorm (E := E) (GeneralLinearGroup.det (splitCentre E a 1)))
    rw [det_splitCentre_one, map_pow, Real.log_pow]
    exact mul_pos (by exact_mod_cast ha) (Real.log_pos (one_lt_ideleNorm_eIdele E))
  refine ⟨cpowChar E (c / D 1), fun t => ?_⟩
  change Complex.exp (c / D 1 * (D t : ℝ)) = _
  have : (D 1 : ℂ) ≠ 0 := by exact_mod_cast hD1.ne'
  rw [hDt t]; push_cast
  congr 1; field_simp

theorem hasCuspImage_of_invariant (H : ∀ f : Sm E a, IsCuspForm f → f ≠ 0 →
    (∀ (t : ℝ) g, f.1 (splitCentre E a t * g) = f.1 g) → HasCuspImage f)
    {f : Sm E a} (h : IsCuspForm f) (h0 : f ≠ 0) : HasCuspImage f := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact H f h h0 fun t g => congrArg f.1 (Subsingleton.elim _ _)
  refine hasCuspImage_of_eigen (fun f c h h0 hc => ?_) h h0
  obtain ⟨χ, hχ⟩ := exists_chiDet_splitCentre (E := E) ha (-c)
  have := (H _ (h.mulChi χ) ((map_ne_zero_iff _ (mulChi a χ).injective).2 h0) fun t g => by
    rw [mulChi_apply, mulChi_apply, map_mul, Units.val_mul, hχ, hc, mul_mul_mul_comm, ← Complex.exp_add]
    simp).mulChi χ⁻¹
  rwa [← mulChi_mul, mul_inv_cancel, mulChi_one] at this

end GlobalTheory.CuspQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesSpecialisedFormProdLinearForms
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

namespace GlobalTheory.HSShort.SplitCoord

theorem map_spec {F E K : Type} [CommRing F] [CommRing E] [CommRing K] [Algebra F E] [Algebra E K] [Algebra F K]
    [IsScalarTower F E K] {D N : ℕ} (s : Fin D → Fin N → E) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    map (algebraMap E K) (spec s f) = spec (fun i j => algebraMap E K (s i j)) f := by
  unfold spec
  induction f using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, MvPolynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X]
    congr 1
    obtain ⟨a, b⟩ := i
    refine Fin.lastCases ?_ (fun a => ?_) a <;> simp [join]

theorem map_lin_smul {E K : Type} [CommRing E] [CommRing K] (φ : E →+* K) {N : ℕ} (c : E) (y : Fin N → E) :
    map φ (lin (c • y)) = C (φ c) * lin fun j => φ (y j) := by
  simp only [lin, map_sum, map_mul, map_X, map_C, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_eq_C_mul {E K σ : Type} [Field E] [Field K] (φ : E →+* K) {P Q : MvPolynomial σ E} (hP : P ≠ 0) {c : K}
    (hc : c ≠ 0) (h : map φ Q = C c * map φ P) : ∃ c₀ : E, c₀ ≠ 0 ∧ Q = C c₀ * P := by
  obtain ⟨m, hm⟩ := ne_zero_iff.1 hP
  have e : φ (coeff m Q) = c * φ (coeff m P) := by
    simpa only [coeff_map, coeff_C_mul] using congrArg (coeff m) h
  have e' : φ (coeff m Q / coeff m P) = c := by
    rw [map_div₀, e, mul_div_cancel_right₀ _ ((map_ne_zero φ).2 hm)]
  refine ⟨coeff m Q / coeff m P, fun h0 => hc (by rw [← e', h0, map_zero]), map_injective φ φ.injective ?_⟩
  rw [map_mul, map_C, e', h]

theorem exists_eq_C_mul_prod {E K ι : Type} [Field E] [Field K] [Fintype ι] (φ : E →+* K) {N : ℕ}
    {Q : MvPolynomial (Fin 1 × Fin N) E} {y v : ι → Fin N → E} {z : ι → Fin N → K} {a : ι → E} (hy : ∀ p, y p ≠ 0)
    (ha : ∀ p, a p ≠ 0) (ea : ∀ p, y p = a p • v p) (hz : ∀ p, z p = fun j => φ (v p j)) {c : K} (hc : c ≠ 0)
    (h : map φ Q = C c * ∏ p, lin (z p)) : ∃ c₀ : E, c₀ ≠ 0 ∧ Q = C c₀ * ∏ p, lin (y p) := by
  have hA : (∏ p, φ (a p)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => (map_ne_zero _).2 (ha p)
  refine exists_eq_C_mul φ (Finset.prod_ne_zero_iff.2 fun p _ => Check.lin_ne (hy p)) (div_ne_zero hc hA) ?_
  rw [h, map_prod]
  simp only [ea, hz, map_lin_smul]
  rw [Finset.prod_mul_distrib, ← map_prod C, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hA]

theorem exists_coord_spec_eq : ∀ (F : Type) [Field F] [NumberField F] (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E] (s : Fin G.D → Fin G.N → E) (hs : (G.baseChange E).IsGood s) (δ : ℕ) (f : MvPolynomial (Fin (G.D + 1) × Fin G.N) F), Split G.toTuple E s → SimpleAt G.toTuple δ f E s → ∃ (Co : Coord (G.baseChange E) hs δ) (c : E), c ≠ 0 ∧ spec s f = C c * ∏ p, lin (Co.y p) := by
  intro F _ _ G E _ _ _ s hs δ f h hS
  obtain rfl := hS.card
  obtain ⟨x, Co, hCo, -⟩ := h.exists_coord hs
  obtain ⟨c, hc, e⟩ := hS.fac
  choose a ha ea using fun p => G.exists_coords_baseChange E (x p).pt.1
  have h₅ (p) : G.coords (LinSys.toBase (RatPt.geomPt G E s (x p))).1 =
      fun j => algebraMap E (AlgebraicClosure E) (G.coords ((x p).pt.1 ≫ G.bcFst E) j) := by
    rw [← LinSys.coords_spMap_comp]
    exact congrArg G.coords ((congrArg (· ≫ G.bcFst E) (Category.assoc _ _ _)).trans (Category.assoc _ _ _))
  have h₇ : ∏ᶠ z ∈ G.geomPts E (G.linSection E s), lin (G.coords (LinSys.toBase z : G.Pt (AlgebraicClosure E)).1) =
      ∏ p, lin (G.coords (LinSys.toBase (RatPt.geomPt G E s (x p)) : G.Pt (AlgebraicClosure E)).1) := by
    refine (finprod_mem_congr h.geomPts_eq fun _ _ => rfl).trans ?_
    rw [finprod_mem_range (RatPt.geomPt_injective hs), ← finprod_comp_equiv x, finprod_eq_prod_of_fintype]
  obtain ⟨c₀, h₀, e₀⟩ := exists_eq_C_mul_prod (N := G.N) (algebraMap E (AlgebraicClosure E)) (Q := spec s f) (y := Co.y)
    (fun p h0 => (G.baseChange E).geom.alg.bpf.coords_ne_zero _ ((hCo p).2.1.symm.trans h0)) ha
    (fun p => (hCo p).2.1.trans (ea p)) h₅ hc ((map_spec s f).trans (e.trans (congrArg (C c * ·) h₇)))
  exact ⟨Co, c₀, h₀, e₀⟩

end GlobalTheory.HSShort.SplitCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousFormsQuotientBirationalSystem
section
set_option autoImplicit false

namespace GlobalTheory.HSShort.FormRatio

open MvPolynomial CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Adelic GlobalTheory.Points GlobalTheory.Twist

theorem exists_forms_of_mem_closure {F K : Type} [Field F] [Field K] {N : ℕ} (φ : F →+* K) (c : Fin N → K) {r : K}
    (hr : r ∈ Subfield.closure (Set.range φ ∪ {r | ∃ i j, r = c i / c j})) :
    ∃ (d : ℕ) (P Q : MvPolynomial (Fin N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ eval₂ φ c Q ≠ 0 ∧
      r * eval₂ φ c Q = eval₂ φ c P := by
  have h0 : ∃ (d : ℕ) (P Q : MvPolynomial (Fin N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ eval₂ φ c Q ≠ 0 ∧
      0 * eval₂ φ c Q = eval₂ φ c P :=
    ⟨0, 0, 1, isHomogeneous_zero _ _ _, isHomogeneous_one _ _, by simp, by simp⟩
  induction hr using Subfield.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | ⟨i, j, rfl⟩
    · exact ⟨0, C a, 1, isHomogeneous_C _ _, isHomogeneous_one _ _, by simp, by simp⟩
    · by_cases hj : c j = 0
      · rwa [hj, div_zero]
      · exact ⟨1, X i, X j, isHomogeneous_X _ _, isHomogeneous_X _ _, by simpa using hj, by simp [hj]⟩
  | one => exact ⟨0, 1, 1, isHomogeneous_one _ _, isHomogeneous_one _ _, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    obtain ⟨e, P', Q', hP', hQ', h1', h2'⟩ := hy
    refine ⟨d + e, P * Q' + Q * P', Q * Q', (hP.mul hQ').add (hQ.mul hP'), hQ.mul hQ', ?_, ?_⟩
    · rw [eval₂_mul]; exact mul_ne_zero h1 h1'
    · rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, ← h2, ← h2']; ring
  | neg x _ hx =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    exact ⟨d, -P, Q, hP.neg, hQ, h1, by rw [eval₂_neg, ← h2, neg_mul]⟩
  | inv x _ hx =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    by_cases hx0 : x = 0
    · rwa [hx0, inv_zero]
    · refine ⟨d, Q, P, hQ, hP, h2 ▸ mul_ne_zero hx0 h1, ?_⟩
      rw [← h2, inv_mul_cancel_left₀ hx0]
  | mul x y _ _ hx hy =>
    obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := hx
    obtain ⟨e, P', Q', hP', hQ', h1', h2'⟩ := hy
    refine ⟨d + e, P * P', Q * Q', hP.mul hP', hQ.mul hQ', ?_, ?_⟩
    · rw [eval₂_mul]; exact mul_ne_zero h1 h1'
    · rw [eval₂_mul, eval₂_mul, ← h2, ← h2']; ring

theorem eq_zero_of_valR_generic {Y : Scheme.{0}} [IsReduced Y] {η : Y} (hη : IsGenericPoint η Set.univ)
    {U : Y.Opens} (f : Γ(Y, U)) (h : valR (resPt η) U f = 0) : f = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro y hy
  have h1 : ptOf (resPt η) ∈ Y.basicOpen f := by
    rw [ptOf_resPt]
    exact (hη.mem_open_set_iff (Y.basicOpen f).isOpen).2 ⟨y, trivial, hy⟩
  exact ((valR_ne_zero_iff _ (Y.basicOpen_le f h1) f).2 h1 h).elim

theorem exists_forms (F : Type) [Field F] (S : LinSys F) (hS : S.IsVariety) (_ : S.BasePointFree)
    (hb : S.Birational) (W : S.Y.Opens) (a : Γ(S.Y, W)) :
    ∃ (d : ℕ) (P Q : MvPolynomial (Fin S.N) F), P.IsHomogeneous d ∧ Q.IsHomogeneous d ∧ Q ∉ S.imageIdeal ∧
      (a ≠ 0 → P ∉ S.imageIdeal) ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : S.Pt K), ptOf x.1 ∈ W →
        valR x.1 W a * aeval (S.coords x.1) Q = aeval (S.coords x.1) P := by
  have := hS.isIntegral
  obtain ⟨η, hη, hr⟩ := hb
  obtain ⟨d, P, Q, hP, hQ, h1, h2⟩ := exists_forms_of_mem_closure (S.baseHom (resPt η)) (S.coords (resPt η))
    (r := valR (resPt η) W a) (hr.ge (Subfield.mem_top _))
  refine ⟨d, P, Q, hP, hQ, fun h => h1 (S.eval₂_coords_eq_zero _ h), fun ha h => ?_, fun K _ _ x hx => ?_⟩
  · rw [S.eval₂_coords_eq_zero _ h] at h2
    exact ha (eq_zero_of_valR_generic hη a ((mul_eq_zero.1 h2).resolve_right h1))
  · set j := S.chartAt (ptOf x.1)
    have hxV : ptOf x.1 ∈ W ⊓ S.L.U j := ⟨hx, S.mem_chartAt _⟩
    have hηV : ptOf (resPt η) ∈ W ⊓ S.L.U j := by
      rw [ptOf_resPt]
      exact (hη.mem_open_set_iff (W ⊓ S.L.U j).isOpen).2 ⟨_, trivial, hxV⟩
    let f : Γ(S.Y, W ⊓ S.L.U j) :=
      (S.Y.presheaf.map (homOfLE inf_le_left).op).hom a *
        (S.Y.presheaf.map (homOfLE inf_le_right).op).hom (zfun (S.form hQ) j) +
        -(S.Y.presheaf.map (homOfLE inf_le_right).op).hom (zfun (S.form hP) j)
    have hf : ∀ {Ω : Type} [Field Ω] (z : Sp Ω ⟶ S.Y), ptOf z ∈ W ⊓ S.L.U j → valR z _ f =
        valR z W a * valR z _ (zfun (S.form hQ) j) - valR z _ (zfun (S.form hP) j) := fun z hz => by
      have h := (le_iff_ptOf_mem z _).2 hz
      rw [valR_add z _ h, valR_neg z _ h, valR_mul z _ h, valR_res z _ h, valR_res z _ h, valR_res z _ h,
        sub_eq_add_neg]
    have hf0 : f = 0 := by
      obtain ⟨c, -, -, hc⟩ := S.exists_frame_change (resPt η) j hηV.2
      refine eq_zero_of_valR_generic hη f ?_
      rw [hf _ hηV, hc, hc, S.powVal_form, S.powVal_form, ← h2]
      ring
    have h3 := hf x.1 hxV
    rw [hf0, valR_zero _ _ ((le_iff_ptOf_mem _ _).2 hxV), eq_comm, sub_eq_zero] at h3
    have e : ∀ {g : MvPolynomial (Fin S.N) F} (hg : g.IsHomogeneous d),
        valR x.1 _ (zfun (S.form hg) j) = aeval (S.coords x.1) g := fun hg =>
      (S.powVal_form x.1 hg).trans (by rw [LinSys.baseHom_ptOver, aeval_def])
    rwa [e, e] at h3

end GlobalTheory.HSShort.FormRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaxIdealSmulMemOfLtOfRelIndexNeZero
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem exists_maxIdeal_smul_mem_of_lt_of_relIndex_ne_zero (F V : Type) [Field F] [NumberField F]
    [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V]
    (N₀ N : Submodule (𝓞 F) V) (hlt : N₀ < N)
    (hidx : N₀.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0) :
    ∃ (u : V) (p : Ideal (𝓞 F)), p.IsMaximal ∧ u ∈ N ∧ u ∉ N₀ ∧ ∀ π ∈ p, π • u ∈ N₀ := by
  classical
  set P : Submodule (𝓞 F) N := N₀.comap N.subtype with hP
  have hPne : P ≠ ⊤ := by
    intro h
    obtain ⟨v, hvN, hvN₀⟩ := SetLike.exists_of_lt hlt
    have hv : (⟨v, hvN⟩ : N) ∈ P := h ▸ Submodule.mem_top
    exact hvN₀ hv
  haveI : Nontrivial (N ⧸ P) := Submodule.Quotient.nontrivial_iff.2 hPne
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty (𝓞 F) (N ⧸ P)
  obtain ⟨hprime, x, hx⟩ := (isAssociatedPrime_iff (R := 𝓞 F) (M := N ⧸ P)).1 hp
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P x
  have hmem : ∀ r : 𝓞 F, r ∈ p ↔ r • (y : V) ∈ N₀ := by
    intro r
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, hP, Submodule.mem_comap]
    rfl
  set n := N₀.toAddSubgroup.relIndex N.toAddSubgroup with hn
  have hkill : n • (y : V) ∈ N₀ := by
    have h := AddSubgroup.nsmul_index_mem (N₀.toAddSubgroup.addSubgroupOf N.toAddSubgroup)
      (⟨y.1, y.2⟩ : N.toAddSubgroup)
    exact AddSubgroup.mem_addSubgroupOf.1 h
  have hnp : ((n : ℕ) : 𝓞 F) ∈ p := by
    rw [hmem, Nat.cast_smul_eq_nsmul]
    exact hkill
  have hp0 : p ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hnp
    exact hidx (by exact_mod_cast hnp)
  refine ⟨(y : V), p, Ideal.IsPrime.isMaximal hprime hp0, y.2, ?_, fun π hπ => (hmem π).1 hπ⟩
  intro hy
  apply hprime.ne_top
  rw [eq_top_iff]
  intro r _
  rw [hmem]
  exact N₀.smul_mem r hy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsIntegersStatement
section
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroups_integers : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ B : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), AddSubgroup (v.adicCompletion F),
      (∀ v, IsOpen (B v : Set (v.adicCompletion F))) ∧
      (∀ v, (B v : Set (v.adicCompletion F)) ⊆ v.adicCompletionIntegers F) ∧
      (∀ᶠ v in Filter.cofinite, (B v : Set (v.adicCompletion F)) = v.adicCompletionIntegers F) ∧
      ∀ y u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (u i) ∈ B v) → g (y + u) = g y := by
  first | exact @GlobalTheory.SBBox.exists_box_invariant | exact GlobalTheory.SBBox.exists_box_invariant | (intros; apply GlobalTheory.SBBox.exists_box_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioMemValuationSubringAtGenericPointStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ratio_mem_valuationSubring_at_generic_point : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∀ η : S.Y, IsGenericPoint η Set.univ → ∀ V : ValuationSubring (S.Y.residueField η), (∀ c, S.baseHom (resPt η) c ∈ V) → ∃ i, S.val (resPt η) (S.comb (u i)) ≠ 0 ∧ S.powVal (resPt η) th / S.val (resPt η) (S.comb (u i)) ^ e ∈ V := by
  first | exact @GlobalTheory.Adelic.LinSys.exists_ratio_mem_valuationSubring | exact GlobalTheory.Adelic.LinSys.exists_ratio_mem_valuationSubring | (intros; apply GlobalTheory.Adelic.LinSys.exists_ratio_mem_valuationSubring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardChartsFormalTowerOfVeryAmpleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standard_charts_formalTower_of_veryAmple : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H₀ : LB (Y 0).left) (n : ℕ) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → VeryAmpleBy (Y 0).hom H₀ s₀ → ∃ C : Charts I Y β n, (∀ i, C.D 0 i = nonzeroLocus (s₀ i)) ∧ ∀ i j (m : H₀.ι), rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ j).f m) = rs (Y 0).left (inf_le_left : C.D 0 i ⊓ H₀.U m ≤ C.D 0 i) (C.ρ 0 i j) * rs (Y 0).left (inf_le_right : C.D 0 i ⊓ H₀.U m ≤ H₀.U m) ((s₀ i).f m) := by
  first | exact @GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy | exact GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy | (intros; apply GlobalTheory.FormalAlg.exists_charts_of_veryAmpleBy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorsHolomorphicModelUniqueUpToPhaseStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extremal_vectors_holomorphic_model_unique_up_to_phase : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), GlobalTheory.HolDict.HolShape M → ExtLine M := by
  first | exact @GlobalTheory.HolLowOnce.extLine_of_holShape | exact GlobalTheory.HolLowOnce.extLine_of_holShape | (intros; apply GlobalTheory.HolLowOnce.extLine_of_holShape <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimProductTranslatesStatement
section
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_product_translates : ∀ (G ι : Type) [Group G] (T : ι → Set G) (c : G → ℂ), (∀ i j, i ≠ j → ∀ a ∈ T i, ∀ b ∈ T j, a * b = b * a) → (∀ i, FiniteDimensional ℂ (Submodule.span ℂ {f : G → ℂ | ∃ a ∈ T i, f = fun g => c (a * g)})) → ∀ l : List ι, l.Nodup → FiniteDimensional ℂ (Submodule.span ℂ {f : G → ℂ | ∃ a : ι → G, (∀ i, a i ∈ T i) ∧ f = fun g => c ((l.map a).prod * g)}) := by
  first | exact @GlobalTheory.TorFin.Comb.finiteDimensional_span_translates_prod | exact GlobalTheory.TorFin.Comb.finiteDimensional_span_translates_prod | (intros; apply GlobalTheory.TorFin.Comb.finiteDimensional_span_translates_prod <;> assumption)
end

