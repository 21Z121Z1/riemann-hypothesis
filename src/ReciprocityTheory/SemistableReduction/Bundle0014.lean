import Mathlib
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
import ReciprocityTheory.SemistableReduction.Bundle0006
import ReciprocityTheory.SemistableReduction.Bundle0001
import ReciprocityTheory.SemistableReduction.Bundle0007
import ReciprocityTheory.SemistableReduction.Bundle0008

-- bundled from ReciprocityTheory.SemistableReduction.GenericImageFinite
section
namespace ReciprocityTheory.MultiplicativeHeights

open MvPolynomial DerivationAlgebraicIndependence

theorem trdeg_sField {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ) :
    Algebra.trdeg K (SField Ω D m) = Algebra.trdeg K Ω + ((1 + (D + 1) * m : ℕ) : Cardinal) := by
  classical
  haveI : FaithfulSMul K Ω :=
    (faithfulSMul_iff_algebraMap_injective K Ω).2 (algebraMap K Ω).injective
  haveI : FaithfulSMul Ω (MvPolynomial (SVars D m) Ω) :=
    (faithfulSMul_iff_algebraMap_injective Ω _).2 (MvPolynomial.C_injective _ _)
  haveI : FaithfulSMul (MvPolynomial (SVars D m) Ω) (SField Ω D m) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2
      (IsFractionRing.injective (MvPolynomial (SVars D m) Ω) (SField Ω D m))
  have h1 := trdeg_add_eq K (MvPolynomial (SVars D m) Ω) (A := SField Ω D m)
  have h2 := trdeg_add_eq K Ω (A := MvPolynomial (SVars D m) Ω)
  have h3 : Algebra.trdeg (MvPolynomial (SVars D m) Ω) (SField Ω D m) = 0 :=
    trdeg_eq_zero_iff.2
      (IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial (SVars D m) Ω)))
  have h4 : Algebra.trdeg Ω (MvPolynomial (SVars D m) Ω) =
      ((1 + (D + 1) * m : ℕ) : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]
    congr 1
    simp [SVars, Fintype.card_sum, Fintype.card_prod]
  rw [← h1, h3, add_zero, ← h2, h4]

theorem genericImageFinite : FieldOfSStatement := by
  classical
  unfold FieldOfSStatement
  intro K Ω _ _ _ _ D m x hfg htr hJ
  obtain ⟨J, hJ⟩ := hJ
  set v : Fin D → KaehlerDifferential K Ω := fun a => KaehlerDifferential.D K Ω (x (J a)) with hv
  have hli : LinearIndependent Ω v := hJ
  have hφ : ∀ a : Fin D, ∃ φ : KaehlerDifferential K Ω →ₗ[Ω] Ω,
      ∀ b, φ (v b) = if a = b then 1 else 0 := by
    intro a
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.lapply a).comp hli.repr)
    refine ⟨g, fun b => ?_⟩
    have hb : v b ∈ Submodule.span Ω (Set.range v) := Submodule.subset_span ⟨b, rfl⟩
    have h := congrArg (fun f => f ⟨v b, hb⟩) hg
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h
    rw [h, Finsupp.lapply_apply, hli.repr_eq_single b ⟨v b, hb⟩ rfl, Finsupp.single_apply]
    simp [eq_comm]
  choose φ hφ using hφ
  let δ : Fin D → Derivation K Ω Ω := fun a => (φ a).compDer (KaehlerDifferential.D K Ω)
  have hδ : ∀ a b, δ a (x (J b)) = if a = b then 1 else 0 := fun a b => hφ a b
  have hg := DerivationAlgebraicIndependence.gFam_indep (K := K) x J δ hδ
  have hind : AlgebraicIndependent K (sImage (D := D) x) := by
    have h1 := hg.comp _ (DerivationAlgebraicIndependence.eIdx_injective D m)
    have h2 := h1.map'
      (f := IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m))
      (IsFractionRing.injective _ _)
    convert h2 using 1
    funext p
    simp [DerivationAlgebraicIndependence.sImage_eq]
  refine ⟨hind, ?_⟩
  have htrS : Algebra.trdeg K (SField Ω D m) = (((D + 1) * (m + 1) : ℕ) : Cardinal) := by
    rw [trdeg_sField, htr, ← Nat.cast_add]
    congr 1
    ring
  have hTB : IsTranscendenceBasis K (sImage (D := D) x) := by
    refine hind.isTranscendenceBasis_of_lift_trdeg_le ?_ ?_
    · rw [htrS]
      exact Cardinal.nat_lt_aleph0 _
    · rw [htrS]
      simp
  have halg := hTB.isAlgebraic_field
  set E := IntermediateField.adjoin K (Set.range (sImage (D := D) x))
  obtain ⟨s, hs⟩ := hfg
  let f : Ω →ₐ[K] SField Ω D m :=
    (IsScalarTower.toAlgHom K (MvPolynomial (SVars D m) Ω) (SField Ω D m)).comp
      (IsScalarTower.toAlgHom K Ω (MvPolynomial (SVars D m) Ω))
  let S : Set (SField Ω D m) := f '' (s : Set Ω) ∪
    Set.range (fun i => algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) (MvPolynomial.X i))
  have hSfin : S.Finite := (s.finite_toSet.image _).union (Set.finite_range _)
  haveI : Finite S := hSfin.to_subtype
  let L := IntermediateField.adjoin E S
  have hK : IntermediateField.adjoin K (f '' (s : Set Ω)) ≤ L.restrictScalars K := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    exact IntermediateField.subset_adjoin E S (Or.inl hz)
  have hω : ∀ ω : Ω, f ω ∈ L := by
    intro ω
    have h1 : f ω ∈ (IntermediateField.adjoin K (s : Set Ω)).map f :=
      (IntermediateField.mem_map _).2 ⟨ω, by rw [hs]; trivial, rfl⟩
    rw [IntermediateField.adjoin_map] at h1
    exact hK h1
  have hP : ∀ p : MvPolynomial (SVars D m) Ω,
      algebraMap (MvPolynomial (SVars D m) Ω) (SField Ω D m) p ∈ L := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have h := hω a
      simpa [f, MvPolynomial.algebraMap_eq] using h
    | add p q hp hq =>
      rw [map_add]
      exact L.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact L.mul_mem hp (IntermediateField.subset_adjoin E S (Or.inr ⟨i, rfl⟩))
  have htop : L = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial (SVars D m) Ω) z
    exact L.div_mem (hP a) (hP b)
  have hfd : FiniteDimensional E L :=
    IntermediateField.finiteDimensional_adjoin fun z _ => (halg.isAlgebraic z).isIntegral
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.GramOfLinearOrder
section
namespace ReciprocityTheory.MultiplicativeHeights

open Finset Pointwise

private lemma support_subset_of_mem_span_of_support_subset {ι : Type} (s : Set (ι →₀ ℕ))
    (G : Set (MvPolynomial ι ℂ)) (hG : ∀ g ∈ G, (g.support : Set (ι →₀ ℕ)) ⊆ s)
    {p : MvPolynomial ι ℂ} (hp : p ∈ Submodule.span ℂ G) : (p.support : Set (ι →₀ ℕ)) ⊆ s := by
  classical
  induction hp using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero => simp
  | add x y _ _ hx hy =>
    intro t ht
    rcases Finset.mem_union.mp (MvPolynomial.support_add ht) with h | h
    exacts [hx h, hy h]
  | smul a x _ hx => exact fun t ht => hx (MvPolynomial.support_smul ht)

theorem gram_of_linearOrder {ι : Type} [Fintype ι] [LinearOrder ι]
    (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) (F : MvPolynomial ι ℂ) (S : Finset (ι →₀ ℕ)) (hF : F ≠ 0) :
    Real.exp (2 * S.card * torusMean F) ≤
      (Matrix.det (Matrix.of fun m m' : S =>
        polyInner (F * MvPolynomial.monomial (m : ι →₀ ℕ) 1)
          (F * MvPolynomial.monomial (m' : ι →₀ ℕ) 1))).re := by
  obtain ⟨m, hmS, hminj, hmlex⟩ := exists_lex_enum S
  let T : Finset (ι →₀ ℕ) := S.biUnion fun s => (F * MvPolynomial.monomial s (1 : ℂ)).support
  have hPT : ∀ s ∈ S, (F * MvPolynomial.monomial s (1 : ℂ)).support ⊆ T := fun s hs =>
    Finset.subset_biUnion_of_mem (fun s => (F * MvPolynomial.monomial s (1 : ℂ)).support) hs
  let v : Fin S.card → EuclideanSpace ℂ T := fun k => coeffVec T (F * MvPolynomial.monomial (m k) 1)

  have hbij : Function.Bijective (fun k : Fin S.card => (⟨m k, hmS k⟩ : S)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨fun a b h => hminj (congrArg Subtype.val h), by simp⟩
  let e : Fin S.card ≃ S := Equiv.ofBijective _ hbij
  have hdet : Matrix.det (Matrix.of fun a b : S =>
        polyInner (F * MvPolynomial.monomial (a : ι →₀ ℕ) 1)
          (F * MvPolynomial.monomial (b : ι →₀ ℕ) 1)) = (Matrix.gram ℂ v).det := by
    rw [← Matrix.det_submatrix_equiv_self e, ← Matrix.det_transpose (Matrix.gram ℂ v)]
    congr 1
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.gram_apply,
      e, Equiv.ofBijective_apply]
    exact polyInner_eq_inner T _ _ (hPT _ (hmS i))
  have hT : ∀ j, ((F * MvPolynomial.monomial (m j) (1 : ℂ)).support : Set (ι →₀ ℕ)) ⊆ T :=
    fun j => by exact_mod_cast hPT _ (hmS j)

  have hδ : ∀ k : Fin S.card, ∀ x ∈ Submodule.span ℂ (v '' Set.Iio k),
      Real.exp (2 * torusMean F) ≤ ‖v k - x‖ ^ 2 := by
    intro k x hx
    have hspan : Submodule.span ℂ (v '' Set.Iio k) =
        (Submodule.span ℂ ((fun j => MvPolynomial.monomial (m j) (1 : ℂ)) '' Set.Iio k)).map
          ((coeffVec T).comp (LinearMap.mulLeft ℂ F)) := by
      rw [Submodule.map_span, ← Set.image_comp]
      rfl
    rw [hspan] at hx
    obtain ⟨Q, hQ, rfl⟩ := hx
    have hQsupp : ∀ t ∈ Q.support, toLex (m k) < toLex t := by
      have hs := support_subset_of_mem_span_of_support_subset {t | toLex (m k) < toLex t} _ (by
        rintro _ ⟨j, hj, rfl⟩ t ht
        have ht' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset ht)
        subst ht'
        exact hmlex j k hj) hQ
      intro t ht
      exact hs ht
    have hmain := exp_torus_mean_le_l2_of_lex hBasic hLex hL2 F hF (m k) Q hQsupp
    have hFQ : ((F * Q).support : Set (ι →₀ ℕ)) ⊆ T := by
      have hmemFQ : F * Q ∈ Submodule.span ℂ
          ((LinearMap.mulLeft ℂ F) '' ((fun j => MvPolynomial.monomial (m j) (1 : ℂ)) '' Set.Iio k)) := by
        rw [← Submodule.map_span]
        exact Submodule.mem_map.mpr ⟨Q, hQ, rfl⟩
      refine support_subset_of_mem_span_of_support_subset _ _ ?_ hmemFQ
      rintro _ ⟨_, ⟨j, _, rfl⟩, rfl⟩
      exact hT j
    have hsupp : (F * (MvPolynomial.monomial (m k) 1 - Q)).support ⊆ T := by
      rw [mul_sub]
      intro t ht
      rcases Finset.mem_union.mp (MvPolynomial.support_sub _ _ _ ht) with h | h
      · exact_mod_cast hT k h
      · exact_mod_cast hFQ h
    have hsub : v k - ((coeffVec T).comp (LinearMap.mulLeft ℂ F)) Q =
        coeffVec T (F * (MvPolynomial.monomial (m k) 1 - Q)) := by
      rw [mul_sub, map_sub] <;> rfl
    rw [hsub, norm_coeffVec T _ hsupp]
    calc Real.exp (2 * torusMean F) = Real.exp (torusMean F) ^ 2 := by
          rw [sq, ← Real.exp_add, two_mul]
      _ ≤ _ := by gcongr
  have hprod := prod_le_re_det_gram S.card v (fun _ => Real.exp (2 * torusMean F))
    (fun _ => (Real.exp_pos _).le) hδ
  rw [hdet]
  refine le_trans (le_of_eq ?_) hprod
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  congr 1
  ring

theorem gram_holds (hBasic : TorusMeanBasicStatement) (hLex : TorusLexStatement)
    (hL2 : TorusL2Cauchy) : GramStatement := by
  unfold GramStatement
  intro ι _ _ F S hF
  letI : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  convert gram_of_linearOrder hBasic hLex hL2 F S hF

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.IntCoresB
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric

def BlockPoly (k n : ℕ) (a : Fin k → ℕ) (F : (Fin k → Fin n → ℂ) → ℂ) : Prop :=
  Continuous F ∧ ∀ (b : Fin k) (p : Fin k → Fin n → ℂ), ∃ g : MvPolynomial (Fin n) ℂ,
    g.IsHomogeneous (a b) ∧ ∀ w, F (Function.update p b w) = MvPolynomial.eval w g

def onSpheres {k n : ℕ} (F : (Fin k → Fin n → ℂ) → ℂ) (z : Fin k → UnitSphereC n) : ℂ :=
  F fun b => spherePoint (z b)

theorem BlockPoly.restrict {k n : ℕ} {a : Fin (k + 1) → ℕ} {F : (Fin (k + 1) → Fin n → ℂ) → ℂ}
    (hF : BlockPoly (k + 1) n a F) (v : Fin n → ℂ) :
    BlockPoly k n (fun j => a j.succ) (fun p => F (Fin.cons v p)) := by
  refine ⟨hF.1.comp (continuous_const.finCons continuous_id), fun b p => ?_⟩
  obtain ⟨g, hg, hgF⟩ := hF.2 b.succ (Fin.cons v p)
  refine ⟨g, hg, fun w => ?_⟩
  simp only
  rw [Fin.cons_update]
  exact hgF w

theorem blockPoly_claim (hSJ : SJStatement) (n : ℕ) : ∀ (k : ℕ) (a : Fin k → ℕ)
    (F : (Fin k → Fin n → ℂ) → ℂ), BlockPoly k n a F → ∀ z0 : Fin k → UnitSphereC n,
    onSpheres F z0 ≠ 0 →
    Integrable (fun z => Real.log ‖onSpheres F z‖) (Measure.pi fun _ : Fin k => sphereProb n) ∧
      Measure.pi (fun _ : Fin k => sphereProb n) {z | onSpheres F z = 0} = 0 := by
  haveI : IsFiniteMeasure (sphereProb n) := by unfold sphereProb; infer_instance
  intro k
  induction k with
  | zero =>
    intro a F hF z0 hz0
    have hconst : ∀ z : Fin 0 → UnitSphereC n, onSpheres F z = onSpheres F z0 := by
      intro z
      unfold onSpheres
      congr 1
      funext b
      exact b.elim0
    refine ⟨?_, ?_⟩
    · simp_rw [hconst]
      exact integrable_const _
    · simp_rw [hconst]
      simp [hz0]
  | succ k ih =>
    intro a F hF z0 hz0
    set μ := sphereProb n with hμ
    set ν := Measure.pi fun _ : Fin k => sphereProb n with hν
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => UnitSphereC n) 0
    have mp : MeasurePreserving e (Measure.pi fun _ : Fin (k + 1) => sphereProb n) (μ.prod ν) :=
      measurePreserving_piFinSuccAbove (fun _ => sphereProb n) 0
    let e2 := e.trans MeasurableEquiv.prodComm
    have mp2 : MeasurePreserving e2 (Measure.pi fun _ : Fin (k + 1) => sphereProb n) (ν.prod μ) :=
      (Measure.measurePreserving_swap).comp mp
    have hcont : Continuous (onSpheres F : (Fin (k + 1) → UnitSphereC n) → ℂ) :=
      hF.1.comp (continuous_pi fun b => (continuous_spherePoint n).comp (continuous_apply b))
    let H : (Fin k → UnitSphereC n) × UnitSphereC n → ℂ := fun q => onSpheres F (e2.symm q)
    have hHm : Measurable H := hcont.measurable.comp e2.symm.measurable
    have hsymm : ∀ z' w, e2.symm (z', w) = Fin.cons w z' := by
      intro z' w
      simp [e2, e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero']
      rfl
    have hH : ∀ z' w, H (z', w) = F (Fin.cons (spherePoint w) (fun b => spherePoint (z' b))) := by
      intro z' w
      simp only [H, onSpheres, hsymm]
      congr 1
      funext b
      refine Fin.cases ?_ (fun j => ?_) b <;> simp
    have hcomp : ∀ z, onSpheres F z = H (e2 z) := by
      intro z
      simp only [H, MeasurableEquiv.symm_apply_apply]
    set v0 := spherePoint (z0 0) with hv0
    have hR := hF.restrict v0
    have hG : ∀ z', onSpheres (fun p => F (Fin.cons v0 p)) z' = H (z', z0 0) := by
      intro z'
      rw [hH]
      rfl
    have hz0' : onSpheres (fun p => F (Fin.cons v0 p)) (fun j => z0 j.succ) ≠ 0 := by
      simp only [onSpheres] at hz0 ⊢
      convert hz0 using 2
      funext b
      refine Fin.cases ?_ (fun j => ?_) b <;> simp [v0]
    obtain ⟨ihInt, ihNull⟩ := ih _ _ hR _ hz0'
    simp_rw [hG] at ihInt ihNull
    have hgood : ∀ᵐ z' ∂ν, H (z', z0 0) ≠ 0 := by
      rw [ae_iff]
      simpa using ihNull
    have hslice : ∀ z', H (z', z0 0) ≠ 0 →
        Integrable (fun w => Real.log ‖H (z', w)‖) μ ∧
        Real.log ‖H (z', z0 0)‖ - (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ) ≤
          ∫ w, Real.log ‖H (z', w)‖ ∂μ ∧ μ {w | H (z', w) = 0} = 0 := by
      intro z' hz'
      obtain ⟨g, hg, hgF⟩ := hF.2 0 (Fin.cons 0 (fun b => spherePoint (z' b)))
      have hHw : ∀ w, H (z', w) = MvPolynomial.eval (spherePoint w) g := by
        intro w
        rw [hH, ← hgF, Fin.update_cons_zero]
      have hu : ‖(z0 0 : EuclideanSpace ℂ (Fin n))‖ = 1 := norm_eq_of_mem_sphere _
      have hgu : MvPolynomial.eval (WithLp.ofLp (z0 0 : EuclideanSpace ℂ (Fin n))) g ≠ 0 := by
        rw [hHw] at hz'
        exact hz'
      obtain ⟨hI, hL⟩ := hSJ n (a 0) g _ hg hu hgu
      have hN := sphere_zero_null hSJ g hg _ hu hgu
      simp_rw [hHw]
      exact ⟨hI, hL, hN⟩
    obtain ⟨C, hC⟩ : ∃ C, ∀ z, ‖onSpheres F z‖ ≤ C := by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
      exact ⟨C, fun z => hC z (Set.mem_univ _)⟩
    set M := Real.log (max C 1) with hMdef
    have hM0 : 0 ≤ M := Real.log_nonneg (le_max_right _ _)
    have hLM : ∀ q, Real.log ‖H q‖ ≤ M := by
      intro q
      rcases (norm_nonneg (H q)).eq_or_lt with h0 | hpos
      · rw [← h0, Real.log_zero]
        exact hM0
      · exact Real.log_le_log hpos ((hC _).trans (le_max_left _ _))
    have habs : ∀ q, ‖Real.log ‖H q‖‖ ≤ 2 * M - Real.log ‖H q‖ := by
      intro q
      rw [Real.norm_eq_abs]
      have := hLM q
      rcases le_total 0 (Real.log ‖H q‖) with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_nonpos h]; linarith
    have hfm : AEStronglyMeasurable (fun q => Real.log ‖H q‖) (ν.prod μ) :=
      (Real.measurable_log.comp hHm.norm).aestronglyMeasurable
    have hInt2 : Integrable (fun q => Real.log ‖H q‖) (ν.prod μ) := by
      rw [integrable_prod_iff hfm]
      refine ⟨hgood.mono fun z' hz' => (hslice z' hz').1, ?_⟩
      refine Integrable.mono'
        (g := fun z' => ∫ _w, (2 * M) ∂μ -
          (Real.log ‖H (z', z0 0)‖ - (a 0 : ℝ) / 2 * (harmonic (n - 1) : ℝ)))
        ((integrable_const _).sub (ihInt.sub (integrable_const _)))
        hfm.norm.integral_prod_right' ?_
      filter_upwards [hgood] with z' hz'
      obtain ⟨hI, hL, -⟩ := hslice z' hz'
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ w, ‖Real.log ‖H (z', w)‖‖ ∂μ ≤ ∫ w, (2 * M - Real.log ‖H (z', w)‖) ∂μ :=
            integral_mono hI.norm ((integrable_const _).sub hI) (fun w => habs _)
        _ = ∫ _w, (2 * M) ∂μ - ∫ w, Real.log ‖H (z', w)‖ ∂μ :=
            integral_sub (integrable_const _) hI
        _ ≤ _ := by linarith
    have hNull2 : (ν.prod μ) {q | H q = 0} = 0 := by
      have hms : MeasurableSet {q | H q = 0} := hHm (measurableSet_singleton 0)
      rw [Measure.measure_prod_null hms]
      filter_upwards [hgood] with z' hz'
      simpa [Set.preimage] using (hslice z' hz').2.2
    refine ⟨?_, ?_⟩
    · have h1 : (fun z => Real.log ‖onSpheres F z‖) = (fun q => Real.log ‖H q‖) ∘ e2 := by
        funext z
        simp only [Function.comp_apply]
        rw [hcomp z]
      rw [h1, mp2.integrable_comp_emb e2.measurableEmbedding]
      exact hInt2
    · have h1 : {z | onSpheres F z = 0} = e2 ⁻¹' {q | H q = 0} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_preimage]
        rw [hcomp z]
      rw [h1, mp2.measure_preimage_emb e2.measurableEmbedding]
      exact hNull2

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.UnipotentB
section
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix

theorem unip_normSq_pow_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) (n : ℕ) (u : Fin r → ℂ) :
    normSq ((A ^ n) *ᵥ u) ≤ c ^ n * normSq u := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, pow_succ']
    calc normSq (A *ᵥ (A ^ n *ᵥ u)) ≤ c * normSq (A ^ n *ᵥ u) := hA _
      _ ≤ c * (c ^ n * normSq u) := mul_le_mul_of_nonneg_left ih hc
      _ = c * c ^ n * normSq u := by ring

theorem unip_normSq_col {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (j : Fin r) :
    normSq (M *ᵥ Pi.single j 1) = ∑ i, ‖M i j‖ ^ 2 := by
  unfold normSq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_single_one]
  rfl

theorem unip_normSq_single {r : ℕ} (j : Fin r) : normSq (Pi.single j (1 : ℂ)) = 1 := by
  unfold normSq
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem unip_diag_sq_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) (n : ℕ) (i : Fin r) :
    ‖(A ^ n) i i‖ ^ 2 ≤ c ^ n := by
  have h1 := unip_normSq_pow_le A c hc hA n (Pi.single i 1)
  rw [unip_normSq_col, unip_normSq_single, mul_one] at h1
  refine le_trans ?_ h1
  exact Finset.single_le_sum (f := fun k => ‖(A ^ n) k i‖ ^ 2) (fun k _ => by positivity)
    (Finset.mem_univ i)

theorem unip_hs_le {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) :
    ∑ a, ∑ b, ‖A a b‖ ^ 2 ≤ r * c := by
  rw [Finset.sum_comm]
  calc ∑ b, ∑ a, ‖A a b‖ ^ 2 = ∑ b : Fin r, normSq (A *ᵥ Pi.single b 1) :=
        Finset.sum_congr rfl fun b _ => (unip_normSq_col A b).symm
    _ ≤ ∑ _b : Fin r, c := by
        refine Finset.sum_le_sum fun b _ => ?_
        have h := hA (Pi.single b 1)
        rwa [unip_normSq_single, mul_one] at h
    _ = r * c := by simp

theorem unip_hs_sub_one {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) :
    ∑ a, ∑ b, ‖(A - 1) a b‖ ^ 2 = ∑ a, ∑ b, ‖A a b‖ ^ 2 - 2 * A.trace.re + r := by
  have key : ∀ a b, ‖(A - 1) a b‖ ^ 2 =
      ‖A a b‖ ^ 2 - (if a = b then 2 * (A a b).re - 1 else 0) := by
    intro a b
    by_cases h : a = b
    · subst h
      simp only [Matrix.sub_apply, Matrix.one_apply_eq, if_true, Complex.sq_norm,
        Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
      ring
    · simp [Matrix.sub_apply, Matrix.one_apply_ne h, h]
  simp_rw [key, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Matrix.trace, Complex.re_sum]
  simp [Finset.sum_sub_distrib, Finset.mul_sum]
  ring

theorem unip_exp_bound (r : ℕ) (hr : 1 ≤ r) : (r : ℝ) * (Real.exp (2 / (3 * r)) - 1) < 1 := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hx0 : 0 < 2 / (3 * (r : ℝ)) := by positivity
  set x : ℝ := 2 / (3 * (r : ℝ)) with hx
  have hxr : (r : ℝ) * x = 2 / 3 := by rw [hx]; field_simp
  have hx1 : x ≤ 2 / 3 := by nlinarith
  have hb := Real.exp_bound (x := x) (by rw [abs_of_pos hx0]; linarith) (n := 4) (by norm_num)
  rw [abs_of_pos hx0] at hb
  have hup := (abs_le.mp hb).2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hup
  norm_num at hup
  have hmain : Real.exp x - 1 < 3 / 2 * x := by
    nlinarith [pow_pos hx0 2, pow_pos hx0 3, pow_pos hx0 4, mul_le_mul_of_nonneg_left hx1 (le_of_lt (pow_pos hx0 3))]
  have hr0 : (0 : ℝ) < r := by linarith
  calc (r : ℝ) * (Real.exp x - 1) < r * (3 / 2 * x) := mul_lt_mul_of_pos_left hmain hr0
    _ = 1 := by rw [show (r : ℝ) * (3 / 2 * x) = 3 / 2 * (r * x) by ring, hxr]; norm_num

end ReciprocityTheory.MultiplicativeHeights
end

