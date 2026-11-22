import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0504
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0146
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0149
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0167
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0486
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0154
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0140
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationViaTruncation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0191
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0139
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0297
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageVanishesOpenCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0474
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.IsJointGenEig
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0458
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicGLNormOneSplit
section
open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitHomeo

open GroundTheory.Automorphic GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_splitCentre : Continuous (splitCentre E a) := by
  have e : splitCentre E a = fun t : ℝ =>
      Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) :=
    funext splitCentre_eq_scalar
  rw [e]
  refine Continuous.units_map _ ?_ |>.comp ((continuous_infId E).comp
    (continuous_expU.comp (continuous_pi fun _ => Complex.continuous_ofReal)))
  change Continuous fun x : Ad E => Matrix.diagonal fun _ : Fin a => x
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal

variable (E) in

def expIdele (t : ℝ) : IdeleGroup E := infId E (expU fun _ : InfinitePlace E => (t : ℂ))

theorem pInf_expIdele (t : ℝ) (w : InfinitePlace E) :
    pInf E (expIdele E t : Ad E) w = Complex.exp t := by
  have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  change pInf E (1 - sInf E 1 + sInf E _) w = _
  simp only [map_add, map_sub, map_one, h, sub_self, zero_add]
  rfl

theorem pFin_expIdele (t : ℝ) : pFin E (expIdele E t : Ad E) = 1 := by
  change (1 : Af E) - 0 + 0 = 1
  simp

theorem ideleModule_expIdele (t : ℝ) :
    (IdeleGroup.ideleModule E (expIdele E t) : ℝ) = Real.exp (Module.finrank ℚ E * t) := by
  have h1 : ∀ v : InfinitePlace E, ‖(expIdele E t : Ad E).1 v‖ = Real.exp t := fun v => by
    have := pInf_expIdele (E := E) t v
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
    refine (congrArg norm this).trans ?_
    rw [Complex.norm_exp, Complex.ofReal_re]
  have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(expIdele E t : Ad E).2 v‖ = 1 := fun v => by
    change ‖pFin E (expIdele E t : Ad E) v‖ = 1
    rw [pFin_expIdele]
    exact norm_one
  rw [IdeleGroup.ideleModule_eq]
  change (∏ v : InfinitePlace E, ‖(expIdele E t : Ad E).1 v‖ ^ v.mult) *
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(expIdele E t : Ad E).2 v‖ = _
  simp only [h1, h2, finprod_one, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← Real.exp_nat_mul]

theorem det_splitCentre (t : ℝ) : AdelicGLn.det E a (splitCentre E a t) = expIdele E t ^ a := by
  rw [splitCentre_eq_scalar]
  refine Units.ext ?_
  change (Matrix.scalar (Fin a) (expIdele E t : Ad E)).det = _
  simp

theorem ideleModule_det_splitCentre (t : ℝ) :
    (IdeleGroup.ideleModule E (AdelicGLn.det E a (splitCentre E a t)) : ℝ) =
      Real.exp ((a * Module.finrank ℚ E : ℝ) * t) := by
  rw [det_splitCentre, map_pow, Positive.val_pow, ideleModule_expIdele, ← Real.exp_nat_mul]
  congr 1
  ring

def splitDeg (E : Type) [Field E] [NumberField E] (a : ℕ) (g : GA E a) : ℝ :=
  Real.log (IdeleGroup.ideleModule E (AdelicGLn.det E a g)) / (a * Module.finrank ℚ E : ℝ)

theorem continuous_splitDeg : Continuous (splitDeg E a) := by
  refine Continuous.div_const (Continuous.log ?_ fun g => ?_) _
  · exact continuous_subtype_val.comp
      (IdeleGroup.continuous_ideleModule.comp (AdelicGLn.continuous_det E a))
  · exact (IdeleGroup.ideleModule E (AdelicGLn.det E a g)).2.ne'

theorem coeff_ne_zero (ha : 0 < a) : (a * Module.finrank ℚ E : ℝ) ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.2 ha.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')

theorem splitCentre_neg_mul_mem (ha : 0 < a) (g : GA E a) :
    splitCentre E a (-splitDeg E a g) * g ∈ Reduction.normOneGL E a := by
  have hc := coeff_ne_zero (E := E) ha
  have hpos := (IdeleGroup.ideleModule E (AdelicGLn.det E a g)).2
  rw [Reduction.mem_normOneGL, map_mul, map_mul, Positive.val_mul, ideleModule_det_splitCentre,
    mul_neg, splitDeg, mul_div_cancel₀ _ hc, Real.exp_neg, Real.exp_log hpos, inv_mul_cancel₀ hpos.ne']

theorem splitDeg_splitCentre_mul (ha : 0 < a) (x : Reduction.normOneGL E a) (t : ℝ) :
    splitDeg E a (splitCentre E a t * (x : GA E a)) = t := by
  have hc := coeff_ne_zero (E := E) ha
  have hx : (IdeleGroup.ideleModule E (AdelicGLn.det E a (x : GA E a)) : ℝ) = 1 :=
    Reduction.mem_normOneGL.1 x.2
  rw [splitDeg, map_mul, map_mul, Positive.val_mul, ideleModule_det_splitCentre, hx, mul_one,
    Real.log_exp, mul_div_cancel_left₀ _ hc]

theorem splitCentre_neg_mul_self (t : ℝ) (g : GA E a) :
    splitCentre E a (-t) * (splitCentre E a t * g) = g := by
  rw [← mul_assoc, ← splitCentre_add, neg_add_cancel, splitCentre_zero, one_mul]

theorem exists_homeomorph (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ha : 0 < a) :
    ∃ e : Reduction.normOneGL E a × ℝ ≃ₜ GA E a, ∀ x t, e (x, t) = splitCentre E a t * (x : GA E a) := by
  refine ⟨{
    toFun := fun p => splitCentre E a p.2 * (p.1 : GA E a)
    invFun := fun g => (⟨splitCentre E a (-splitDeg E a g) * g, splitCentre_neg_mul_mem ha g⟩, splitDeg E a g)
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }, fun _ _ => rfl⟩
  · rintro ⟨x, t⟩
    refine Prod.ext (Subtype.ext ?_) (splitDeg_splitCentre_mul ha x t)
    change splitCentre E a (-splitDeg E a (splitCentre E a t * (x : GA E a))) * _ = _
    rw [splitDeg_splitCentre_mul ha x t, splitCentre_neg_mul_self]
  · intro g
    change splitCentre E a (splitDeg E a g) * (splitCentre E a (-splitDeg E a g) * g) = g
    simpa using splitCentre_neg_mul_self (-splitDeg E a g) g
  · exact (continuous_splitCentre.comp continuous_snd).mul
      (continuous_subtype_val.comp continuous_fst)
  · refine Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_splitDeg
    exact (continuous_splitCentre.comp continuous_splitDeg.neg).mul continuous_id

end GlobalTheory.CompanionTheory.SplitHomeo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineGradedCohomologyVanishingStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_graded_cohomology_vanishing : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q]
    (V : X.Opens) (hV : IsAffineOpen V) (s r j : ℕ), r < s → j ≠ r → Subsingleton (HQ (KS q s {V}) r ((r : ℤ) + 1) j) := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.gr_aff | exact GlobalTheory.CompanionTheory.GrForm.gr_aff | (intros; apply GlobalTheory.CompanionTheory.GrForm.gr_aff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineGradedQuotientVanishAboveDim
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.GrTop

variable {X : Scheme.{0}}

theorem iInf_basicOpen {V : X.Opens} {ι : Type} (f : ι → Γ(X, V)) (S : Finset ι) (hS : S.Nonempty) :
    (⨅ α ∈ S, X.basicOpen (f α)) = X.basicOpen (∏ α ∈ S, f α) := by
  classical
  induction hS using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
    rw [Finset.cons_eq_insert, Finset.iInf_insert, Finset.prod_insert (by simpa using ha), Scheme.basicOpen_mul, ih]

theorem exists_cover {O : Type} [CommRing O] (q : X ⟶ Spec (CommRingCat.of O)) (d : ℕ) [SmoothOfRelativeDimension d q]
    {V : X.Opens} (hV : IsAffineOpen V) :
    ∃ (ι : Type) (_ : Fintype ι) (f : ι → Γ(X, V)), (⨆ α, X.basicOpen (f α)) = V ∧
      ∀ α, Nonempty (Coord q (X.basicOpen (f α)) d) := by
  classical
  have h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d) (q.appLE ⊤ V le_top).hom :=
    HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension d) q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  have key : ∀ x : V, ∃ f : Γ(X, V), (x : X) ∈ X.basicOpen f ∧ Nonempty (Coord q (X.basicOpen f) d) := by
    intro x
    obtain ⟨f, hf, hst⟩ := GlobalTheory.CompanionTheory.CovEx.exists_basicOpen (RingHom.IsStandardSmoothOfRelativeDimension d)
      RingHom.isStandardSmoothOfRelativeDimension_respectsIso q hV h x.2
    obtain ⟨g, hg, he⟩ := hst.exists_etale_mvPolynomial
    exact ⟨f, hf, GlobalTheory.CompanionTheory.CovEx.coord_basicOpen q hV f g hg he⟩
  choose f hf hc using key
  obtain ⟨t, ht⟩ := hV.isCompact.elim_finite_subcover (fun x : V => (X.basicOpen (f x) : Set X))
    (fun x => (X.basicOpen (f x)).2) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hf _⟩)
  refine ⟨t, inferInstance, fun a => f a.1, le_antisymm (iSup_le fun a => X.basicOpen_le _) ?_, fun a => hc a.1⟩
  intro x hx
  obtain ⟨y, hy⟩ := Set.mem_iUnion.1 (ht hx)
  obtain ⟨hy, hxy⟩ := Set.mem_iUnion.1 hy
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hxy⟩

end GlobalTheory.CompanionTheory.GrTop

namespace GlobalTheory.CompanionTheory.GrTop

theorem twoVariableSeriesVanishesBelowDegree_one_shiftVariable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s r j : ℕ)
    (hsr : s ≤ r) : Subsingleton (HQ (KS q s {V}) (r : ℤ) ((r : ℤ) + 1) j) := by
  have hz : ∀ (T : (KS q s {V}).FullSubcategory)
      (x : (sq (sFil (KS q s {V}) (r : ℤ)) (sFil (KS q s {V}) ((r : ℤ) + 1))).obj T), x = 0 := by
    intro T x
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    have hy2 : (show T.obj.B from y) ∈ T.obj.pdPow ((r : ℤ).toNat) := hy
    rw [Int.toNat_natCast] at hy2
    have hy' : (show T.obj.B from y) ∈ T.obj.pdPow s := T.obj.pdPow_anti hsr hy2
    rw [T.property.1.1, Ideal.mem_bot] at hy'
    subst hy'
    rfl
  refine ⟨fun a b => ?_⟩
  obtain ⟨z, hz1, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 a
  obtain ⟨z', hz1', rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ j).1 b
  have e : z = z' := funext fun σ => (hz _ _).trans (hz _ _).symm
  subst e
  rfl

end GlobalTheory.CompanionTheory.GrTop

namespace GlobalTheory.CompanionTheory.GrTop

theorem grTop (hG : KH.LocGr) (hP : KH.PolyTf) : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (d : ℕ) [SmoothOfRelativeDimension d q] (V : X.Opens), IsAffineOpen V →
    ∀ (s : ℕ) (r : ℤ) (j : ℕ), (d : ℤ) < r → Subsingleton (HQ (KS q s {V}) r (r + 1) j) := by
  intro K _ _ X q d _ V hV s r j hr
  lift r to ℕ using (by omega)
  have hdr : d < r := by exact_mod_cast hr
  rcases le_or_gt s r with hsr | hsr
  · exact twoVariableSeriesVanishesBelowDegree_one_shiftVariable q V s r j hsr
  obtain ⟨ι, _, f, hcov, hc⟩ := exists_cover q d hV
  let U : ι → X.Opens := fun α => X.basicOpen (f α)
  have hloc : ∀ S : Finset ι, S.Nonempty → ∀ j, Subsingleton (HU (sq (thFil (smFun X q) (r : ℤ))
      (thFil (smFun X q) ((r : ℤ) + 1))) (St (TF 1 s) {⨅ α ∈ S, U α}) j) := by
    intro S hS j
    obtain ⟨α, hα⟩ := id hS
    have haff : IsAffineOpen (⨅ α ∈ S, U α) := by
      change IsAffineOpen (⨅ α ∈ S, X.basicOpen (f α))
      rw [iInf_basicOpen f S hS]
      exact hV.basicOpen _
    obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (hc α).some (iInf₂_le α hα) haff
    exact GlobalTheory.CompanionTheory.KIso.loc_vanish q hG hP c' r s hdr (by omega) j
  have hglob := (GlobalTheory.T.stable_cover_cech_vanishing.1 (sq (thFil (smFun X q) (r : ℤ)) (thFil (smFun X q) ((r : ℤ) + 1))) (TF 1 s) U 0).2.1
    hloc j
  have h2 : KS q s (Set.range U) ≤ KS q s {V} := by
    rintro T ⟨hT, W, ⟨α, rfl⟩, hW⟩
    exact ⟨hT, V, rfl, fun x hx => X.basicOpen_le (f α) (hW hx)⟩
  have hc' : ∀ W ∈ ({V} : Set X.Opens), W ≤ sSup (Set.range U) := by
    intro W hW
    rw [Set.mem_singleton_iff.1 hW, sSup_range]
    exact hcov.ge
  have b := (GlobalTheory.T.cech_refinement_cohomology_bijective (TF 1 s : ObjectProperty (Thick (smFun X q))) (Or.inl ⟨rfl, 1, s, rfl⟩) (Set.range U) {V} h2 hc' j).1 (r : ℤ) ((r : ℤ) + 1)
  have : Subsingleton (HQ (KS q s (Set.range U)) (r : ℤ) ((r : ℤ) + 1) j) := hglob
  exact ⟨fun a c => b.1 (@Subsingleton.elim _ this _ _)⟩

end GlobalTheory.CompanionTheory.GrTop

namespace GlobalTheory.CompanionTheory.GrTop

theorem grTop_main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    [SmoothOfRelativeDimension d q] (V : X.Opens), IsAffineOpen V → ∀ (s : ℕ) (r : ℤ) (j : ℕ), (d : ℤ) < r →
    Subsingleton (HQ (KS q s {V}) r (r + 1) j) :=
  @grTop GlobalTheory.CompanionTheory.LocGrStep.loc_gr GlobalTheory.CompanionTheory.PolyTfCon.polyTf

end GlobalTheory.CompanionTheory.GrTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnalyticOrthogonalVanishingStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_orthogonal_vanishing : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (F : ℕ → ℝ → H) (M C : ℝ) (u : H), (∀ k t, HasDerivAt (F k) (F (k + 1) t) t) → (∀ k t, ‖F k t‖ ≤ M * C ^ k * (k.factorial : ℝ)) → (∀ k, inner ℂ u (F k 0) = 0) → ∀ t, inner ℂ u (F 0 t) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds | exact GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds | (intros; apply GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageVanishesOpenCellStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_vanishes_open_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (h0 : eO ψ f = 0)
    (p : Mir k ((i + 1) + t + 1)) (hp : p ∉ Cl k i t),
  AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f p := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.LocO.main | exact GlobalTheory.CompanionTheory.BZPhiPG.LocO.main | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.LocO.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

def CovAt {D : D7} {n : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {θ : InfFam D}
    (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (γ : G D n) : Prop :=
  ∀ (v : Mx D V.rank (n + n)) (Φ Ψ : schwartzA θ V.rank n), Ψ.1 = Heisenberg₂ ψ V v Φ.1 →
    (ω γ Ψ).1 = Heisenberg₂ ψ V (HMul.hMul v (mat γ⁻¹)) (ω γ Φ).1

def FieldGen (K : Type) [Field K] (σ : K →+* K) (n : ℕ) : Prop :=
  ∀ T : Matrix (Fin (n + n)) (Fin (n + n)) K → Prop, (∀ g h, T g → T h → T (g * h)) →
    (∀ a : Matrix (Fin n) (Fin n) K, IsUnit a.det → T (mA σ a)) →
    (∀ b : Matrix (Fin n) (Fin n) K, cT σ b = b → T (nB b)) → T (Jm K n) →
    ∀ g, IsUnit g.det → IsUnitary σ (Jm K n) g → T g

variable {D : D7} {n : ℕ}

theorem mat_mul' (g h : G D n) : mat (g * h) = mat g * mat h := by
  unfold mat; rw [map_mul]; rfl

theorem mat_one' : mat (1 : G D n) = 1 := by
  unfold mat; rw [map_one]; rfl

theorem mat_inv_mul' (g : G D n) : mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel, mat_one']

theorem mat_mul_inv' (g : G D n) : mat g * mat g⁻¹ = 1 := by
  rw [← mat_mul', mul_inv_cancel, mat_one']

theorem mat_injective' : Function.Injective (mat : G D n → Mx D (n + n) (n + n)) :=
  fun _ _ e => Subtype.ext (Units.ext e)

theorem x_part_mul_block {m : ℕ} (v : Mx D m (n + n)) (A B C E : Mx D n n) :
    xPart (HMul.hMul v (blk4 A B C E) : Mx D m (n + n)) = HMul.hMul (xPart v) A + HMul.hMul (yPart v) C := by
  funext i j
  simp only [xPart, yPart, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]

theorem y_part_mul_block {m : ℕ} (v : Mx D m (n + n)) (A B C E : Mx D n n) :
    yPart (HMul.hMul v (blk4 A B C E) : Mx D m (n + n)) = HMul.hMul (xPart v) B + HMul.hMul (yPart v) E := by
  funext i j
  simp only [xPart, yPart, blk4, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← finSumFinEquiv.sum_comp]
  simp [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂]

theorem submatrix_fromBlocks_mul {R : Type} [CommRing R] (A B C E A' B' C' E' : Matrix (Fin n) (Fin n) R) :
    blk4 A B C E * blk4 A' B' C' E' = blk4 (A * A' + B * C') (A * B' + B * E') (C * A' + E * C') (C * B' + E * E') := by
  simp only [blk4]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one {R : Type} [CommRing R] : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  simp only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem covAt_mul {ψ : AddChar (AF D.host.F) ℂ} {V : HSp D} {θ : InfFam D}
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {γ₁ γ₂ : G D n}
    (h₁ : CovAt ψ V ω γ₁) (h₂ : CovAt ψ V ω γ₂) : CovAt ψ V ω (γ₁ * γ₂) := by
  intro v Φ Ψ hΨ
  have e1 := h₁ _ (ω γ₂ Φ) (ω γ₂ Ψ) (h₂ v Φ Ψ hΨ)
  rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, e1, mul_inv_rev, mat_mul', Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.EisCovar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirMemCenterEnveloping
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.Inh.CapelliCasimir
open Finset

theorem mem_subalgebra_of_dual {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (x : A)
    (h : ∀ f : A →ₗ[ℂ] ℂ, (∀ z ∈ S, f z = 0) → f x = 0) : x ∈ S := by
  by_contra hx
  have hx' : x ∉ Subalgebra.toSubmodule S := hx
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem hx'
  exact hf1 (h f fun z hz => LinearMap.mem_ker.1 (hf2 hz))

theorem cas_mem_of_qdet_mem {A : Type} [Ring A] [Algebra ℂ A] (S : Subalgebra ℂ A) (n : ℕ)
    (E : Fin n → Fin n → A) (hE : Formalism.REAL.GlRel E)
    (hcap : ∀ Y : ℂ, Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) ∈ S) : Formalism.REAL.Cas E ∈ S := by
  obtain ⟨Rm, hR⟩ := _root_.GlobalTheory.qdet_top_three_orders A n E
  by_cases hn : 2 ≤ n
  swap
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · simp [Formalism.REAL.Cas]
    · have h0 := hcap 0
      rw [hR] at h0
      have h1 : E 0 0 ∈ S := by
        simpa [Finset.filter_singleton] using h0
      have : Formalism.REAL.Cas E = E 0 0 * E 0 0 := by simp [Formalism.REAL.Cas]
      rw [this]
      exact Subalgebra.mul_mem _ h1 h1
  set ρ : Fin n → ℂ := fun l => ((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ) with hρ
  have hρ0 : ∑ l, ρ l = 0 := by
    have h1 : ∑ l, ρ l = ∑ l, ρ (Fin.rev l) := (Equiv.sum_comp Fin.revPerm ρ).symm
    have h2 : ∑ l, ρ (Fin.rev l) = - ∑ l, ρ l := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      have := l.2
      simp only [hρ, Fin.val_rev]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linear_combination (h1.trans h2) / 2
  have core := fun (f : A →ₗ[ℂ] ℂ) (hf : ∀ z ∈ S, f z = 0) =>
    scalar_core n hn ρ (fun _ => 0) (fun i => f (E i i))
      (fun i j => f (E i i * E j j - E j i * E i j)) (fun d => f (Rm d)) (f 1)
      (((n : ℂ) - 1) / 2)
      (fun Y => by
        have h1 := hf _ (hcap Y)
        rw [hR] at h1
        have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
        simp only [map_add, map_sum, map_smul, smul_eq_mul, add_sub_assoc] at h1
        simp only [e, mul_zero] at h1 ⊢
        exact h1)
  have hT : ∑ i, E i i ∈ S := by
    refine mem_subalgebra_of_dual S _ fun f hf => ?_
    have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
    have := (core f hf).1
    rw [hρ0, e] at this
    simp only [map_sum]
    linear_combination this
  have hW : (2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i ∈ S := by
    refine mem_subalgebra_of_dual S _ fun f hf => ?_
    have e : f 1 = 0 := hf 1 (Subalgebra.one_mem _)
    have h2 := (core f hf).2
    rw [e] at h2
    simp only [sum_erase_eq_sub (mem_univ _), hρ0] at h2
    simp only [map_sub f, map_sum, map_smul, smul_eq_mul]
    have h5 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) * f (E i i)
        = - (2 * ∑ i, (0 - ρ i) * f (E i i)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [hρ]; ring
    rw [h5]
    simp only [map_sub f] at h2
    linear_combination h2
  have h3 := sq_sub_cas E hE
  have : Formalism.REAL.Cas E = (∑ i, E i i) * (∑ i, E i i)
      - ((2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i) := by
    rw [← h3]; abel
  rw [this]
  exact Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hT hT) hW

theorem cas_mem_Zalg : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ),
    Formalism.REAL.Cas (Eop (a := a) τ) ∈ Zalg E a := by
  intro F _ _ _ n τ
  have hcap : ∀ Y : ℂ, cap (a := n) τ Y ∈ Zalg F n := fun Y =>
    Algebra.subset_adjoin (show cap (a := n) τ Y ∈ {z | ∃ τ u, z = cap τ u} from ⟨τ, Y, rfl⟩)
  exact cas_mem_of_qdet_mem (Zalg F n) n (Eop τ) (glRel_Eop τ) hcap

end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasselmanFirstPropertyStatement
section
open GlobalTheory.PRep PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casselman_first_property : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], PositivityTheory.SphericalProduct.A1 G := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract | exact GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract | (intros; apply GlobalTheory.CompanionTheory.Casselman.hecke_dominant_mul_abstract <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesLieActionStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_commutes_lie_action : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (z : Module.End ℂ (Sm E a)), z ∈ Zalg E a → ∀ X, z * lie E a X = lie E a X * z := by
  first | exact @GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie | exact GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie | (intros; apply GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteCenterMonicAnnihilatorStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofinite_center_monic_annihilator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (J : Set (Module.End ℂ (Sm E n))), Cofin J → ∀ z ∈ Zalg E n, ∃ p : Polynomial ℂ, p.Monic ∧ ∀ φ : Sm E n, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed | exact GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed | (intros; apply GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed <;> assumption)
end

