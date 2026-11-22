import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0018
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0023
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0005
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedCohomology.ExistsSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0001
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.PfDict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0208

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrInert
section
noncomputable section

namespace GlobalTheory.ThK.Dbl.Inert

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.LFun.InertChart PositivityTheory.ThK PositivityTheory.ThKH.Iwas PositivityTheory.ThKH.Locpair PositivityTheory.ThKH.Locrep
open GlobalTheory.EmbChart (atPlace evFin_atPlace atPlace_mul_right tensAt)
open GlobalTheory.Doubling (absE)
open GlobalTheory.Doubling (leviOf blkMat dblGram leviMat KeepsDiag)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables

section Alg

variable {L : Type} [CommRing L] {n : ℕ} (a : GL (Fin n) L)

abbrev dg (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n ⊕ Fin n) (Fin n) R := diagCols (Fin n)

def dA : Matrix (Fin n ⊕ Fin n) (Fin (n + n)) L := (Matrix.fromBlocks a.1 0 0 a.1).submatrix id finSumFinEquiv.symm

def dB : Matrix (Fin (n + n)) (Fin n ⊕ Fin n) L := (Matrix.fromBlocks (a⁻¹).1 0 0 (a⁻¹).1).submatrix finSumFinEquiv.symm id

theorem dA_dB : dA a * dB a = 1 := by
  rw [dA, dB, Matrix.submatrix_mul_equiv]; simp [Matrix.fromBlocks_multiply]

theorem dB_dA : dB a * dA a = 1 := (Matrix.mul_eq_one_comm_of_equiv finSumFinEquiv).1 (dA_dB a)

theorem dA_gram (c : L →+* L) (J : Matrix (Fin n) (Fin n) L) :
    cT c (dA a) * (dbl J)ᵀ * dA a = dblGram finSumFinEquiv (cT c a.1 * Jᵀ * a.1) := by
  have : cT c (Matrix.fromBlocks a.1 0 0 a.1) * (dbl J)ᵀ * Matrix.fromBlocks a.1 0 0 a.1 =
      Matrix.fromBlocks (cT c a.1 * Jᵀ * a.1) 0 0 (-(cT c a.1 * Jᵀ * a.1)) := by
    simp [cT, dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [dblGram, blkMat, ← this]; rfl

theorem dA_conj (X : Matrix (Fin (n + n)) (Fin (n + n)) L) : dA a * X * dB a =
    Matrix.fromBlocks a.1 0 0 a.1 * X.submatrix finSumFinEquiv finSumFinEquiv * Matrix.fromBlocks (a⁻¹).1 0 0 (a⁻¹).1 := by
  conv_lhs => rw [show X = (X.submatrix finSumFinEquiv finSumFinEquiv).submatrix finSumFinEquiv.symm finSumFinEquiv.symm by simp]
  rw [dA, dB, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]; rfl

theorem dA_blk (x : Matrix (Fin n) (Fin n) L) :
    dA a * blkMat finSumFinEquiv x (1 : Matrix (Fin n) (Fin n) L) * dB a = Matrix.fromBlocks (a.1 * x * (a⁻¹).1) 0 0 1 := by
  rw [dA_conj, GlobalTheory.Doubling.submatrix_blkMat]; simp [Matrix.fromBlocks_multiply]

theorem dA_par {X : Matrix (Fin (n + n)) (Fin (n + n)) L} (h : KeepsDiag finSumFinEquiv X) :
    dA a * X * dB a * dg n L = dg n L * (a.1 * leviMat finSumFinEquiv X * (a⁻¹).1) := by
  rw [dA_conj, ← Matrix.fromBlocks_toBlocks (X.submatrix _ _)]
  simp only [dg, diagCols, Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add, ← Matrix.add_mul]
  rw [h]; rfl

theorem dA_sub (X : Matrix (Fin (n + n)) (Fin (n + n)) L) {i j : Fin n → Fin n ⊕ Fin n} (hi : i ∈ ({.inl, .inr} : Set _))
    (hj : j ∈ ({.inl, .inr} : Set _)) : (a⁻¹).1 * (dA a * X * dB a - 1).submatrix i j * a.1 =
      (X.submatrix finSumFinEquiv finSumFinEquiv - 1).submatrix i j := by
  have e : ∀ N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L, (a⁻¹).1 * N.submatrix i j * a.1 =
      (Matrix.fromBlocks (a⁻¹).1 0 0 (a⁻¹).1 * N * Matrix.fromBlocks a.1 0 0 a.1).submatrix i j := fun N => by
    conv_rhs => rw [← Matrix.fromBlocks_toBlocks N]
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add] <;> rfl
  have d : Matrix.fromBlocks (a⁻¹).1 0 0 (a⁻¹).1 * Matrix.fromBlocks a.1 0 0 a.1 = 1 := by simp [Matrix.fromBlocks_multiply]
  rw [e, dA_conj, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, d, ← Matrix.mul_assoc, ← Matrix.mul_assoc, d, Matrix.one_mul,
    Matrix.mul_assoc, d, Matrix.mul_one]

end Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {v : Pl F} {w : HeightOneSpectrum (𝓞 E)} {Y : Spc F E n}

theorem chi_at (hw : IsInertAt F E v w) {χ : Chr F E} (hr : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0)
    (hu : UnrAt χ w) (y : (w.adicCompletion E)ˣ) : χ (locIdele F w y) = 1 :=
  GlobalTheory.InertChars.locIdele_eq_of_inert hw χ 1 (hr.triv_of_even (by simp)) hu (fun _ _ => map_one Circle.toUnits) y

theorem abs_at (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E}
    (hc : IsConjAt σ h c) (hv : ∀ x, Valued.v (c x) = Valued.v x) {x : (AE F E)ˣ} (hx : At (evFin F v) (x.1 - 1))
    {y : (w.adicCompletion E)ˣ} (e : piE h x.1 = y) (z : ℂ) : ((absE F E x : ℝ) : ℂ) ^ z = secVal (qV F v) 1 z y := by
  set u := GlobalTheory.Doubling.unitFin F E v x
  have e' : toCompl h u.1 = y := e
  have h0 : Valued.v y.1 ≠ 0 := (map_ne_zero _).2 y.ne_zero
  have h1 : Valued.v y.1 = WithZero.exp (-ordL y.1) := by
    rw [ordL, dif_neg h0, neg_neg]; exact (WithZero.coe_unzero h0).symm
  have n0 : Algebra.norm (Fv F v) u.1 ≠ 0 := (u.isUnit.map _).ne_zero
  have h2 : Valued.v (Algebra.norm (Fv F v) u.1) = WithZero.exp (-(2 * ordL y.1)) := by
    have h3 := congrArg (toCompl h) (GlobalTheory.Doubling.algebraMap_norm_eq hσ u.1)
    rw [map_mul, ← hc, e', show toCompl h (algebraMap _ _ (Algebra.norm (Fv F v) u.1)) = complMap h (Algebra.norm (Fv F v) u.1) from
      (toCompl_tmul h _ 1).trans (by rw [map_one, mul_one]; rfl)] at h3
    have h4 := congrArg Valued.v h3
    rw [valued_complMap h n0, isUnram_iff.1 (isUnram_of_isInertAt hw) w h, pow_one, map_mul, hv, h1, ← WithZero.exp_add] at h4
    rw [h4]; congr 1; ring
  have h5 : (absE F E x : ℝ) = (qV F v : ℝ) ^ ((-(2 * ordL y.1) : ℤ) : ℝ) := by
    rw [GlobalTheory.InertChars.eq_ideleAt_of_at x hx, GlobalTheory.Doubling.absE_ideleAt, GlobalTheory.Doubling.absEv_apply, coe_nnnorm,
      FinitePlace.norm_def, h2, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, Real.rpow_intCast]
    exact NNReal.coe_zpow _ _
  rw [h5, ← Complex.cpow_mul_ofReal_nonneg (Nat.cast_nonneg _), secVal, MonoidHom.one_apply, Units.val_one, one_mul]
  push_cast
  congr 1; ring

theorem frame {B : Base F E} {r s : ℕ} (hσ : IsCMExt F E σ) (hY : Y.IsHerm σ B r s) (hw : IsInertAt F E v w) {h : w.under (𝓞 F) = v}
    {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c) :
    ∃ a, IsFrameAt w Y.L a ∧ cT c a.1 * ((incM F Y.J).map (piE h))ᵀ * a.1 = antiJ _ n := by
  have hd : ((1 : E) • Y.Jᵀ).det ≠ 0 := by rw [one_smul, Matrix.det_transpose]; exact (Vac.herm_det hY).ne_zero
  obtain ⟨a, h1, h2⟩ := exists_frame_antiJ hσ (J := (1 : E) • Y.Jᵀ) ⟨fun i j => by simp [hY.herm], hd⟩ hY.lat.fg hY.lat.span_eq_top hw hc
    (PositivityTheory.ThKG.Loc.Iwa.selfDual_of hd hY.lat (fun y hy x hx => SelfDual.inclR_mem_intLoc v (by
      rw [PositivityTheory.ThKG.Loc.Iwa.hE_smul, one_mul]; exact ⟨⟨_, (hY.dual y).1 hy x hx⟩, rfl⟩)) (s := 1)
      ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top) fun y hy => by
        simp only [OneMemClass.coe_one, map_one, one_smul]
        refine (hY.dual y).2 fun x hx => ?_
        obtain ⟨o, ho⟩ := hy x hx
        rw [PositivityTheory.ThKG.Loc.Iwa.hE_smul, one_mul] at ho
        rw [← ho]; exact o.isIntegral_coe)
  refine ⟨a, h1, Eq.trans ?_ h2⟩
  congr 2
  exact Matrix.ext fun i j => (piE_incl h _).trans (by simp)

theorem one_map {ι R : Type} [DecidableEq ι] [CommRing R] (φ : AE F E →+* R) : (1 : Matrix ι ι (AE F E)).map φ = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem zero_map {R : Type} [CommRing R] (φ : AE F E →+* R) : (0 : Matrix (Fin n) (Fin n) (AE F E)).map φ = 0 :=
  Matrix.map_zero _ (map_zero _)

theorem diag_map {R : Type} [CommRing R] (φ : AE F E →+* R) :
    (dg n (AE F E)).map φ = dg n R := by
  rw [dg, diagCols, Matrix.fromRows_map, one_map]; rfl

variable (hw : IsInertAt F E v w) {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c)
  {a : GL (Fin n) (w.adicCompletion E)} (hH : cT c a.1 * ((incM F Y.J).map (piE h))ᵀ * a.1 = antiJ _ n)

def lift1 : GU c n →* UA σ Y.J := liftW hw hc a.mul_inv a.inv_mul hH

def lift2 : GD c n →* G2 σ Y := liftW hw hc (dA_dB a) (dB_dA a) (by
  rw [← hH, ← dA_gram, dbl, dbl, Matrix.fromBlocks_map, zero_map, Matrix.map_neg _ (map_neg _)])

theorem mat_lift1 (x : GU c n) : mat (lift1 hw hc hH x) = up hw h _ (a.1 * x.1.1 * (a⁻¹).1) := rfl

theorem mat_lift2 (x : GD c n) : mat2 (lift2 hw hc hH x) = up hw h _ (dA a * x.1.1 * dB a) := rfl

theorem lift_emb (x : GU c n) : IsEmb (lift1 hw hc hH x) 1 (lift2 hw hc hH (io1 c n x)) := by
  rw [IsEmb, mat_lift1, mat_lift2, show mat (1 : UA σ Y.J) = 1 from rfl]
  refine extW hw h ?_ ?_
  · rw [up_pi, Matrix.fromBlocks_map, zero_map, one_map, up_pi]
    exact dA_blk a _
  · rw [up_aw, Matrix.fromBlocks_map, zero_map, one_map, up_aw, Matrix.fromBlocks_one]

theorem lift_mem (ha : IsFrameAt w Y.L a) {B : Base F E} {K : Subgroup (G2 σ Y)} (hK : IsStab2 B K) {k : GD c n}
    (hk : k ∈ KD c n) : lift2 hw hc hH k ∈ K := by
  have key : ∀ x ∈ KD c n, At (evFin F v) (mat2 (lift2 hw hc hH x) - 1) ∧ ∀ i j : Fin n → Fin n ⊕ Fin n,
      i ∈ ({.inl, .inr} : Set _) → j ∈ ({.inl, .inr} : Set _) → ∀ z ∈ latW Y v,
        (mat2 (lift2 hw hc hH x) - 1).submatrix i j *ᵥ z ∈ latW Y v := fun x hx => by
    rw [mat_lift2]
    refine ⟨up_at hw h _, fun i j hi hj => (stab_iff hw h ha _).2 fun l m => ?_⟩
    rw [← Matrix.submatrix_map, Matrix.map_sub _ (map_sub _), one_map, up_pi, dA_sub a _ hi hj]
    exact sub_mem ((mem_GLint_iff.1 (show x.1 ∈ GLint _ (intL _) from hx.2)).1 _ _) (one_int _ _)
  refine mem_K (v := v) hK ?_
  rintro x (rfl | rfl)
  · exact key k hk
  · rw [← map_inv]; exact key _ (inv_mem hk)

theorem lift_par (p : PD c n) : ∃ t, IsPar (lift2 hw hc hH p) t ∧ At (evFin F v) ((Matrix.GeneralLinearGroup.det t).1 - 1) ∧
    piE h (Matrix.GeneralLinearGroup.det t).1 = aD c n p := by
  obtain ⟨t, ht⟩ : ∃ t : GL (Fin n) (AE F E), t.1 = up hw h _ (a.1 * leviMat finSumFinEquiv p.1.1.1 * (a⁻¹).1) :=
    ⟨Units.map ((up hw h _).comp (conjM a.mul_inv a.inv_mul)) (leviOf finSumFinEquiv _ p), rfl⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · change mat2 (lift2 hw hc hH p) * dg n (AE F E) = dg n (AE F E) * t.1
    rw [mat_lift2, ht]
    refine extW hw h ?_ ?_
    · rw [Matrix.map_mul, Matrix.map_mul, diag_map, up_pi, up_pi]
      exact dA_par a (GlobalTheory.Doubling.mem_siegelOf.1 p.2)
    · rw [Matrix.map_mul, Matrix.map_mul, up_aw, up_aw, Matrix.one_mul, Matrix.mul_one]
  · rw [Matrix.GeneralLinearGroup.val_det_apply, ht, up, MonoidHom.comp_apply, det_liftM]
    rw [show ∀ y, liftE E v y - 1 = tensAt E v (y - 1) from fun y => add_sub_cancel_left _ _]
    exact at_tensAt v _
  · rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, RingHom.mapMatrix_apply, ht, up_pi, Matrix.det_units_conj]
    rfl

theorem mem_locGrp {g : UA σ Y.J} (hg : g ∈ locGrp σ Y v) : At (evFin F v) (g.1.1 - 1) :=
  (Subgroup.closure_le (USub σ Y v)).2 (fun _ h => h) hg

theorem inert_lift_mem_local_group (x : GU c n) : lift1 hw hc hH x ∈ locGrp σ Y v := Subgroup.subset_closure (by
  change At (evFin F v) (mat (lift1 hw hc hH x) - 1)
  rw [mat_lift1]
  exact up_at hw h _)

def chartW [IsTopologicalRing (AE F E)] : locGrp σ Y v ≃ₜ* GU c n where
  toFun g := downW hc a.mul_inv a.inv_mul hH g.1
  invFun x := ⟨lift1 hw hc hH x, inert_lift_mem_local_group hw hc hH x⟩
  left_inv g := Subtype.ext (lift_down hw hc a.mul_inv a.inv_mul hH (g := g.1) (mem_locGrp g.2))
  right_inv := down_lift hw hc a.mul_inv a.inv_mul hH
  map_mul' g g' := map_mul (downW hc a.mul_inv a.inv_mul hH) g.1 g'.1
  continuous_toFun := (continuous_downW hw hc a.mul_inv a.inv_mul hH).comp continuous_subtype_val
  continuous_invFun := (continuous_liftW hw hc a.mul_inv a.inv_mul hH).subtype_mk (inert_lift_mem_local_group hw hc hH)

include hw in
theorem down_mem (ha : IsFrameAt w Y.L a) (g : UA σ Y.J) : downW hc a.mul_inv a.inv_mul hH g ∈ KU c n ↔ IntAt v g := by
  have hat : ∀ z ∈ latW Y v, At (evFin F v) z := fun z hz => ((mem_latW_iff hw h Y z).1 hz).1
  have e : ∀ x : GU c n, x ∈ KU c n ↔ (∀ i j, x.1.1 i j ∈ Ov E w) ∧ ∀ i j, (x⁻¹).1.1 i j ∈ Ov E w := fun x =>
    ⟨fun h => mem_GLint_iff.1 (show x.1 ∈ GLint _ (intL _) from h.2), fun h => ⟨x.2, (mem_GLint_iff (O := intL _)).2 h⟩⟩
  rw [e, ← map_inv]
  refine Iff.trans (and_congr ((stab_latW hat).trans (stab_iff hw h ha (mat g))) ((stab_latW hat).trans
    (stab_iff hw h ha (mat g⁻¹)))).symm ?_
  simp only [IntAt, imp_and, forall_and]

theorem main : LocUnrInert := by
  rintro F E _ _ _ _ _ σ B n Y r s hB hY χ - hr K e hK he v ⟨w, hw⟩ hu μ hμ hμ1 z f hz hf
  have h := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw h
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hB.cm hw hc
  have hϖ : ϖ ≠ 0 := fun h0 => WithZero.zero_ne_coe (by simpa only [h0, map_zero] using hU.2.2.2.1)
  obtain ⟨a, ha, hH⟩ := frame hB.cm hY hw hc
  have sph : IsSphSec c (qV F v) n 1 z fun x => f (lift2 hw hc hH x) := fun p k hk => by
    obtain ⟨t, h1, h2, h3⟩ := lift_par hw hc hH p
    beta_reduce
    rw [map_mul, hf _ t h1 (up_at hw h _) _ (lift_mem hw hc hH ha hK hk) (up_at hw h _), abs_at hB.cm hw hc hU.2.1 h2 h3,
      GlobalTheory.InertChars.eq_ideleAt_of_at _ h2, ideleAt_eq_locIdele_of_isInertAt h hw, chi_at hw hr (hu w h), Circle.coe_one, one_mul]
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  let _ : MeasurableSpace (GU c n) := borel _
  have : BorelSpace (GU c n) := ⟨rfl⟩
  let φ := chartW hw hc hH
  let m := φ.toHomeomorph.toMeasurableEquiv
  have : (μ.map m).IsHaarMeasure := φ.isHaarMeasure_map μ
  obtain ⟨i1, i2⟩ := triv (ϖ := Units.mk0 ϖ hϖ) hU (μ.map m) (by
    rw [m.map_apply, ← hμ1]
    exact congrArg μ (Set.ext fun g => down_mem hw hc hH ha g.1)) hz sph
  have e2 : ∀ u : locGrp σ Y v, lift2 hw hc hH (io1 c n (m u)) = e (u.1, 1) := fun u => by
    refine Subtype.ext (Units.ext ((lift_emb hw hc hH _).trans (Eq.trans ?_ (he _ _).symm)))
    rw [show lift1 hw hc hH (m u) = u.1 from congrArg Subtype.val (φ.left_inv u)]
  rw [integrable_map_equiv, Function.comp_def] at i1
  rw [integral_map_equiv] at i2
  simp only [e2] at i1 i2
  refine ⟨i1, ?_⟩
  rw [locD, if_neg fun ⟨τ⟩ => not_isSplit_of_isInertAt hw (SplitChart.isSplit_of_algHom hB.cm τ)]
  refine i2.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [Lv, show Formalism.L2.Host.aboveF (L := E) F v = {w} by ext u; simp [mem_aboveF, under_eq_iff hw], Finset.prod_singleton, locL,
    charFam_of_unrAt (hu w h), eulerFac_singleton, val, locChar, MonoidHom.comp_apply, MonoidHom.comp_apply, chi_at hw hr (hu w h),
    map_one, Units.val_one, one_mul, npow, absNorm_eq hB.cm.2.2.1 hw]
  rfl

end GlobalTheory.ThK.Dbl.Inert

theorem GlobalTheory.ThK.Dbl.locUnrInert : GlobalTheory.ThK.Dbl.LocUnrInert := GlobalTheory.ThK.Dbl.Inert.main

end
end

-- bundled from Development.WeilBound.ThetaLifts.LatticeBasics.NearUnits
section
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.SplitFlip PositivityTheory.KCo PositivityTheory.ThK.SplitDict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace Bmp

theorem near_units {A : Type} [Monoid A] [TopologicalSpace A] {U : Set Aˣ} (hU : U ∈ 𝓝 (1 : Aˣ)) :
    ∀ᶠ p in 𝓝 ((1, 1) : A × A), ∀ g : Aˣ, g.1 = p.1 → (g⁻¹).1 = p.2 → g ∈ U := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap] at hU
  obtain ⟨V, hV, h⟩ := hU
  have c : Continuous fun p : A × A => (p.1, MulOpposite.op p.2) := continuous_fst.prodMk (MulOpposite.continuous_op.comp continuous_snd)
  filter_upwards [c.continuousAt.preimage_mem_nhds (x := (1, 1)) hV] with p hp g h1 h2
  exact h (show (g.1, MulOpposite.op (g⁻¹).1) ∈ V by rw [h1, h2]; exact hp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {n d : ℕ}

theorem near_UA (h : PositivityTheory.KCo.IsSec σ t sec) {X : Spc F E n} (hu : IsUnit ((incM F X.J).map (piW t))) {U : Set (UA σ X.J)} (hU : U ∈ 𝓝 1) :
    ∀ᶠ p in 𝓝 ((1, 1) : Matrix (Fin n) (Fin n) (Fv F v) × Matrix (Fin n) (Fin n) (Fv F v)), ∀ g ∈ UAt σ X (evFin F v),
      (mat g).map (piW t) = p.1 → (mat g⁻¹).map (piW t) = p.2 → g ∈ U := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  obtain ⟨U', h1, h2⟩ := (mem_nhds_subtype _ _ _).1 hU
  obtain ⟨A, hA⟩ := hu
  have cs : Continuous (sgl v : Fv F v → AF F) := (continuous_const.prodMk (continuous_singleFin v) : Continuous fun a => ((0 : Ainf F), singleFin v a))
  let S : Matrix (Fin n) (Fin n) (Fv F v) → Matrix (Fin n) (Fin n) (Fv F v) → Matrix (Fin n) (Fin n) (AE F E) := fun p q =>
    1 + of fun i j => sgl v ((p - 1) i j) • sec (1, 0) + sgl v (((A⁻¹).1 * qᵀ * A.1 - 1) i j) • sec (0, 1)
  have cS : Continuous fun p : _ × _ => S p.1 p.2 := continuous_const.add (continuous_matrix fun i j =>
    ((cs.comp ((continuous_fst.sub continuous_const).matrix_elem i j)).smul continuous_const).add
    ((cs.comp ((((continuous_const.matrix_mul continuous_snd.matrix_transpose).matrix_mul continuous_const).sub
      continuous_const).matrix_elem i j)).smul continuous_const))
  have S1 : S 1 1 = 1 := by ext i j; simp [S]
  have eS : ∀ g : UA σ X.J, At (evFin F v) (mat g - 1) → mat g = S ((mat g).map (piW t)) ((mat g⁻¹).map (piW t)) := fun g hg => by
    refine h.extM ?_ ?_ ?_
    · rw [← sub_sub]
      exact hg.kd_sub (kd_at_matrix.2 fun i j => (at_sgl_smul _ _).kd_add (at_sgl_smul _ _))
    · ext i j
      simp [S, (h.smul _ _).1, h.fst, ev_sgl, one_apply, apply_ite (piW t)]
    · have e1 := h.unit_rel g
      have e2 : ((mat g⁻¹).map (piW t))ᵀ * ((mat g).map (piW t))ᵀ = 1 := by
        rw [← transpose_mul, ← Matrix.map_mul, show mat g * mat g⁻¹ = 1 from g.1.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
          transpose_one]
      have e3 : (mat g).map (piW (t.comp σ)) = (A⁻¹).1 * ((mat g⁻¹).map (piW t))ᵀ * A.1 := by
        rw [← hA] at e1
        conv_rhs => rw [← e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ (_)ᵀ]
        erw [e2]
        rw [Matrix.mul_one, Units.inv_mul, Matrix.one_mul]
        rfl
      rw [e3]
      ext i j
      simp [S, (h.smul _ _).2, h.snd, ev_sgl, one_apply, apply_ite (piW (t.comp σ))]
  have c2 := cS.prodMk (cS.comp continuous_swap)
  filter_upwards [(c2.tendsto' (1, 1) (1, 1) (by simp [S1])).eventually (near_units h1)] with p hp g hg e1 e2
  have hg' : At (evFin F v) (mat g⁻¹ - 1) := by
    rw [show mat g⁻¹ - 1 = -mat g⁻¹ * (mat g - 1) by
      rw [mul_sub, neg_mul, show mat g⁻¹ * mat g = 1 from g.1.inv_mul]; simp [neg_add_eq_sub]]
    exact At.kd_mul_left hg _
  refine h2 (hp g.1 ((eS g hg).trans (by rw [e1, e2])) ((eS g⁻¹ hg').trans (by rw [inv_inv, e1, e2]; rfl)))

theorem exists_level {P : Matrix (Fin n) (Fin n) (Fv F v) × Matrix (Fin n) (Fin n) (Fv F v) → Prop} (hP : ∀ᶠ p in 𝓝 (1, 1), P p) :
    ∃ a : v.adicCompletionIntegers F, a ≠ 0 ∧ a ∈ IsLocalRing.maximalIdeal _ ∧
      ∀ p q, p - 1 ∈ lam (Fv F v) a n n → q - 1 ∈ lam (Fv F v) a n n → P (p, q) := by
  have := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have : CompactSpace (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F)) := inferInstanceAs (CompactSpace (_ → _ → _))
  obtain ⟨w, w1, w0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (IsDiscreteValuationRing.not_a_field (v.adicCompletionIntegers F))
  have cm : Continuous fun α : Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) => α.map (algebraMap _ (Fv F v)) :=
    continuous_id.matrix_map continuous_subtype_val
  have h1 : ∀ᶠ a : Fv F v in 𝓝 0, ∀ y ∈ (Set.univ : Set (Matrix (Fin n) (Fin n) (v.adicCompletionIntegers F) × Matrix _ _ _)),
      P (a • y.1.map (algebraMap _ _) + 1, a • y.2.map (algebraMap _ _) + 1) :=
    isCompact_univ.eventually_forall_of_forall_eventually fun y _ =>
      ((((continuous_fst.smul (cm.comp (continuous_fst.comp continuous_snd))).add continuous_const).prodMk
        ((continuous_fst.smul (cm.comp (continuous_snd.comp continuous_snd))).add continuous_const)).tendsto' (0, y) (1, 1)
        (by simp)).eventually hP
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((Valued.tendsto_zero_pow_of_v_lt_one (x := (w : Fv F v)) ((Valuation.mem_maximalIdeal_iff _ _).1 w1)).eventually h1)
  refine ⟨w ^ (N + 1), pow_ne_zero _ w0, Ideal.pow_mem_of_mem _ w1 _ N.succ_pos, fun p q ⟨α, hα⟩ ⟨β, hβ⟩ => ?_⟩
  exact (eq_add_of_sub_eq hα.symm) ▸ (eq_add_of_sub_eq hβ.symm) ▸ hN (N + 1) N.le_succ (α, β) trivial

theorem ind_mem {a : v.adicCompletionIntegers F} (ha : a ≠ 0) (Y₀ : Matrix (Fin n) (Fin d) (Fv F v)) :
    (fun Y => Set.indicator (lam (Fv F v) a n d : Set _) (fun _ => (1 : ℂ)) (Y - Y₀)) ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)) := by
  have := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have : CompactSpace (Matrix (Fin n) (Fin d) (v.adicCompletionIntegers F)) := inferInstanceAs (CompactSpace (_ → _ → _))
  have ha' : (a : Fv F v) ≠ 0 := fun h => ha (Subtype.ext h)
  have op : IsOpen ((lam (Fv F v) a n d).toAddSubgroup : Set (Matrix (Fin n) (Fin d) (Fv F v))) := by
    have o : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
    have e : ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin d) (Fv F v)), ∀ i j, (a : Fv F v)⁻¹ * Y i j ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => eventually_all.2 fun j => by
        have c : Continuous fun Y : Matrix (Fin n) (Fin d) (Fv F v) => (a : Fv F v)⁻¹ * Y i j :=
          continuous_const.mul (continuous_id.matrix_elem i j)
        exact (c.tendsto' 0 0 (by simp)).eventually (o.mem_nhds (zero_mem _))
    refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (e.mono fun Y hY => mem_lam.2 ⟨fun i j => ⟨_, hY i j⟩, ?_⟩)
    exact Matrix.ext fun i j => mul_inv_cancel_left₀ ha' _
  have hf := GlobalTheory.WeilM.HaarUniq.indicator_mem ⟨_, op⟩ (isCompact_range
    (f := fun α : Matrix (Fin n) (Fin d) (v.adicCompletionIntegers F) => (a : Fv F v) • α.map (algebraMap _ (Fv F v)))
    (continuous_matrix fun i j => continuous_const.mul (continuous_subtype_val.comp (continuous_id.matrix_elem i j))))
  exact ⟨hf.1.comp_continuous (Homeomorph.subRight Y₀).continuous, hf.2.comp_homeomorph (Homeomorph.subRight Y₀)⟩

end Bmp

open Bmp in
theorem bump : Bump := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp hnd v hv
  obtain ⟨t⟩ : Nonempty (E →ₐ[F] Fv F v) := ⟨B.τ ⟨v, hv⟩⟩
  obtain ⟨⟨ι, hι⟩, -, -, k⟩ := dictX F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.weil v t
  obtain ⟨⟨sec, h⟩, hsm⟩ := section_statement F E σ hp.base.cm v t
  have hG := grams h hp.herm hp.skew
  have n1 := near_UA h hG.uA ((Euler.isOpen_int (σ := σ) hp.herm.lat v).mem_nhds (one_mem _))
  have hv1 : ∀ᶠ y in 𝓝 (1 : Fv F v), ValuativeRel.valuation (Fv F v) y = 1 := by
    simpa [Filter.Eventually] using (ValuativeRel.valuation (Fv F v)).locally_const (x := 1) (by simp)
  have n2 := near_units (A := Matrix (Fin n) (Fin n) (Fv F v))
    (U := {g | chrW χW t (gdet g) = 1 ∧ ValuativeRel.valuation (Fv F v) (gdet g : Fv F v) = 1})
    (Eventually.and ((GeneralLinearGroup.continuous_det.tendsto' 1 1 (map_one _)).eventually
      ((hsm χW hp.hW).2.mem_nhds (one_mem _)))
      (((Units.continuous_val.comp GeneralLinearGroup.continuous_det).tendsto' 1 1 (by simp)).eventually hv1))
  obtain ⟨a, a0, a1, ha⟩ := exists_level (((continuous_fst.matrix_transpose.prodMk continuous_snd.matrix_transpose).tendsto'
    (1, 1) (1, 1) (by simp)).eventually (n1.and n2))
  let y : Matrix (Fin n) (Fin d) (v.adicCompletionIntegers F) := (1 : Matrix (Fin d) (Fin d) _).submatrix (Fin.castLE hnd) id
  have hy : y * yᵀ = 1 := by
    rw [transpose_submatrix, transpose_one, ← submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.one_mul,
      submatrix_one _ (Fin.castLE_injective hnd)]
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀, Y₀ = y.map (algebraMap _ (Fv F v)) := ⟨_, rfl⟩
  obtain ⟨φ, hφ, e⟩ := hι.bij.2.2 (ind_mem a0 Y₀)
  have mult : ∀ u, At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → ∀ c : ℂ, (∀ Y, Y - Y₀ ∈ lam (Fv F v) a n d →
      psiV B.ψ v (trace (Yᵀ * -u.map (piW t))) = c) → Acts (evFin F v) (M.co.rho B.ψ u) φ (c • φ) := fun u hu h0 c hc => by
    have ac := adjoint_statement.Heisenberg₂ F _ B.ψ v _ (hu.kd_map M.co.e.toLinearMap) φ
    have mem := schr_mem ((adjoint_statement.psi F _ hp.base.std).2 v).1 (locW v (M.co.e.toLinearMap u)) hφ
    rw [← hι.bij.2.1 mem ((SB _).smul_mem c hφ) (funext fun Y => ?_)]
    · exact ac
    obtain ⟨x, hx, hcx, -⟩ := exists_coord h hG (ofM Y, 0)
    have := hι.mult u hu h0 φ hφ _ mem ac x hx (coord_snd.1 (congrArg Prod.snd hcx))
    rw [co_eq h, symp_eq h hG hx, hcx, dotProduct_zero, sub_zero, toM_ofM] at this
    rw [this, map_smul, Pi.smul_apply, smul_eq_mul, e]
    by_cases hY : Y - Y₀ ∈ lam (Fv F v) a n d
    · rw [← hc Y hY, ← dot_ofM]; rfl
    · simp [Set.indicator_of_notMem hY]
  refine ⟨φ, hφ, fun h0 => ?_, fun g hg => ?_⟩
  · have := congrFun e Y₀
    simp [h0] at this
  let g₀ := GeneralLinearGroup.map (piW t) g.1
  rcases dich (O := v.adicCompletionIntegers F) (psiV B.ψ v) (fun x => ⟨fun H => ⟨⟨x, (hp.base.psiP v hv x).1 fun z hz => H ⟨z, hz⟩⟩, rfl⟩,
    fun ⟨o, ho⟩ z => (hp.base.psiP v hv x).2 (ho ▸ o.2) z z.2⟩) a0 a1 y _ hy (invT g₀)⁻¹ with ⟨h1, h2⟩ | ⟨l, h1, h2⟩
  · obtain ⟨b1, b2⟩ := ha _ _ h1 h2
    obtain ⟨b2, b3⟩ := b2 g₀ rfl rfl
    obtain ⟨φ₁, m1, ac, e1⟩ := (k ι hι).1 g hg g₀ rfl φ hφ
    have key : ∀ Y, g₀.1ᵀ * Y - Y₀ ∈ lam (Fv F v) a n d ↔ Y - Y₀ ∈ lam (Fv F v) a n d := fun Y => by
      refine ⟨fun H => ?_, fun H => hY₀ ▸ keep h1 y (hY₀ ▸ H)⟩
      have := keep h2 y (hY₀ ▸ H)
      rwa [show g₀.1ᵀ = ((invT g₀)⁻¹).1 from rfl, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, ← hY₀] at this
    have e2 : ι φ₁ = ι φ := e1.trans (funext fun Y => by
      clear b1 ha k n1 n2 mult
      rw [omB, b2, apow_of_valuation_eq_one b3, show gdet (1 : GL (Fin d) (Fv F v)) = 1 from map_one _, map_one, apow_one,
        Units.val_one, Units.val_one, Matrix.mul_one, one_mul, one_mul, one_mul, one_mul, e]
      by_cases hY : Y - Y₀ ∈ lam (Fv F v) a n d
      · exact (Set.indicator_of_mem ((key Y).2 hY) _).trans (Set.indicator_of_mem hY fun _ => (1 : ℂ)).symm
      · exact (Set.indicator_of_notMem (mt (key Y).1 hY) _).trans (Set.indicator_of_notMem hY fun _ => (1 : ℂ)).symm)
    rw [hι.bij.2.1 m1 hφ e2] at ac
    exact Or.inl ⟨b1 g hg rfl rfl, ac⟩
  · rw [← hY₀] at h2
    let u₀ : Matrix (Fin n) (Fin d) (Fv F v) := of fun i j => -l (single i j 1)
    have el : ∀ Y, trace (Yᵀ * -u₀) = l Y := fun Y => by
      conv_rhs => rw [matrix_eq_sum_single Y]
      simp only [← dot_ofM, dotProduct, ofM, Fintype.sum_prod_type, map_sum, u₀, Matrix.neg_apply, of_apply, neg_neg]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [← smul_eq_mul, ← map_smul]; simp
    refine Or.inr ⟨secM sec u₀ 0, psiV B.ψ v (l Y₀), psiV B.ψ v (l (g₀.1ᵀ * Y₀)), h.atM _ _, fun H => h2 ?_,
      mult _ (h.atM _ _) (h.sndM _ _) _ fun Y hY => ?_,
      mult _ ((h.atM _ _).kd_mul_left _) (by rw [Matrix.map_mul, h.sndM, Matrix.mul_zero]) _ fun Y hY => ?_⟩
    · refine mul_right_cancel₀ ((psiV B.ψ v).val_isUnit (l Y₀)).ne_zero ?_
      rw [← AddChar.map_add_eq_mul, ← map_add, sub_add_cancel, one_mul, H]
      rfl
    · rw [h.fstM, el, ← sub_add_cancel Y Y₀, map_add, AddChar.map_add_eq_mul, (h1 _ hY).1, one_mul]
    · rw [Matrix.map_mul, h.fstM, ← Matrix.mul_neg, ← Matrix.mul_assoc, ← transpose_transpose (Yᵀ * _), transpose_mul,
        transpose_transpose, el, ← sub_add_cancel Y Y₀, Matrix.mul_add, map_add, AddChar.map_add_eq_mul]
      exact (congrArg (· * _) (h1 _ hY).2).trans (one_mul _)

end GlobalTheory.ThK.Dbl

end
end

