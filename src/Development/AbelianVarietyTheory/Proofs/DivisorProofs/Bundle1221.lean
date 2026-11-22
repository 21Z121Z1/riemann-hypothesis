import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmpleSectionClearingRationalFunctionDenomi
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HSNef.DenOne

open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.LBGerm

variable {X : Scheme.{0}} [IsIntegral X]

theorem isRatSec_lbPow {L : LB X} {r : L.ι → X.functionFieldˣ} (hr : IsRatSec L r) (τ : ℕ) :
    IsRatSec (lbPow L τ) fun c => r (c PUnit.unit) ^ τ := fun c c' h => by
  have l : (lbPow L τ).U c ⊓ (lbPow L τ).U c' ≤ L.U (c PUnit.unit) ⊓ L.U (c' PUnit.unit) :=
    fun _ hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have e : (lbPow L τ).g c c' = res l (L.g (c PUnit.unit) (c' PUnit.unit)) ^ τ := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [e, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow,
    ← mul_pow, hr _ _ (l h)]
  exact congrArg (fun a => (a * _) ^ τ) (fnOf_resG l h _).symm

theorem res_mem_secOn (L : LB X) (V : X.Opens) (a : Γ(X, V)) :
    (fun J : PUnit → L.ι => resG X (inf_le_left : V ⊓ powChart L J ≤ V) a) ∈ secOn (lbPow L 0) V :=
  mem_secOn_of_germ _ fun y i j hV hi hj => by
    rw [gm_lbPow_g 0 (𝟙 X) y i j hi hj, pow_zero, Units.val_one, one_mul]
    exact (gs_res (𝟙 X) y _ (⟨hV, hi⟩ : y ∈ V ⊓ (lbPow L 0).U i) a).trans
      (gs_res (𝟙 X) y _ (⟨hV, hj⟩ : y ∈ V ⊓ (lbPow L 0).U j) a).symm

theorem unitAt_ne_zero {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : UnitAt x f) : f ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  exact (hc.map (algebraMap _ X.functionField)).ne_zero

theorem exists_den_one : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (f : X.functionField),
    ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H 0 c ∧ g * f ∈ P.H 0 c := by
  intro k _ X _ p D _ P hA f
  haveI := hA.compactSpace
  haveI := hA.quasiSeparatedSpace
  have hL := hA.isLB
  obtain ⟨n, hn, s, hgs, haff⟩ := hA.exists_affine (genericPoint X)
  haveI : Nonempty (nonzeroLocus s) := ⟨⟨_, hgs⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X (nonzeroLocus s) haff
  obtain ⟨a, b, hb, hf⟩ := IsFractionRing.div_surjective (A := Γ(X, nonzeroLocus s)) f
  change fnOf _ hgs a / fnOf _ hgs b = f at hf
  have hβ : fnOf _ hgs b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  obtain ⟨Na, ha⟩ := exists_sec_eq_pow_mul hL s _ (res_mem_secOn P.A.B (nonzeroLocus s) a)
  obtain ⟨Nb, hb'⟩ := exists_sec_eq_pow_mul hL s _ (res_mem_secOn P.A.B (nonzeroLocus s) b)
  obtain ⟨u, hu⟩ := ha (max Na Nb + 1) (by omega)
  obtain ⟨v, hv⟩ := hb' (max Na Nb + 1) (by omega)
  have hρ := isRatSec_lbPow P.hr' (0 + n * (max Na Nb + 1))
  obtain ⟨e, he⟩ := RepDict.exists_quot (isLB_lbPow hL (0 + n * (max Na Nb + 1))) hρ
  have hmem : ∀ w : (lbPow P.A.B (0 + n * (max Na Nb + 1))).Sec,
      e w ∈ P.H 0 ((0 + n * (max Na Nb + 1) : ℕ) : ℤ) := by
    intro w x i j _ hj
    have hJ : x ∈ (lbPow P.A.B (0 + n * (max Na Nb + 1))).U (fun _ => j) := mem_powChart.2 hj
    have h1 := he w (fun _ => j) (gen_mem hJ)
    simp only [Pair.loc, zpow_zero, mul_one, zpow_natCast]
    rw [← Units.val_pow_eq_pow_val, h1]
    exact regAt_fnOf hJ _ _
  obtain ⟨j₀, hj₀⟩ := exists_chart hL (genericPoint X)
  have hJ₀ : genericPoint X ∈ powChart P.A.B (fun _ => j₀) := mem_powChart.2 hj₀
  have hVJ : genericPoint X ∈ nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) := ⟨hgs, hJ₀⟩
  have key : ∀ (w : (lbPow P.A.B (0 + n * (max Na Nb + 1))).Sec) (a' : Γ(X, nonzeroLocus s)),
      resG X (inf_le_right : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ powChart P.A.B (fun _ => j₀))
          (powFn w (fun _ => j₀)) =
        resG X (inf_le_right : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ powChart P.A.B (fun _ => j₀))
          (powFn s (fun _ => j₀)) ^ (max Na Nb + 1) *
        resG X (inf_le_left : nonzeroLocus s ⊓ powChart P.A.B (fun _ => j₀) ≤ nonzeroLocus s) a' →
      e w * (P.r' j₀ : X.functionField) ^ (0 + n * (max Na Nb + 1)) =
        fnOf _ hJ₀ (powFn s (fun _ => j₀)) ^ (max Na Nb + 1) * fnOf _ hgs a' := by
    intro w a' h
    have h' := congrArg (fnOf _ hVJ) h
    rw [map_mul, map_pow, fnOf_resG, fnOf_resG, fnOf_resG] at h'
    rw [← Units.val_pow_eq_pow_val]
    exact (he w _ hJ₀).trans h'
  have eu := key u a (hu _)
  have ev := key v b (hv _)
  have hS : fnOf _ hJ₀ (powFn s (fun _ => j₀)) ≠ 0 := by
    exact unitAt_ne_zero ((unitAt_fnOf_iff hJ₀ hJ₀ _).2 ((mem_nonzeroLocus_iff_basicOpen s hJ₀).1 hgs))
  have hR : (P.r' j₀ : X.functionField) ^ (0 + n * (max Na Nb + 1)) ≠ 0 := pow_ne_zero _ (P.r' j₀).ne_zero
  refine ⟨0 + n * (max Na Nb + 1), e v, by positivity, fun h0 => ?_, hmem v, ?_⟩
  · rw [h0, zero_mul] at ev
    exact mul_ne_zero (pow_ne_zero _ hS) hβ ev.symm
  · have e1 : e u = _ := eq_div_of_mul_eq hR eu
    have e2 : e v = _ := eq_div_of_mul_eq hR ev
    have : e v * f = e u := by
      rw [e1, e2, ← hf]
      field_simp
    rw [this]
    exact hmem u

end GlobalTheory.HSNef.DenOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeRigidifiedBundleTrivialLocu
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocusLocal

open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison in

theorem exists_gen_pull_pull_iff {X Y Z : Scheme.{0}} (N : LB X) (a : Y ⟶ X) (b : Z ⟶ Y) :
    (∃ s : ((N.pull a).pull b).Gen, s.IsGen) ↔ ∃ s : (N.pull (b ≫ a)).Gen, s.IsGen := by
  have hb : ∀ z : Z, (b ≫ a).base z = a.base (b.base z) := fun z => rfl
  have m1 : ∀ (j : PUnit.{1} → N.ι) (z : Z), z ∈ (N.pull (b ≫ a)).U j →
      z ∈ ((N.pull a).pull b).U (fun _ _ => j PUnit.unit) := by
    intro j z hz
    have h1 : (b ≫ a).base z ∈ N.U (j PUnit.unit) := (mem_wchart_pu N (b ≫ a) j z).1 hz
    have h2 : b.base z ∈ (N.pull a).U (fun _ => j PUnit.unit) :=
      (mem_wchart_pu N a (fun _ => j PUnit.unit) (b.base z)).2 (by rw [← hb]; exact h1)
    exact (mem_wchart_pu (N.pull a) b (fun _ _ => j PUnit.unit) z).2 h2
  have m2 : ∀ (j : PUnit.{1} → PUnit.{1} → N.ι) (z : Z), z ∈ ((N.pull a).pull b).U j →
      z ∈ (N.pull (b ≫ a)).U (fun _ => j PUnit.unit PUnit.unit) := by
    intro j z hz
    have h2 : b.base z ∈ (N.pull a).U (j PUnit.unit) := (mem_wchart_pu (N.pull a) b j z).1 hz
    have h1 : a.base (b.base z) ∈ N.U (j PUnit.unit PUnit.unit) :=
      (mem_wchart_pu N a (j PUnit.unit) (b.base z)).1 h2
    exact (mem_wchart_pu N (b ≫ a) (fun _ => j PUnit.unit PUnit.unit) z).2 (by rw [hb]; exact h1)
  constructor
  · intro h
    refine exists_gen_transfer (L := (N.pull a).pull b) (L' := N.pull (b ≫ a))
      (fun j _ _ => j PUnit.unit) m1 ?_ h
    intro i j y hy
    have hy' := pull_inf_le N (b ≫ a) i j hy
    exact (germ_pull N (b ≫ a) i j y hy hy').trans
      (germ_pull_pull N a b (fun _ _ => i PUnit.unit) (fun _ _ => j PUnit.unit) y ⟨m1 i y hy.1, m1 j y hy.2⟩ hy').symm
  · intro h
    refine exists_gen_transfer (L := N.pull (b ≫ a)) (L' := (N.pull a).pull b)
      (fun j _ => j PUnit.unit PUnit.unit) m2 ?_ h
    intro i j y hy
    have hy2 : y ∈ (N.pull (b ≫ a)).U (fun _ => i PUnit.unit PUnit.unit) ⊓
        (N.pull (b ≫ a)).U (fun _ => j PUnit.unit PUnit.unit) := ⟨m2 i y hy.1, m2 j y hy.2⟩
    have hy' := pull_inf_le N (b ≫ a) _ _ hy2
    exact (germ_pull_pull N a b i j y hy hy').trans (germ_pull N (b ≫ a) _ _ y hy2 hy').symm

end GlobalTheory.TrivLocusLocal

namespace GlobalTheory.TrivLocusLocal

theorem exists_closed_triv_local : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∀ x : S, ∃ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), x ∈ U ∧ IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ U), TrivCond A N T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  intro S _ A _ L₀ N hA hL₀ ha hN hr x
  obtain ⟨R, j, _, hx, -⟩ := Scheme.exists_affine_mem_range_and_range_subset (x := x) (U := ⊤) trivial
  let j' : Sp R ⟶ S := j
  haveI : IsOpenImmersion j' := inferInstanceAs (IsOpenImmersion j)
  letI : GrpObj ((Over.pullback j').obj A) := Functor.grpObjObj
  let φ₀ := pullback.fst A.hom j'
  have hp := isGrpPullback_pullback A j'
  have hB : IsAbelianScheme ((Over.pullback j').obj A) := Out.TLinPf.isAb_pullback j' A hA
  have hL₀' := pull_isLB hL₀ φ₀
  have haB : Out.RelAmple ((Over.pullback j').obj A) (L₀.pull φ₀) := by
    have := GlobalTheory.KTrivSpread.relAmple_chart j' (𝟙 _) hL₀ ha
    rwa [Category.id_comp] at this
  have hN' := pull_isLB hN φ₀
  have hrB : Out.Rigidified ((Over.pullback j').obj A) (N.pull φ₀) := by
    obtain ⟨s, hs⟩ := hr
    have h1 := exists_gen_pull_comp N (eSec A) j' ⟨s, hs⟩
    rw [← GlobalTheory.RigidBundleGlue.eSec_comm hp] at h1
    exact (exists_gen_pull_pull_iff N φ₀ (eSec ((Over.pullback j').obj A))).2 h1
  obtain ⟨Z, i₀, hi₀, H⟩ := GlobalTheory.T.exists_closed_subscheme_trivial_locus_rigidified R ((Over.pullback j').obj A) (L₀.pull φ₀) (N.pull φ₀) hB hL₀' haB hN' hrB
  refine ⟨j'.opensRange, Z, i₀ ≫ j'.isoOpensRange.hom, hx, inferInstance, fun T t => ?_⟩
  let t' : T ⟶ Sp R := t ≫ j'.isoOpensRange.inv
  have ht : t' ≫ j' = t ≫ j'.opensRange.ι := by
    simp only [t', Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  letI : GrpObj ((Over.pullback t').obj ((Over.pullback j').obj A)) := Functor.grpObjObj
  have hq := isGrpPullback_pullback ((Over.pullback j').obj A) t'
  have H1 := H T t' _ _ hq
  have hP : IsPullback (pullback.fst ((Over.pullback j').obj A).hom t' ≫ φ₀)
      (pullback.snd ((Over.pullback j').obj A).hom t') A.hom (t ≫ j'.opensRange.ι) := by
    rw [← ht]
    exact (IsPullback.of_hasPullback ((Over.pullback j').obj A).hom t').paste_horiz
      (IsPullback.of_hasPullback A.hom j')
  rw [← trivCond_iff A N T (t ≫ j'.opensRange.ι) _ _ _ hP, ← exists_gen_pull_pull_iff]
  refine H1.trans ⟨fun ⟨z, hz⟩ => ⟨z, ?_⟩, fun ⟨z, hz⟩ => ⟨z, ?_⟩⟩
  · rw [← Category.assoc, hz]
    simp only [t', Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · simp only [t', ← hz, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end GlobalTheory.TrivLocusLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetTwistedCentralizerElliptic
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.CentCpt

section Closed
variable {L : Type} [NormedField L] [IsAlgClosed L] {n : ℕ}

theorem exists_eigenbasis (y : Matrix (Fin n) (Fin n) L) (hs : y.charpoly.Separable) :
    ∃ (ι : Type) (_ : Fintype ι) (v : ι → Fin n → L) (l : ι → L), LinearIndependent L v ∧
      Fintype.card ι = n ∧ ∀ i, Module.End.HasEigenvector (Matrix.toLin' y) (l i) (v i) := by
  classical
  have hnd : y.charpoly.roots.Nodup := nodup_roots hs
  have hcard : y.charpoly.roots.toFinset.card = n := by
    rw [Multiset.toFinset_card_of_nodup hnd, splits_iff_card_roots.1 (IsAlgClosed.splits _),
      charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hev : ∀ r : y.charpoly.roots.toFinset, ∃ v : Fin n → L,
      Module.End.HasEigenvector (Matrix.toLin' y) r.1 v := fun r =>
    ((Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2 (by
      rw [Matrix.charpoly_toLin']
      exact isRoot_of_mem_roots (Multiset.mem_toFinset.1 r.2))).exists_hasEigenvector
  choose v hv using hev
  exact ⟨_, inferInstance, v, fun r => r.1,
    Module.End.eigenvectors_linearIndependent' _ _ Subtype.val_injective v hv,
    by rw [Fintype.card_coe, hcard], hv⟩

theorem aeval_mulVec_eigen (y : Matrix (Fin n) (Fin n) L) {μ : L} {x : Fin n → L}
    (h : Module.End.HasEigenvector (Matrix.toLin' y) μ x) (q : L[X]) :
    aeval y q *ᵥ x = q.eval μ • x := by
  rw [← Module.End.aeval_apply_of_hasEigenvector h]
  have h1 := aeval_algHom_apply (toLinAlgEquiv' (R := L) (n := Fin n)).toAlgHom y q
  exact (LinearMap.congr_fun h1 x).symm

theorem exists_bound (y : Matrix (Fin n) (Fin n) L) (hs : y.charpoly.Separable) :
    ∃ M : ℝ, ∀ t : Matrix (Fin n) (Fin n) L, t * y = y * t →
      (∃ B : ℝ, ∀ k : ℕ, ∀ i j, ‖(t ^ k) i j‖ ≤ B) → ∀ i j, ‖t i j‖ ≤ M := by
  classical
  obtain ⟨ι, _, v, l, hli, hcard, hv⟩ := exists_eigenbasis y hs
  let b : Module.Basis ι L (Fin n → L) :=
    basisOfLinearIndependentOfCardEqFinrank' v hli (by rw [hcard, Module.finrank_fin_fun])
  have hb : ⇑b = v := coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _
  let c : Fin n → ι → L := fun j i => b.repr (Pi.single j 1) i
  refine ⟨∑ a, ∑ j, ∑ i, ‖c j i‖ * ‖v i a‖, fun t ht ⟨B, hB⟩ a j => ?_⟩
  obtain ⟨p, hp⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm y t hs ht.symm
  have hpow : ∀ k : ℕ, ∀ i, (t ^ k) *ᵥ v i = (p.eval (l i)) ^ k • v i := by
    intro k i
    rw [hp, ← map_pow, aeval_mulVec_eigen y (hv i), eval_pow]
  have hd : ∀ i, ‖p.eval (l i)‖ ≤ 1 := by
    intro i
    obtain ⟨a0, ha0⟩ : ∃ a0, v i a0 ≠ 0 := by
      by_contra h
      push_neg at h
      exact (hv i).2 (funext h)
    have hk : ∀ k : ℕ, ‖p.eval (l i)‖ ^ k ≤ (B * ∑ j, ‖v i j‖) / ‖v i a0‖ := by
      intro k
      rw [le_div_iff₀ (norm_pos_iff.2 ha0), ← norm_pow, ← norm_mul]
      have e := congrFun (hpow k i) a0
      rw [Pi.smul_apply, smul_eq_mul] at e
      rw [← e, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hB k a0 j) (norm_nonneg _)
    by_contra h1
    push_neg at h1
    obtain ⟨k, hk'⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually_gt_atTop
      ((B * ∑ j, ‖v i j‖) / ‖v i a0‖)).exists
    exact absurd (hk k) (not_le.2 hk')
  have hcol : t a j = (t *ᵥ Pi.single j 1) a := by
    rw [Matrix.mulVec_single_one]; rfl
  have hexp : (Pi.single j 1 : Fin n → L) = ∑ i, c j i • v i := by
    rw [← hb]; exact (b.sum_repr _).symm
  have hval : t a j = ∑ i, c j i * (p.eval (l i) * v i a) := by
    rw [hcol, hexp, Matrix.mulVec_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hpow 1 i
    rw [pow_one, pow_one] at this
    rw [Matrix.mulVec_smul, this, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  rw [hval]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∑ i, ‖c j i * (p.eval (l i) * v i a)‖ ≤ ∑ i, ‖c j i‖ * ‖v i a‖ := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (by
      simpa using mul_le_mul_of_nonneg_right (hd i) (norm_nonneg (v i a))) (norm_nonneg _)
  refine h1.trans ?_
  have hnn : ∀ a' j', 0 ≤ ∑ i, ‖c j' i‖ * ‖v i a'‖ := fun _ _ =>
    Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc ∑ i, ‖c j i‖ * ‖v i a‖ ≤ ∑ j', ∑ i, ‖c j' i‖ * ‖v i a‖ :=
        Finset.single_le_sum (f := fun j' => ∑ i, ‖c j' i‖ * ‖v i a‖) (fun j' _ => hnn a j') (Finset.mem_univ j)
    _ ≤ ∑ a', ∑ j', ∑ i, ‖c j' i‖ * ‖v i a'‖ :=
        Finset.single_le_sum (f := fun a' => ∑ j', ∑ i, ‖c j' i‖ * ‖v i a'‖)
          (fun a' _ => Finset.sum_nonneg fun j' _ => hnn a' j') (Finset.mem_univ a)

end Closed
end GlobalTheory.CentCpt

namespace GlobalTheory.CentCpt

section Local
variable {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] {n : ℕ}

theorem exists_bound_local (y : Matrix (Fin n) (Fin n) F) (hs : y.charpoly.Separable) :
    ∃ M : ℝ, ∀ t : Matrix (Fin n) (Fin n) F, t * y = y * t →
      (∃ B : ℝ, ∀ k : ℕ, ∀ i j, ‖(t ^ k) i j‖ ≤ B) → ∀ i j, ‖t i j‖ ≤ M := by
  letI : NormedField (AlgebraicClosure F) := spectralNorm.normedField F (AlgebraicClosure F)
  let f : F →+* AlgebraicClosure F := algebraMap F _
  have hf : ∀ x : F, ‖f x‖ = ‖x‖ := fun x => spectralNorm_extends (L := AlgebraicClosure F) x
  obtain ⟨M, hM⟩ := exists_bound (y.map f) (by rw [Matrix.charpoly_map]; exact hs.map)
  refine ⟨M, fun t ht ⟨B, hB⟩ i j => ?_⟩
  have := hM (t.map f) (by rw [← Matrix.map_mul, ht, Matrix.map_mul]) ⟨B, fun k a b => by
      rw [← Matrix.map_pow, Matrix.map_apply, hf]; exact hB k a b⟩ i j
  rwa [Matrix.map_apply, hf] at this

theorem isCompact_bdd [ProperSpace F] (M : ℝ) :
    IsCompact {g : GL (Fin n) F | (∀ i j, ‖(g : Matrix (Fin n) (Fin n) F) i j‖ ≤ M) ∧
      ∀ i j, ‖((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j‖ ≤ M} := by
  first
  | exact @_root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units
  | exact _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units
  | (apply _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units <;> assumption)
  | (intros; apply _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BoundedUnitsCompact.isCompact_bounded_units ..)

end Local

theorem norm_le_sum {F : Type} [NormedField F] {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    ‖A i j‖ ≤ ∑ a, ∑ b, ‖A a b‖ :=
  (Finset.single_le_sum (f := fun b => ‖A i b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun a => ∑ b, ‖A a b‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.mem_univ i))

end GlobalTheory.CentCpt

namespace GlobalTheory.CentCpt

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w),
    y.1.val.charpoly.Separable → ∃ Ω : Set (UL n w), IsCompact Ω ∧ ∀ t ∈ twCent (MonoidHom.id (UL n w)) y,
      IsCompact (closure (Subgroup.zpowers t : Set (UL n w))) → t ∈ Ω := by
  intro E _ _ _ _ n w y hs
  letI : NontriviallyNormedField (w.adicCompletion E) := Valued.toNontriviallyNormedField _ _
  haveI : IsUltrametricDist (w.adicCompletion E) :=
    inferInstanceAs (@IsUltrametricDist (w.adicCompletion E)
      (Valued.toNormedField (w.adicCompletion E) (WithZero (Multiplicative ℤ))).toDist)
  haveI : CompleteSpace (w.adicCompletion E) := inferInstance
  haveI : ProperSpace (w.adicCompletion E) :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (w.adicCompletion E)
  obtain ⟨M, hM⟩ := exists_bound_local (y.1.val) hs
  refine ⟨Subtype.val ⁻¹' {g : GLw n w | (∀ i j, ‖(g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j‖ ≤ M) ∧
      ∀ i j, ‖((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j‖ ≤ M},
    (GlobalTheory.LocFinU.isClosed_UL n w).isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_bdd (n := n) M), ?_⟩
  have hbd : ∀ s ∈ twCent (MonoidHom.id (UL n w)) y, IsCompact (closure (Subgroup.zpowers s : Set (UL n w))) →
      ∀ i j, ‖(s.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j‖ ≤ M := by
    intro s hs' hcs
    have hcont : Continuous fun g : UL n w =>
        ∑ a, ∑ b, ‖(g.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) a b‖ :=
      continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
        ((Units.continuous_val.comp continuous_subtype_val).matrix_elem a b).norm
    obtain ⟨B, hB⟩ := (hcs.image hcont).bddAbove
    refine hM _ ?_ ⟨B, fun k a b => ?_⟩
    · have h1 : s * y = y * s := hs'
      have h2 := congrArg (fun g : UL n w => (g.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) h1
      simpa using h2
    · have hk : s ^ k ∈ closure (Subgroup.zpowers s : Set (UL n w)) :=
        subset_closure (Subgroup.npow_mem_zpowers s k)
      have e : ((s ^ k).1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
          (s.1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ^ k := by
        simp [Subgroup.coe_pow, Units.val_pow_eq_pow_val]
      rw [← e]
      exact (norm_le_sum _ a b).trans (hB ⟨_, hk, rfl⟩)
  intro t ht hc
  refine ⟨hbd t ht hc, ?_⟩
  have := hbd t⁻¹ (inv_mem ht) (by rwa [Subgroup.zpowers_inv])
  simpa using this

end GlobalTheory.CentCpt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactShellNsmul
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

namespace GlobalTheory.NonarchShell

theorem exists_compact_shell_nsmul : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (V : Set (Fin N → v.adicCompletion F)), V ∈ nhds 0 →
      ∃ K : Set (Fin N → v.adicCompletion F), IsCompact K ∧ (0 : Fin N → v.adicCompletion F) ∉ K ∧
        ∀ t, t ∉ V → ∃ n : ℕ, n • t ∈ K := by
  intro F _ _ v N V hV
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  set q : ℕ := Ideal.absNorm v.asIdeal with hqdef
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hq1 : ‖(q : v.adicCompletion F)‖ < 1 := by
    have := (NumberField.FinitePlace.norm_lt_one_iff_mem F v ((q : 𝓞 F))).2 (Ideal.absNorm_mem _)
    rwa [map_natCast, map_natCast] at this
  have hqne : (q : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F)) q]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hq0)
  have hqpos : 0 < ‖(q : v.adicCompletion F)‖ := norm_pos_iff.2 hqne
  have hsm : ∀ (m : ℕ) (t : Fin N → v.adicCompletion F), ‖m • t‖ = ‖(m : v.adicCompletion F)‖ * ‖t‖ := by
    intro m t
    rw [← Nat.cast_smul_eq_nsmul (v.adicCompletion F), norm_smul]
  refine ⟨{t | r * ‖(q : v.adicCompletion F)‖ ≤ ‖t‖ ∧ ‖t‖ ≤ r}, ?_, ?_, ?_⟩
  · refine (isCompact_closedBall (0 : Fin N → v.adicCompletion F) r).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · intro t ht
      simpa [mem_closedBall_zero_iff] using ht.2
  · intro h
    have h1 := h.1
    rw [norm_zero] at h1
    exact absurd h1 (not_le.2 (mul_pos hr hqpos))
  · intro t ht
    have htr : r ≤ ‖t‖ := by
      by_contra hlt
      exact ht (hrV (mem_ball_zero_iff.2 (not_le.1 hlt)))
    have htpos : 0 < ‖t‖ := lt_of_lt_of_le hr htr
    have hex : ∃ k : ℕ, ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hr htpos) hq1
      exact ⟨k, (lt_div_iff₀ htpos).1 hk⟩
    classical
    set k := Nat.find hex with hkdef
    have hk : ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_mul] at hk
      exact absurd htr (not_le.2 hk)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hjmin : ¬ ‖(q : v.adicCompletion F)‖ ^ j * ‖t‖ < r :=
      Nat.find_min hex (by omega)
    have hnorm : ‖(q ^ k) • t‖ = ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ := by
      rw [hsm, Nat.cast_pow, norm_pow]
    refine ⟨q ^ k, ?_, ?_⟩
    · show r * ‖(q : v.adicCompletion F)‖ ≤ ‖(q ^ k) • t‖
      rw [hnorm, hj, pow_succ]
      have := not_lt.1 hjmin
      nlinarith
    · show ‖(q ^ k) • t‖ ≤ r
      rw [hnorm]; exact hk.le

end GlobalTheory.NonarchShell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePointsRegularDivAffineOpenStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_points_regular_div_affineOpen : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (V : X.Opens), IsAffineOpen V → ∀ (hV : genericPoint X ∈ V) (a : Γ(X, V)), fnOf V hV a ≠ 0 → ∃ T : Set X, T.Finite ∧ ∀ x ∈ V, ∀ τ g : X.functionField, RegAt x τ → (∀ z ∈ T, z ⤳ x → UnitAt z τ) → RegAt x g → RegAt x (g * τ / fnOf V hV a) → RegAt x (g / fnOf V hV a) := by
  first | exact @GlobalTheory.exists_finite_points_regAt_div_of_affine | exact GlobalTheory.exists_finite_points_regAt_div_of_affine | (intros; apply GlobalTheory.exists_finite_points_regAt_div_of_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeLocalizationSameFractionFieldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteType_localization_same_fractionField : ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L), IsLocModel c R →
    ∃ (S : Subring L) (hS : ∀ a, c a ∈ S) (q : Ideal S), q.IsPrime ∧ (c.codRestrict S hS).FiniteType ∧
      (∀ f : L, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ f * b = a) ∧
      ∀ f : L, f ∈ R ↔ ∃ a b : S, b ∉ q ∧ f * b = a := by
  first | exact @GlobalTheory.FieldPair.IsLocModel.exists_finiteType_localization | exact GlobalTheory.FieldPair.IsLocModel.exists_finiteType_localization | (intros; apply GlobalTheory.FieldPair.IsLocModel.exists_finiteType_localization <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyOfTotallyOrderedRatFnFamilyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (J : Type) [Fintype J] [Nonempty J] (f : J → X.functionField) (w : J → ℝ), Total f → ∃ M : HermLB p, IsFS M f w := by
  first | exact @GlobalTheory.HSNef.exists_isFS | exact GlobalTheory.HSNef.exists_isFS | (intros; apply GlobalTheory.HSNef.exists_isFS <;> assumption)
end

