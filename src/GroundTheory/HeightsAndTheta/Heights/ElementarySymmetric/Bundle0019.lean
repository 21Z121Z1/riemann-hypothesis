import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0033
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSection
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GramMatrices.PGramAtPosDef
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0055
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0032
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0041
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0039
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0048

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMixedTwistShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace MixedTwistShiftAlt

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem foldl_twist_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (I : Chart x) :
    ∀ (l : List (Fin n)) (F : SubSystem k x Ω),
      (l.foldl (fun F i => F.twist (L i)) F).sub I = F.sub I * (l.map fun i => (L i).sub I).prod
  | [], F => by simp
  | i :: l, F => by
    rw [List.foldl_cons, foldl_twist_sub L I l, SubSystem.twist_sub_eq_mul_of_line, List.map_cons,
      List.prod_cons]
    ring

theorem prod_map_filter {R : Type*} [CommMonoid R] {n : ℕ} (g : Fin n → R) (T : Finset (Fin n)) :
    ∀ l : List (Fin n),
      ((l.filter (· ∈ T)).map g).prod = (l.map fun j => g j ^ (if j ∈ T then 1 else 0)).prod
  | [] => rfl
  | j :: l => by
    by_cases hj : j ∈ T <;> simp [hj, prod_map_filter g T l]

theorem tensorSub_sub {n : ℕ} (L : Fin n → SubSystem k x Ω) (T : Finset (Fin n)) (I : Chart x) :
    (tensorSub L T).sub I = ∏ j, (L j).sub I ^ (if j ∈ T then 1 else 0) := by
  have h0 : (twistSys k x 0).sub I = 1 := (SubSystem.pow_sub (twistSys k x 0) 0 I).trans (pow_zero _)
  rw [tensorSub, foldl_twist_sub, h0, one_mul, prod_map_filter, Fin.prod_univ_def]

theorem twistPows_snoc_sub {n : ℕ} (L : Fin n → LineBundle k x) (M : LineBundle k x) (T : Finset (Fin n))
    (m : ℕ) (I : Chart x) :
    ((twistSys k x 0).twistPows (n + 1)
        (fun j => (Fin.snoc (α := fun _ => LineBundle k x) L M j).toSubSystem)
        (Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m)).sub I =
      M.sub I ^ m * (tensorSub (fun i => (L i).toSubSystem) T).sub I := by
  have h0 : (twistSys k x 0).sub I = 1 := (SubSystem.pow_sub (twistSys k x 0) 0 I).trans (pow_zero _)
  rw [SnapperSections.twistPows_sub, tensorSub_sub, h0, one_mul, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

end MixedTwistShiftAlt

open MixedTwistShiftAlt in

theorem MixedTwistShift.proof (hH : SnapperHyperplane.Statement.{u, w}) (hS : SnapperSection.Statement.{u, w})
    (hP : SnapperDiffPoly.Statement) (hR : RestrLenEuler.Statement.{u, w}) (hD : SubsetDiffConst.Statement) :
    MixedTwistShift.Statement.{u, w} := by
  intro k _ Ω _ _ N x n qq hp hh hle hdim L M d
  set L' : Fin (n + 1) → LineBundle k x := Fin.snoc (α := fun _ => LineBundle k x) L M with hL'
  set ν : Finset (Fin n) → ℕ → Fin (n + 1) → ℕ :=
    fun T m => Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m with hν
  set f : (Fin (n + 1) → ℕ) → ℤ → ℚ := fun e c => (pieceChar k qq 0 L' e c : ℚ) with hf
  set Ls : Fin n → SubSystem k x Ω := fun i => (L i).toSubSystem with hLs

  have hA : ∀ T (c : ℤ), ((tensorSub Ls T).twist M.toSubSystem).twist (twistSys k x c) =
      ((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T 1)).twist (twistSys k x c) := by
    intro T c
    congr 1
    refine SubSystem.ext_sub fun I => ?_
    rw [twistPows_snoc_sub, SubSystem.twist_sub_eq_mul_of_line, pow_one]
  have hB : ∀ T (c : ℤ), (tensorSub Ls T).twist (twistSys k x c) =
      ((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T 0)).twist (twistSys k x c) := by
    intro T c
    congr 1
    refine SubSystem.ext_sub fun I => ?_
    rw [twistPows_snoc_sub, pow_zero, one_mul]

  have hev : ∀ m : ℕ, ∀ᶠ c : ℤ in atTop, ∀ T : Finset (Fin n),
      restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
        (twistSys k x c)) = pieceChar k qq 0 L' (ν T m) c :=
    fun m => eventually_all.2 fun T => hR k Ω N x qq hh hle (n + 1) L' (ν T m)
  have hsum : ∀ (m : ℕ) (c : ℤ), (∀ T : Finset (Fin n),
      restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
        (twistSys k x c)) = pieceChar k qq 0 L' (ν T m) c) →
      ((∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        restrLen qq (((twistSys k x 0).twistPows (n + 1) (fun j => (L' j).toSubSystem) (ν T m)).twist
          (twistSys k x c)) : ℤ) : ℚ) = subsetDiff n f m c := by
    intro m c h
    rw [subsetDiff]
    push_cast
    exact Finset.sum_congr rfl fun T _ => by rw [h T]
  obtain ⟨hconst, hzero⟩ := hD n f (pieceChar_isNumPolyLT hH hS hP L' (n + 1) qq hp hh hle hdim 0)
  have hT1 : Tendsto (fun c : ℕ => (c : ℤ) + d) atTop atTop :=
    tendsto_atTop_add_const_right _ d tendsto_natCast_atTop_atTop
  have hLhs : ∀ᶠ c : ℕ in atTop, ((∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
      restrLen qq (((tensorSub Ls T).twist M.toSubSystem).twist (twistSys k x ((c : ℤ) + d))) : ℤ) : ℚ) =
        subsetDiff n f 1 ((c : ℤ) + d) := by
    filter_upwards [hT1.eventually (hev 1)] with c hc
    simp only [hA]
    exact hsum 1 _ hc
  split_ifs with hW
  ·
    have hI : ∀ᶠ c : ℕ in atTop, (interSum qq Ls c : ℚ) = subsetDiff n f 0 (c : ℤ) := by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually (hev 0)] with c hc
      rw [interSum]
      simp only [hB]
      exact hsum 0 _ hc
    obtain ⟨c₀, hc₀⟩ := hI.exists_forall_of_atTop
    have hκ : ∀ᶠ c : ℕ in atTop, interSum qq Ls c = interSum qq Ls c₀ := by
      filter_upwards [eventually_ge_atTop c₀] with c hc
      exact_mod_cast (hc₀ c hc).trans ((hconst 0 0 c c₀).trans (hc₀ c₀ le_rfl).symm)
    have hlim : interNum qq Ls = interSum qq Ls c₀ :=
      (tendsto_const_nhds.congr' (hκ.mono fun _ hc => hc.symm)).limUnder_eq
    rw [hlim]
    filter_upwards [hLhs] with c hc
    exact_mod_cast hc.trans ((hconst 1 0 _ c₀).trans (hc₀ c₀ le_rfl).symm)
  ·
    have hlow : IsNumPolyLT (n + 1) n f := by
      by_cases hrel : ∃ i, (X i : Poly k N) ∉ qq
      · have := hp
        obtain ⟨e, he⟩ := SnapperSections.exists_dim_eq qq hh hrel
        have hen : e ≠ n := fun h => hW ⟨hp, hh, hle, hrel, by subst h; exact he⟩
        have hle' : e + 1 ≤ n + 1 := by
          rw [he] at hdim
          exact_mod_cast hdim
        refine pieceChar_isNumPolyLT hH hS hP L' n qq hp hh hle ?_ 0
        rw [he]
        exact_mod_cast (by omega : e + 1 ≤ n)
      · push Not at hrel
        exact ⟨0, Or.inl rfl, fun e c => by simp [hf, pieceChar_of_irrelevant qq hrel]⟩
    filter_upwards [hLhs] with c hc
    exact_mod_cast hc.trans (hzero hlow 1 _)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMuLineNormEq
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

namespace MuLineNormEq

omit [Algebra ℚ Ω] in

theorem valAt_torusSmul {y : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y))
    {s : K → ℂ} (hs : ∀ k, s k ≠ 0) (hsw : torusSmul s w ∈ mcPts (mCoordIdeal y)) {a : Ω} {v : ℂ}
    (hv : IsValueAt y a w v) : valAt y a (torusSmul s w) = valAt y a w := by
  rw [LowerBoundFree.valAt_eq hw hv]
  exact LowerBoundFree.valAt_eq hsw
    (HermMetricEq.isValueAt_iff.2 ((HermMetricEq.isValueAt_iff.1 hv).smul s hs))

omit [Algebra ℚ Ω] in

theorem exists_unit_value {y : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y))
    {c : (k : K) → ι k} {f u : Ω} (hdom : InFrameDomain y c f w) (hu : IsUnitOn y c f u) :
    ∃ v, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y u w v ∧ v ≠ 0 := by
  obtain ⟨hc, v, hv, hv0⟩ := hdom
  have hf0 : f ≠ 0 := fun h0 => hv0 (isValueAt_zero hw (by rwa [h0] at hv))
  have hfi := HermMetricEq.regularAt_inv hf0 ⟨v, hv, hv0⟩
  have hreg : ∀ a : Ω, (∃ n : ℕ, f ^ n * a ∈ chartRing ℤ (segreCoord y) c) →
      IndefiniteRowSideFullHecke.LowerBoundFree.RegularAt y a w := by
    rintro a ⟨n, hn⟩
    have h1 := (HermMetricEq.regularAt_pow hfi n).mul
      (IndefiniteRowSideFullHecke.LowerBoundFree.regularAt_of_mem_chartRing hw hc hn)
    rwa [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hf0, one_pow, one_mul] at h1
  obtain ⟨hu0, hu1, hu2⟩ := hu
  obtain ⟨vu, hvu⟩ := hreg _ hu1
  obtain ⟨vi, hvi⟩ := hreg _ hu2
  have h1 : vu * vi = 1 := IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt.unique hw (hvu.mul hvi)
    (by rw [mul_inv_cancel₀ hu0]; exact IndefiniteRowSideFullHecke.LowerBoundFree.isValueAt_one)
  exact ⟨vu, hvu, left_ne_zero_of_mul_eq_one h1⟩

theorem gramAt_eq (D : ComponentData II Ψ K ι Ω E) (τ : Ψ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ D.Xo)
    {b : Fin D.N → E τ} (l : Fin (D.h τ).m)
    (hd : InFrameDomain D.y ((D.h τ).chart l) ((D.h τ).fr l) z) {S : Matrix (Fin D.N) (Fin D.N) Ω}
    (hSe : ∀ q, b q = ∑ p, S p q • (D.h τ).b l p) {Sz : Matrix (Fin D.N) (Fin D.N) ℂ}
    (hSz : ∀ p q, IsValueAt D.y (S p q) z (Sz p q)) :
    LowerBoundFree.gramAt (D.h τ) b z = Szᴴ * (D.h τ).gram l z * Sz := by
  classical
  have hzX : z ∈ mcPts (mCoordIdeal D.y) \ D.Bd := hz
  have hzP := hzX.1
  have hex : ∃ l, InFrameDomain D.y ((D.h τ).chart l) ((D.h τ).fr l) z := ⟨l, hd⟩
  have hd0 := hex.choose_spec
  obtain ⟨T, hT, hTe⟩ := HermMetricEq.exists_coeff ((D.h τ).isFrame hex.choose) hzP hd0
    (HermMetricEq.isFrameAt_of_isFrameOver ((D.h τ).isFrame l) hzP hd).1
  have hTS : ∀ q, b q = ∑ p, (T * S) p q • (D.h τ).b hex.choose p := by
    intro q
    rw [hSe q]
    simp only [hTe, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun p _ => ?_
    rw [mul_comm]
  have hS' : ∃ S' : Matrix (Fin D.N) (Fin D.N) Ω, ∀ q, b q = ∑ p, S' p q • (D.h τ).b hex.choose p :=
    ⟨T * S, hTS⟩
  have hchoose : hS'.choose = T * S := HermMetricEq.coeff_unique ((D.h τ).isFrame hex.choose).2.2.2.1
    fun q => (hS'.choose_spec q).symm.trans (hTS q)
  have hTz : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt D.y (T p q) z (HermMetricEq.valM D.y T z p q) :=
    fun p q => (hT p q).isValueAt hzP
  have hTSz := HermMetricEq.isValueAt_mul hTz (fun p q => HermMetricEq.isValueAt_iff.1 (hSz p q))
  have hvals : (Matrix.of fun p q => valAt D.y (hS'.choose p q) z) = HermMetricEq.valM D.y T z * Sz := by
    ext p q
    rw [hchoose]
    exact LowerBoundFree.valAt_eq hzP (HermMetricEq.isValueAt_iff.2 (hTSz p q))
  have hcomp := (D.h τ).compat hex.choose l z hzX hd0 hd T hTe (HermMetricEq.valM D.y T z)
    (fun p q => HermMetricEq.isValueAt_iff.2 (hTz p q))
  rw [LowerBoundFree.gramAt, dif_pos hex, dif_pos hS', hvals, hcomp, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem gramAt_torusSmul (D : ComponentData II Ψ K ι Ω E) (τ : Ψ) {w : (Σ k, ι k) → ℂ} (hw : w ∈ D.Xo)
    {s : K → ℂ} (hs : ∀ k, s k ≠ 0) (hsw : torusSmul s w ∈ D.Xo) {c : (k : K) → ι k} {f : Ω}
    {b : Fin D.N → E τ} (hb : IsFrameOver D.y (D.W τ) c f b) (hdom : InFrameDomain D.y c f w) :
    LowerBoundFree.gramAt (D.h τ) b (torusSmul s w) = LowerBoundFree.gramAt (D.h τ) b w := by
  have hwX : w ∈ mcPts (mCoordIdeal D.y) \ D.Bd := hw
  obtain ⟨l, hl⟩ := (D.h τ).cover w hwX
  obtain ⟨S, hS, hSe⟩ := HermMetricEq.exists_coeff ((D.h τ).isFrame l) hwX.1 hl
    (HermMetricEq.isFrameAt_of_isFrameOver hb hwX.1 hdom).1
  have hSw : ∀ p q, IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt D.y (S p q) w (HermMetricEq.valM D.y S w p q) :=
    fun p q => (hS p q).isValueAt hwX.1
  have hl' : InFrameDomain D.y ((D.h τ).chart l) ((D.h τ).fr l) (torusSmul s w) :=
    HermMetricEq.inFrameDomain_smul s hs hl
  rw [gramAt_eq D τ hsw l hl' hSe (fun p q => HermMetricEq.isValueAt_iff.2 ((hSw p q).smul s hs)),
    gramAt_eq D τ hw l hl hSe (fun p q => HermMetricEq.isValueAt_iff.2 (hSw p q)),
    (D.h τ).torus l w hwX hl s hs]

theorem datum_norm_pos (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) {w : (Σ k, ι k) → ℂ}
    (hw : w ∈ D.Xo) (d : MuFrameAt H w) : 0 < d.norm := by
  classical
  have hwX : w ∈ mcPts (mCoordIdeal D.y) \ D.Bd := hw
  obtain ⟨vu, hvu, hvu0⟩ := exists_unit_value hwX.1 d.inDom d.unit
  have hval : valAt D.y d.u w = vu := LowerBoundFree.valAt_eq hwX.1 (HermMetricEq.isValueAt_iff.2 hvu)
  unfold MuFrameAt.norm
  refine mul_pos (mul_pos ?_ ?_) (Finset.prod_pos fun τ _ => Real.sqrt_pos.2 ?_)
  · rw [hval]
    exact norm_pos_iff.2 hvu0
  · exact Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (d.inDom.1 k)) _
  · have hP := GramAtPosDef.proof D τ w d.c d.f (d.b τ) hw (d.adapted τ).1 d.inDom
    have h1 := Complex.lt_def.1 hP.det_pos
    have h2 := Complex.lt_def.1
      (hP.submatrix (e := headIdx D.j_le_N) (Fin.castLE_injective D.j_le_N)).det_pos
    unfold quotNormSq
    exact div_pos (by simpa using h1.1) (by simpa using h2.1)

theorem exists_datum_smul (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) {w z : (Σ k, ι k) → ℂ}
    (hw : w ∈ D.Xo) {s : K → ℂ} (hs : ∀ k, s k ≠ 0) (hzs : z = torusSmul s w) (hz : z ∈ D.Xo)
    (d : MuFrameAt H z) : ∃ d' : MuFrameAt H w, d.norm = (∏ k, ‖s k‖ ^ H.aMu k) * d'.norm := by
  subst hzs
  have hwX : w ∈ mcPts (mCoordIdeal D.y) \ D.Bd := hw
  have hzX : torusSmul s w ∈ mcPts (mCoordIdeal D.y) \ D.Bd := hz
  have hdom : InFrameDomain D.y d.c d.f w := by
    have h := HermMetricEq.inFrameDomain_smul (fun k => (s k)⁻¹) (fun k => inv_ne_zero (hs k)) d.inDom
    convert h using 1
    funext p
    simp [torusSmul, inv_mul_cancel_left₀ (hs p.1)]
  refine ⟨⟨d.c, d.f, hdom, d.b, d.adapted, d.u, d.unit, d.eq⟩, ?_⟩
  obtain ⟨vu, hvu, -⟩ := exists_unit_value hwX.1 hdom d.unit
  have hval : valAt D.y d.u (torusSmul s w) = valAt D.y d.u w :=
    valAt_torusSmul hwX.1 hs hzX.1 (HermMetricEq.isValueAt_iff.2 hvu)
  have hprod : (∏ k, ‖torusSmul s w ⟨k, d.c k⟩‖ ^ H.aMu k) =
      (∏ k, ‖s k‖ ^ H.aMu k) * ∏ k, ‖w ⟨k, d.c k⟩‖ ^ H.aMu k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [torusSmul, norm_mul, mul_zpow]
  have hg : ∀ τ, LowerBoundFree.gramAt (D.h τ) (d.b τ) (torusSmul s w) = LowerBoundFree.gramAt (D.h τ) (d.b τ) w :=
    fun τ => gramAt_torusSmul D τ hw hs hz (d.adapted τ).1 hdom
  show ‖valAt D.y d.u (torusSmul s w)‖ * (∏ k, ‖torusSmul s w ⟨k, d.c k⟩‖ ^ H.aMu k) *
      ∏ τ, Real.sqrt (quotNormSq D.j_le_N (LowerBoundFree.gramAt (D.h τ) (d.b τ) (torusSmul s w))) =
    (∏ k, ‖s k‖ ^ H.aMu k) * (‖valAt D.y d.u w‖ * (∏ k, ‖w ⟨k, d.c k⟩‖ ^ H.aMu k) *
      ∏ τ, Real.sqrt (quotNormSq D.j_le_N (LowerBoundFree.gramAt (D.h τ) (d.b τ) w)))
  simp only [hval, hprod, hg]
  ring

theorem proof (D : ComponentData II Ψ K ι Ω E) (H : HodgeData D) (hI : MuFrameNormIndep.Statement D H) :
    MuLineNormEq.Statement D H := by
  intro z hz d
  obtain ⟨s, hs, hzs⟩ := exists_eq_smul_orbitRep z
  set w := orbitRep z with hwdef
  have hzX : z ∈ mcPts (mCoordIdeal D.y) \ D.Bd := hz
  have hwP : w ∈ mcPts (mCoordIdeal D.y) := by
    have h := mcPts_smul D.arith.2.1.2.1 (fun k => (s k)⁻¹) (fun k => inv_ne_zero (hs k)) hzX.1
    convert h using 1
    funext p
    rw [hzs]
    simp [torusSmul, inv_mul_cancel_left₀ (hs p.1)]
  have hw : w ∈ D.Xo := ⟨hwP, fun hB => hzX.2 (by rw [hzs]; exact D.bd_torus w hB s hs)⟩
  obtain ⟨d', hdd'⟩ := exists_datum_smul D H hw hs hzs hz d
  have hpos := datum_norm_pos D H hw d'
  have hM : muMetric H w = d'.norm := by
    rw [muMetric, dif_pos ⟨d'⟩]
    exact hI w hw _ d'
  have hR := refNorm_pos H.aMu hwP.1
  have hRz : refNorm H.aMu z = (∏ k, ‖s k‖ ^ H.aMu k) * refNorm H.aMu w := by
    rw [hzs]
    exact refNorm_smul _ s w
  show refNorm H.aMu z * Real.exp (Real.log (muMetric H w / refNorm H.aMu w)) = d.norm
  rw [hM, Real.exp_log (div_pos hpos hR), hRz, hdd']
  field_simp

end MuLineNormEq

end GroundTheory.Heights₂.Heights.NineStatements
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperSectionX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u w

namespace SnapperSectionClosed

theorem snapperFinite : SnapperFinite.Statement.{u, w, w} :=
  SnapperFinite.proof Extension.full Extension.full TwistTilde.proof TwistTilde.proof TildeShift.proof
    (TildeFiniteE.proof SerreFinite.full)

theorem quotAdd : SnapperQuotAdd.Statement.{u, w, w} :=
  SnapperQuotAdd.proof (SnapperSubquotFinite.proof snapperFinite)

theorem quotDevissage : SnapperQuotDevissage.Statement.{u, w, w} :=
  SnapperQuotDevissage.proof SnapperQuotFilt.proof SnapperQuotIso.proof quotAdd SubFamilyTwist.proof

end SnapperSectionClosed

open SnapperSectionClosed in

theorem SnapperSection.full : SnapperSection.Statement.{u, w} :=
  SnapperSection.proof quotAdd quotDevissage MulQuotEq.proof SectionNonvanish.proof SectionMulInj.proof

end GroundTheory.Heights₂.Heights.Kleiman
end

