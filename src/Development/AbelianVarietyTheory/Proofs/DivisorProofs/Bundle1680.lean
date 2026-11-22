import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThickPointHyperbolic
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1650
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardGroupElementsChartReturnLe
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.ChartMult

open Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def blk (X : Data E r) (b : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin X.p0) (Fin X.p0) ℂ :=
  Matrix.of fun k a => b τ (Fin.castLE X.p0_le k) (Fin.castLE X.p0_le a)

theorem colP_rmul_eq (X : Data E r) (y : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (a : Fin X.p0) :
    X.colP (rmul y b) τ a = ∑ k, blk X b τ k a • X.colP y τ k := by
  classical
  funext i
  have e1 : X.colP (rmul y b) τ a i = ∑ j, y τ i j * b τ j (Fin.castLE X.p0_le a) := by
    show (mat y τ * mat b τ : Matrix (Fin r) (Fin r) ℂ) i (Fin.castLE X.p0_le a) = _
    rw [Matrix.mul_apply]; rfl
  rw [e1, Finset.sum_apply]
  symm
  refine Finset.sum_of_injOn (Fin.castLE X.p0_le) ((Fin.castLE_injective _).injOn)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) (fun j _ hj => ?_) (fun c _ => ?_)
  · have hj' : X.p0 ≤ (j : ℕ) := by
      by_contra h
      exact hj ⟨⟨j, not_le.mp h⟩, by simp, by ext; simp⟩
    rw [(hb τ).2 j _ (by
      show ((Fin.castLE X.p0_le a : Fin r) : ℕ) < j
      have := a.isLt
      simp only [Fin.val_castLE]; omega), mul_zero]
  · show blk X b τ c a * y τ i _ = _
    simp only [blk, Matrix.of_apply]
    rw [mul_comm]

theorem blk_det_ne (X : Data E r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) :
    (blk X b τ).det ≠ 0 := by
  have hup : (mat b τ).BlockTriangular id := fun a c h => (hb τ).2 a c h
  have hd := (hb τ).1
  rw [Matrix.det_of_upperTriangular hup] at hd
  have hup' : (blk X b τ).BlockTriangular id := fun a c h => by
    simp only [blk, Matrix.of_apply]
    exact (hb τ).2 _ _ (by rw [Fin.lt_def]; simp only [Fin.val_castLE]; exact h)
  rw [Matrix.det_of_upperTriangular hup', Finset.prod_ne_zero_iff]
  intro k _
  rw [Finset.prod_ne_zero_iff] at hd
  exact hd _ (Finset.mem_univ _)

end GlobalTheory.ChartMult

namespace GlobalTheory.ChartMult

open Matrix
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gramPos_rmul (X : Data E r) (y : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) (τ : X.Ψ) :
    X.gramPos (rmul y b) τ = (blk X b τ)ᵀ * X.gramPos y τ * (blk X b τ).map (starRingEnd ℂ) := by
  ext a c
  rw [Data.gramPos_apply, colP_rmul_eq X y hb, colP_rmul_eq X y hb, hermC_sum_left]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Data.gramPos_apply,
    hermC_smul_left, hermC_sum_right, hermC_smul_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

theorem posPart_eq_dot (X : Data E r) (y : Frame X.Ψ r) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.posPart y τ v = ((fun a => hermC τ.1 X.Gm v (X.colP y τ a)) ⬝ᵥ
      ((X.gramPos y τ)⁻¹ *ᵥ (fun a => conj (hermC τ.1 X.Gm v (X.colP y τ a))))).re := by
  unfold Data.posPart
  congr 1
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [mul_assoc]; rfl

theorem maj_rmul_any (X : Data E r) (y : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (v : Fin r → ℂ) : X.maj (rmul y b) τ v = X.maj y τ v := by
  unfold Data.maj
  congr 2
  rw [posPart_eq_dot, posPart_eq_dot]
  set B := blk X b τ
  have hB := blk_det_ne X hb τ
  have hc : (fun a => hermC τ.1 X.Gm v (X.colP (rmul y b) τ a)) =
      (fun a => hermC τ.1 X.Gm v (X.colP y τ a)) ᵥ* B.map (starRingEnd ℂ) := by
    funext a
    rw [colP_rmul_eq X y hb, hermC_sum_right]
    simp only [vecMul, dotProduct, hermC_smul_right, Matrix.map_apply]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hw : (fun a => conj (hermC τ.1 X.Gm v (X.colP (rmul y b) τ a))) =
      Bᵀ *ᵥ (fun a => conj (hermC τ.1 X.Gm v (X.colP y τ a))) := by
    funext a
    rw [colP_rmul_eq X y hb, hermC_sum_right]
    simp only [mulVec, dotProduct, hermC_smul_right, Matrix.transpose_apply, map_sum, map_mul,
      Complex.conj_conj]
    rfl
  have hB1 : IsUnit (B.map (starRingEnd ℂ)).det := by
    rw [show B.map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix B from rfl, ← RingHom.map_det]
    exact (Ne.isUnit hB).map _
  have hB2 : IsUnit Bᵀ.det := by rw [Matrix.det_transpose]; exact Ne.isUnit hB
  rw [hc, hw, gramPos_rmul X y hb, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB1,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB2, Matrix.mul_one]

end GlobalTheory.ChartMult

namespace GlobalTheory.ChartMult

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem emb_mulVec' {r : ℕ} (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) E) (v : Fin r → E) :
    Data.emb τ (M *ᵥ v) = (M.map τ) *ᵥ Data.emb τ v := by
  funext a
  simp [Data.emb, Matrix.mulVec, dotProduct, map_sum]

theorem maj_le_four {r : ℕ} (X : DataX E r) {x : Frame X.Ψ r} (hx : IsOrth X.toData x) {ρ : ℝ}
    (hρ : (r : ℝ) ^ 2 * ρ ≤ 1 / 100) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {z z' : V (nd X.toData)}
    (hz : ‖z‖ ≤ ρ) (hz' : ‖z'‖ ≤ ρ) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (heq : lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') b) (v : Fin r → E) :
    ∑ τ, X.maj x τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)) ≤
      4 * ∑ τ, X.maj x τ (Data.emb τ.1 v) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have hr2 : (0 : ℝ) ≤ (r : ℝ) ^ 2 := by positivity
  have hs : ∀ w : V (nd X.toData), ‖w‖ ≤ ρ → (r : ℝ) ^ 2 * ‖w‖ ≤ 1 / 100 := fun w hw =>
    (mul_le_mul_of_nonneg_left hw hr2).trans hρ
  have h1 := (GlobalTheory.T.majorant_chart_point_centre_factor_two E r X.toData x z' hx (hs z' hz') τ
    (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v))).2
  have h2 := (GlobalTheory.T.majorant_chart_point_centre_factor_two E r X.toData x z hx (hs z hz) τ (Data.emb τ.1 v)).1
  have e1 : X.maj (cpt X.toData x z') τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v)) =
      X.maj (cpt X.toData x z) τ (Data.emb τ.1 v) := by
    rw [← maj_rmul_any X.toData _ hb, ← heq, emb_mulVec',
      GlobalTheory.MajInv.maj_lact X.toData (X.Γ_stab γ hγ)]
  rw [e1] at h1
  linarith

end GlobalTheory.ChartMult

namespace GlobalTheory

open Matrix

theorem chart_mult_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r) (x : Frame X.Ψ r) (ε ρ : ℝ), 0 < r → IsOrth X.toData x → 0 < ε → (r : ℝ) ^ 2 * ρ ≤ 1 / 100 → (∀ γ ∈ X.Γ, ∀ v ∈ X.L', (γ : Matrix (Fin r) (Fin r) E).mulVec v ∈ X.L') → (∀ v ∈ X.L', v ≠ 0 → ε ≤ ∑ τ, X.maj x τ (Data.emb τ.1 v)) → ({γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z z' : V (nd X.toData), ‖z‖ ≤ ρ ∧ ‖z'‖ ≤ ρ ∧ ∃ b ∈ Bor X.Ψ r, lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') b}.encard : ℝ≥0∞) ≤ ENNReal.ofReal (multBd E r ε) := by
  intro E _ _ _ r X x ε ρ hr hx hε hρ hL hmin
  classical
  have hdom : x ∈ X.dom := ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfA.dom_of_orth X.toData hx
  obtain ⟨w, hwL, hli, hwB⟩ := exists_short_basis_at X x hdom ε hε hmin
  set Bd : ℝ := (2 * fdeg E * r : ℝ) ^ 4 * dE E ^ 2 / (4 * ε) with hBd
  have hd : 0 ≤ dE E := abs_nonneg _
  have hBd0 : 0 ≤ Bd := by positivity
  set T : Set (Fin r → E) := {v | v ∈ X.L' ∧ ∑ τ, X.maj x τ (Data.emb τ.1 v) ≤ 4 * Bd} with hT
  have hTc := GlobalTheory.T.encard_selfDualLattice_bounded_majorant_le E r X x ε (4 * Bd) hdom hε (by positivity) hmin
  have hTfin : T.Finite := by
    rw [← Set.encard_ne_top_iff]
    intro htop
    rw [htop] at hTc
    simp at hTc
  set Tf := hTfin.toFinset
  set S := {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z z' : V (nd X.toData), ‖z‖ ≤ ρ ∧ ‖z'‖ ≤ ρ ∧ ∃ b ∈ Bor X.Ψ r, lact γ (cpt X.toData x z) = rmul (cpt X.toData x z') b}
  let f : GL (Fin r) E → Fin r → Fin r → E := fun γ i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i
  have hmaps : Set.MapsTo f S (↑(Fintype.piFinset fun _ : Fin r => Tf)) := by
    rintro γ ⟨hγ, z, z', hz, hz', b, hb, heq⟩
    rw [Fintype.coe_piFinset]
    intro i _
    simp only [Tf, Set.Finite.coe_toFinset]
    refine ⟨hL γ hγ _ (hwL i), ?_⟩
    have := ChartMult.maj_le_four X hx hρ hγ hz hz' hb heq (w i)
    have := hwB i
    show ∑ τ, X.maj x τ (Data.emb τ.1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ w i)) ≤ 4 * Bd
    linarith
  have hinj : Set.InjOn f S := by
    intro γ _ γ' _ h
    haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    let bw := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
    have hlin : Matrix.toLin' (γ : Matrix (Fin r) (Fin r) E) = Matrix.toLin' (γ' : Matrix (Fin r) (Fin r) E) :=
      bw.ext fun i => by
        simp only [bw, coe_basisOfLinearIndependentOfCardEqFinrank, Matrix.toLin'_apply]
        exact congrFun h i
    exact Units.ext (Matrix.toLin'.injective hlin)
  have hS := Set.encard_le_encard_of_injOn hmaps hinj
  rw [Set.encard_coe_eq_coe_finsetCard, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hS
  have hTe : T.encard = (Tf.card : ℕ∞) := hTfin.encard_eq_coe_toFinset_card
  rw [hTe, ENat.toENNReal_coe] at hTc
  set a : ℝ := (1 + 2 * Real.sqrt (4 * Bd / ε)) ^ (2 * fdeg E * r) with ha
  have ha0 : 0 ≤ a := by positivity
  have hsq : Real.sqrt (4 * Bd / ε) = 2 * fdeg E * r * (2 * fdeg E * r) * dE E / ε := by
    rw [show 4 * Bd / ε = (2 * fdeg E * r * (2 * fdeg E * r) * dE E / ε) ^ 2 by
      rw [hBd]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hmult : a ^ r = multBd E r ε := by
    rw [ha, hsq, multBd, ← pow_mul]
    congr 1
    · ring
    · ring
  calc (S.encard : ℝ≥0∞) ≤ ((Tf.card ^ r : ℕ) : ℕ∞) := ENat.toENNReal_le.mpr hS
    _ = (Tf.card : ℝ≥0∞) ^ r := by rw [ENat.toENNReal_coe]; push_cast; rfl
    _ ≤ ENNReal.ofReal a ^ r := pow_le_pow_left₀ zero_le hTc r
    _ = ENNReal.ofReal (multBd E r ε) := by rw [← ENNReal.ofReal_pow ha0, hmult]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyTwConj
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FibStable

section Generic

variable {G : Type} [Group G]

theorem twRel_equiv (θ : G →* G) : Equivalence fun x y : G => ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun x => ⟨1, by simp⟩, fun ⟨g, h⟩ => ⟨g⁻¹, by rw [h, map_inv]; group⟩,
    fun ⟨g, h⟩ ⟨k, h'⟩ => ⟨g * k, by rw [h', h, map_mul]; group⟩⟩

def cls (θ : G →* G) (x : G) : TwCl θ := Quot.mk _ x

theorem cls_eq_iff (θ : G →* G) (x y : G) : cls θ x = cls θ y ↔ ∃ g, y = g⁻¹ * x * θ g :=
  ⟨fun h => (twRel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

theorem cls_rep (θ : G →* G) (c : TwCl θ) : cls θ c.rep = c := Quot.out_eq c

theorem rep_cls (θ : G →* G) (y : G) : ∃ g, (cls θ y).rep = g⁻¹ * y * θ g :=
  (cls_eq_iff θ _ _).1 (cls_rep θ (cls θ y)).symm

theorem index_ne_zero [TopologicalSpace G] [IsTopologicalGroup G] (θ : G →* G) (K K' : Subgroup G)
    (hK : IsCompact (K : Set G)) (hK' : IsLevel θ K K') (f : G → ℂ) (hf : IsHecke K' f) (δ x : G) :
    (rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k))).index ≠ 0 := by
  obtain ⟨ho, -, hθ⟩ := hK'
  have h1 : K'.subgroupOf K ≤ rStab fun k : K => f ((x * k)⁻¹ * δ * θ (x * k)) := by
    intro k' hk' k
    rw [Subgroup.mem_subgroupOf] at hk'
    have e : (x * ((k * k' : K) : G))⁻¹ * δ * θ (x * ((k * k' : K) : G)) =
        (k' : G)⁻¹ * ((x * k)⁻¹ * δ * θ (x * k)) * θ k' := by
      simp only [Subgroup.coe_mul, map_mul]; group
    show f _ = f _
    rw [e, (hf.2 _ (hθ _ hk') _).2, (hf.2 _ (K'.inv_mem hk') _).1]
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have ho' : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := ho.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ ho'
  have h2 : (K'.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  intro h0
  exact h2 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.index_dvd_of_le h1))

theorem eq_single {D : Type} (B : D → ℂ) (h01 : ∀ d, B d = 0 ∨ B d = 1) (hs : ∑ᶠ d, B d = 1) :
    ∃ u, ∀ d, B d = if d = u then 1 else 0 := by
  have hfin : (Function.support B).Finite := by
    by_contra h
    rw [finsum_of_infinite_support h] at hs
    exact zero_ne_one hs
  rw [finsum_eq_sum _ hfin] at hs
  have hc : hfin.toFinset.card = 1 := by
    have : ∑ d ∈ hfin.toFinset, B d = (hfin.toFinset.card : ℂ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Set.Finite.mem_toFinset] at hd
      rcases h01 d with h | h
      · exact absurd h hd
      · simp [h]
    rw [this] at hs
    exact_mod_cast hs
  obtain ⟨u, hu⟩ := Finset.card_eq_one.1 hc
  refine ⟨u, fun d => ?_⟩
  split_ifs with h
  · subst h
    have : d ∈ hfin.toFinset := by rw [hu]; exact Finset.mem_singleton_self _
    rw [Set.Finite.mem_toFinset] at this
    rcases h01 d with h' | h'
    · exact absurd h' this
    · exact h'
  · by_contra hne
    have : d ∈ hfin.toFinset := by rw [Set.Finite.mem_toFinset]; exact hne
    rw [hu, Finset.mem_singleton] at this
    exact h this

end Generic

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def locTerm (n : ℕ) (w : Pl E) (P : E[X]) (φ : GLw n w → ℂ) (d : TwCl (thL n w)) : ℂ :=
  if (nrmL n w d.rep).val.charpoly = atPl w P then twOrb (thL n w) (GlobalTheory.LFun.KGL w n) d.rep φ else 0

theorem charpoly_twConj (n : ℕ) (w : Pl E) (g y : GLw n w) :
    (nrmL n w (g⁻¹ * y * thL n w g)).val.charpoly = (nrmL n w y).val.charpoly := by
  rw [nrmL_twConj, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']

theorem stTw_eq (n : ℕ) (w : Pl E) (P : E[X]) (φ : GLw n w → ℂ) :
    stTw n w (atPl w P) φ = ∑ᶠ d, locTerm n w P φ d := by
  unfold stTw clSum locTerm
  refine finsum_congr fun d => ?_
  simp only [Set.mem_setOf_eq, Pi.one_apply, one_mul]

theorem locTerm_cls (n : ℕ) (w : Pl E) (P : E[X]) (K' : Subgroup (GLw n w))
    (hK' : IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) K') (φ : GLw n w → ℂ) (hφ : IsHecke K' φ) (y : GLw n w)
    (hy : (nrmL n w y).val.charpoly = atPl w P) :
    locTerm n w P φ (cls (thL n w) y) = twOrb (thL n w) (GlobalTheory.LFun.KGL w n) y φ := by
  obtain ⟨g, hg⟩ := rep_cls (thL n w) y
  unfold locTerm
  rw [hg, charpoly_twConj, if_pos hy]
  apply GlobalTheory.TwOrbConj.twOrb_twConj
  intro x
  exact index_ne_zero _ _ _ (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).2 hK' φ hφ y x

end Local

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ K' : ∀ w : Pl E, Subgroup (GLw n w), IsLevelFam (thL n) (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' → ∀ φ : ∀ w : Pl E, GLw n w → ℂ, IsTest (fun w : Pl E => GlobalTheory.LFun.KGL w n) K' φ → ∀ P ∈ Ell E n, (∑ᶠ c : TwCl (thE E n), if (c.rep * thE E n c.rep).val.charpoly = P then ∏ᶠ w ∈ S, twOrb (thL n w) (GlobalTheory.LFun.KGL w n) (locEl n w c.rep) (φ w) else 0) * (2 : ℂ) ^ nfac P = (2 : ℂ) ^ (n * Fintype.card (InfinitePlace E)) * ∏ᶠ w ∈ S, stTw n w (atPl w P) (φ w) := by
  intro E _ _ _ hU n S hS K' hK' φ hφ P hP
  obtain ⟨δ₀, hδ₀⟩ := (GlobalTheory.T.kappaConstant_mul_of_coprime_ellipticPolynomials E hU n 0 P 1 hP
    ⟨monic_one, natDegree_one, separable_one, fun τ z hz => by simp at hz⟩ isCoprime_one_right).2.1
  obtain ⟨A, hA⟩ : ∃ A : Set (TwCl (thE E n)), A = {c | (c.rep * thE E n c.rep).val.charpoly = P} := ⟨_, rfl⟩
  have hcA : ∀ c, c ∈ A ↔ (c.rep * thE E n c.rep).val.charpoly = P := fun c => by rw [hA]; rfl
  have hL : (∑ᶠ c : TwCl (thE E n), if (c.rep * thE E n c.rep).val.charpoly = P then
      ∏ᶠ w ∈ S, twOrb (thL n w) (GlobalTheory.LFun.KGL w n) (locEl n w c.rep) (φ w) else 0) =
      ∑ᶠ c : TwCl (thE E n), if c ∈ A then
      ∏ᶠ w ∈ S, locTerm n w P (φ w) (cls (thL n w) (locEl n w c.rep)) else 0 := by
    refine finsum_congr fun c => ?_
    by_cases hc : (c.rep * thE E n c.rep).val.charpoly = P
    · rw [if_pos hc, if_pos ((hcA c).2 hc)]
      exact finprod_mem_congr rfl fun w _ => (locTerm_cls n w P (K' w) (hK'.1 w) (φ w) (hφ.1 w) _
        (by rw [ThBasic.charpoly_nrmL hU, hc])).symm
    · rw [if_neg hc, if_neg (fun h => hc ((hcA c).1 h))]
  have hR : ∏ᶠ w ∈ S, stTw n w (atPl w P) (φ w) = ∏ᶠ w ∈ S, ∑ᶠ d, locTerm n w P (φ w) d :=
    finprod_mem_congr rfl fun w _ => stTw_eq n w P (φ w)
  rw [hL, hR]
  refine GlobalTheory.T.finsum_restricted_product_count (Pl E) (TwCl (thE E n)) (fun w => TwCl (thL n w)) S (fun w => locTerm n w P (φ w))
    (fun c w => cls (thL n w) (locEl n w c.rep)) A
    (nfac P) (n * Fintype.card (InfinitePlace E)) (fun w => ⟨cls _ 1⟩) ?_ ?_ ?_ ?_
  · intro w _
    refine (GlobalTheory.BCT.ClsFin.classes_finite E hU n w (atPl w P) hP.2.2.1.map).1.subset fun d hd => ?_
    by_contra h
    exact Function.mem_support.1 hd (by unfold locTerm; exact if_neg h)
  · filter_upwards [GlobalTheory.T.twisted_orbital_integral_spherical_unit E hU n S hS P hP, hφ.2, GlobalTheory.T.stable_twisted_orbital_unit_almost_all E hU n P hP] with w h1 h2 h3
    refine eq_single _ (fun d => ?_) ?_
    · try dsimp only
      unfold locTerm
      rw [h2]
      split_ifs with h
      · rw [h1 _ h]; split_ifs <;> simp
      · exact Or.inl rfl
    · try dsimp only
      rw [← stTw_eq, h2]
      exact h3
  · intro c hc
    rw [hcA] at hc
    filter_upwards [GlobalTheory.T.twisted_orbital_integral_spherical_unit E hU n S hS P hP, hφ.2, GoodInt.eventually_mem_KGL c.rep,
      GoodInt.eventually_mem_KGL (c.rep * thE E n c.rep)] with w h1 h2 h3 h4
    have hy : (nrmL n w (locEl n w c.rep)).val.charpoly = atPl w P := by rw [ThBasic.charpoly_nrmL hU, hc]
    have hK : locEl n w c.rep ∈ GlobalTheory.LFun.KGL w n := by
      unfold locEl
      split_ifs
      exacts [h4, h3]
    try dsimp only
    rw [locTerm_cls n w P (K' w) (hK'.1 w) (φ w) (hφ.1 w) _ hy, h2, h1 _ hy, if_pos ⟨1, by simpa using hK⟩]
  · intro e he
    try dsimp only at he
    have hpoly : ∀ w ∈ S, (nrmL n w (e w).rep).val.charpoly = atPl w P := fun w hw => by
      by_contra h
      exact he w hw (by unfold locTerm; exact if_neg h)
    obtain ⟨y, hyS, hy1, hy2⟩ : ∃ y : ∀ w, GLw n w, (∀ w ∈ S, cls (thL n w) (y w) = e w) ∧
        (∀ w, (nrmL n w (y w)).val.charpoly = atPl w P) ∧ ∀ᶠ w in cofinite, y w ∈ GlobalTheory.LFun.KGL w n := by
      refine ⟨fun w => if w ∈ S then (if h : ∃ g : GLw n w, g⁻¹ * (e w).rep * thL n w g ∈ GlobalTheory.LFun.KGL w n then
          h.choose⁻¹ * (e w).rep * thL n w h.choose else (e w).rep) else locEl n w δ₀, fun w hw => ?_, fun w => ?_, ?_⟩
      · try dsimp only
        rw [if_pos hw]
        split_ifs with h
        · rw [← (cls_eq_iff (thL n w) (e w).rep _).2 ⟨h.choose, rfl⟩, cls_rep]
        · exact cls_rep _ _
      · try dsimp only
        split_ifs with hw h
        · rw [charpoly_twConj]; exact hpoly w hw
        · exact hpoly w hw
        · rw [ThBasic.charpoly_nrmL hU, hδ₀]
      · filter_upwards [GlobalTheory.T.twisted_orbital_integral_spherical_unit E hU n S hS P hP, hφ.2, GoodInt.eventually_mem_KGL δ₀,
          GoodInt.eventually_mem_KGL (δ₀ * thE E n δ₀)] with w h1 h2 h3 h4
        try dsimp only
        split_ifs with hw h
        · exact h.choose_spec
        · exfalso
          have hne := he w hw
          unfold locTerm at hne
          rw [if_pos (hpoly w hw), h2, h1 _ (hpoly w hw), if_neg h] at hne
          exact hne rfl
        · unfold locEl
          split_ifs
          exacts [h4, h3]
    have hc := GlobalTheory.T.twisted_class_count_char_poly E hU n S hS P hP y hy1 hy2
    convert hc using 2
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c => and_congr (hcA c) (forall₂_congr fun w hw => ?_))
    try dsimp only
    rw [← hyS w hw, eq_comm, cls_eq_iff]

end GlobalTheory.BCT.FibStable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondEIsCoprimeHalfDifferent
section
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.StdDatum.HalfDiff

theorem isCoprime_of_natCast_mem {D : D7} {I : Ideal (𝓞 D.host.E)} {N : ℕ} (hN : Nat.Coprime N (D.host.QS * D.host.q))
    (hI : (N : 𝓞 D.host.E) ∈ I) : IsCoprime I D.host.𝔟 := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  have hb : D.host.𝔟 ≤ M := le_sup_right.trans hle
  have h0 : M ≠ ⊥ := fun e => ReciprocityTheory.ChartRestriction.G.PullbackSections.MLI.bb_ne_bot D (eq_bot_iff.2 (e ▸ hb))
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨M, hM.isPrime, h0⟩
  exact GlobalTheory.HalfCompare.not_mem_of_coprime P hN (GlobalTheory.HalfCompare.two_q_mem (P := P) (Ideal.dvd_iff_le.2 hb))
    (hle (Ideal.mem_sup_left hI))

theorem coprime_of_mod {a b m : ℕ} (h : a % m = 1) (hb : b ∣ m) : Nat.Coprime a b := by
  have : Nat.Coprime a m := by rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h, Nat.gcd_one_left]
  exact this.coprime_dvd_right hb

theorem exists_nat_mem_place_coprime {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) {v : HeightOneSpectrum (𝓞 D.host.F)} (hv : v ∈ P.S0) :
    ∃ p : ℕ, Nat.Coprime p (D.host.QS * D.host.q) ∧ ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have hg : ∀ k, Nat.Coprime (D.host.g k) (D.host.QS * D.host.q) := fun k =>
    coprime_of_mod (D.ntypes.g_cond k) (dvd_mul_right _ _)
  rcases P.mem_S0_of_sum_eq.1 hv with rfl | h1
  · exact ⟨q0 D, coprime_of_mod (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
      (Dvd.dvd.mul_left ⟨D.host.d, rfl⟩ _), P.basePlace_over_qZero⟩
  · rcases (S1_mem_OmF D).1 h1 with h' | h' | h' | h'
    · exact ⟨_, hg 0, h'⟩
    · exact ⟨_, hg 1, h'⟩
    · exact ⟨_, h.1, h'⟩
    · exact ⟨_, h.2, h'⟩

theorem exists_nat_mem_condE {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    ∃ N : ℕ, Nat.Coprime N (D.host.QS * D.host.q) ∧ (N : 𝓞 D.host.E) ∈ SqNum.condE P := by
  classical
  choose! p hp hm using fun v (hv : v ∈ P.S0) => exists_nat_mem_place_coprime P h hv
  refine ⟨∏ v ∈ P.S0, p v ^ condExp P v, Nat.Coprime.prod_left fun v hv => (hp v hv).pow_left _, ?_⟩
  unfold SqNum.condE
  push_cast
  refine Ideal.prod_mem_prod fun v hv => Ideal.pow_mem_pow ?_ _
  have h1 : ((p v : ℕ) : 𝓞 D.host.F) ∈ ((P.w v).under (𝓞 D.host.F)).asIdeal := by
    rw [P.under_w hv]; exact hm v hv
  simpa using Ideal.mem_comap.1 h1

theorem condE_isCoprime_halfDifferent {D : D7} {T : Type} {L : LevCh D T} (P : Places L)
    (h : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    IsCoprime (SqNum.condE P) D.host.𝔟 ∧ IsCoprime (D.host.conj • SqNum.condE P) D.host.𝔟 := by
  obtain ⟨N, hN, hm⟩ := exists_nat_mem_condE P h
  refine ⟨isCoprime_of_natCast_mem hN hm, isCoprime_of_natCast_mem hN ?_⟩
  have h1 := Ideal.smul_mem_pointwise_smul D.host.conj _ _ hm
  have h2 : D.host.conj • (N : 𝓞 D.host.E) = N := map_natCast (MulSemiringAction.toRingHom _ _ D.host.conj) N
  rwa [h2] at h1

end GlobalTheory.FunObj.StdDatum.HalfDiff

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeSupLatticeComponentEqStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_supLattice_component_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), ∀ j ≤ P.T, (h.data f₁ f₂ th k).degM j = GlobalTheory.AllWt.degOn U x V dict Z (GlobalTheory.AllWt.wtOf Dw (P.wt j) 0) := by
  first | exact @GlobalTheory.CompHS.Ready.degM_eq | exact GlobalTheory.CompHS.Ready.degM_eq | (intros; apply GlobalTheory.CompHS.Ready.degM_eq <;> assumption)
end

