import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SummableOfCount
section
noncomputable section

open scoped NNReal TensorProduct
open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Eis.Conv GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GodementSectionReduction

open GlobalTheory.SummCount in

theorem summable_of_count (ι : Type) (n N : ℕ) (b C t : ℝ) (k : ι → Fin n → ℕ)
    (h : ι → ℝ) (hb : 1 < b) (ht : (N : ℝ) < t)
    (hh : ∀ q, 0 ≤ h q ∧ h q ≤ C * ∏ i, (b ^ k q i)⁻¹)
    (hT : ∀ (m : Fin n → ℕ) (T : Finset ι), (∀ q ∈ T, k q = m) →
      (T.card : ℝ) ≤ C * ∏ i, b ^ (N * m i)) :
    Summable fun q => h q ^ t := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg N) ht.le
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨q0⟩⟩
  · exact .of_finite
  have hP : ∀ m : Fin n → ℕ, 0 < ∏ i, (b ^ m i)⁻¹ := fun m => by positivity
  have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right (hP (k q0))).1 ((hh q0).1.trans (hh q0).2)
  set r := b ^ ((N : ℝ) - t) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hb0.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  set g : (Fin n → ℕ) → ℝ := fun m => C * C ^ t * ∏ i, r ^ m i with hg_def
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    simp only [hg_def]; positivity
  have hg : Summable g :=
    (summable_prod_fin_tuple (summable_geometric_of_lt_one hr0 hr1) (fun _ => pow_nonneg hr0 _)
      n).mul_left _
  have key : ∀ q, h q ^ t ≤ C ^ t * ∏ i, ((b ^ k q i)⁻¹) ^ t := fun q => by
    rw [Real.finset_prod_rpow _ _ (fun i _ => by positivity), ← Real.mul_rpow hC (hP _).le]
    exact Real.rpow_le_rpow (hh q).1 (hh q).2 ht0
  refine summable_of_sum_le (c := ∑' m, g m) (fun q => Real.rpow_nonneg (hh q).1 _) fun T => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := T.image k)
    (fun q hq => Finset.mem_image_of_mem k hq)]
  refine le_trans (Finset.sum_le_sum fun m _ => ?_) (hg.sum_le_tsum _ (fun m _ => hg0 m))
  calc ∑ q ∈ T with k q = m, h q ^ t
      ≤ ∑ q ∈ T with k q = m, C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t :=
        Finset.sum_le_sum fun q hq => by
          have := key q
          rwa [(Finset.mem_filter.1 hq).2] at this
    _ = ((T.filter (k · = m)).card : ℝ) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * ∏ i, b ^ (N * m i)) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) :=
        mul_le_mul_of_nonneg_right (hT m _ fun q hq => (Finset.mem_filter.1 hq).2)
          (mul_nonneg (Real.rpow_nonneg hC _)
            (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _))
    _ = g m := by
        simp only [hg_def, hr, ← pow_mul_inv_rpow_eq hb0 N, Finset.prod_mul_distrib]
        ring

open GlobalTheory.Eis.Conv.CovSkew in

theorem cover_adele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) : ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : ℕ, ∃ Y : Finset (AF F ⊗[F] E),
      (Y.card : ℝ) ≤ C * ((4 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ m ∧ ∀ z : AF F ⊗[F] E, ∃ x : E, ∃ y ∈ Y, ∃ ω ∈ Ω,
        z = inclR (F := F) (AF F) x + y + (halfE F E).1 ^ m * ω := by
  classical
  haveI := hσ.1
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact F
  obtain ⟨δ, -, hsp⟩ := exists_delta F E σ hσ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := isTopologicalRing_tens
  have hcont : Continuous fun p : AF F × AF F => psi (F := F) δ p.1 p.2 := by
    unfold psi
    fun_prop
  refine ⟨_, C₀ ^ 2, (hΩ₀.prod hΩ₀).image hcont, fun m => ?_⟩
  obtain ⟨Y, hY, hYc⟩ := hcov m
  refine ⟨(Y ×ˢ Y).image fun y => psi δ y.1 y.2, ?_, fun z => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_product, Nat.cast_mul]
    refine (mul_self_le_mul_self (Nat.cast_nonneg _) hY).trans (le_of_eq ?_)
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, mul_pow]
    ring
  · obtain ⟨u, v, rfl⟩ := exists_coords δ hsp z
    set c : AF F := algebraMap F (AF F) 2⁻¹ with hc
    have h2 : 2 * c = 1 := by
      rw [hc, ← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
    obtain ⟨x, y, hy, ω, hω, e⟩ := hYc (c * (u + v))
    obtain ⟨x', y', hy', ω', hω', e'⟩ := hYc (c * (v - u))
    refine ⟨(x - x') • (1 : E) + (x + x') • δ, _, Finset.mem_image.mpr ⟨(y, y'), Finset.mem_product.2 ⟨hy, hy'⟩, rfl⟩,
      _, ⟨(ω, ω'), ⟨hω, hω'⟩, rfl⟩, ?_⟩
    have : (halfE F E).1 = algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1 := rfl
    rw [this, ← map_pow, ← psi_split, ← e, ← e', psi_eq]
    congr 2
    · linear_combination (-u) * h2
    · linear_combination (-v) * h2

variable {D : D7} {T T₀ : HSp D} {r : ℕ}

abbrev hf (D : D7) : (AE D)ˣ := halfE D.host.F D.host.E

abbrev bs (D : D7) : ℝ := 4 ^ Fintype.card (InfinitePlace D.host.F)

theorem one_lt_bs : 1 < bs D := one_lt_pow₀ (by norm_num) Fintype.card_ne_zero

theorem val_dg (m : Fin r → ℕ) : (dg (hf D) fun i => (m i : ℤ)).1 = diagonal fun i => (hf D).1 ^ m i := by
  simp [dg]

theorem adj_dg (l : Fin r → ℤ) : adj (dg (hf D) l)⁻¹.1 = (dg (hf D) l)⁻¹.1 :=
  congrArg Units.val (cti_dg (σ := cA D) (sigR_halfE D.sp.cm.sig) l)

theorem adj_dg' (l : Fin r → ℤ) : adj (dg (hf D) l).1 = (dg (hf D) l).1 :=
  congrArg Units.inv (cti_dg (σ := cA D) (sigR_halfE D.sp.cm.sig) l)

theorem cover_rect (D : D7) (r n : ℕ) : ∃ (K : Set (Mx D r n)) (C : ℝ), IsCompact K ∧ ∀ m : Fin r → ℕ,
    ∃ Y : Finset (Mx D r n), (Y.card : ℝ) ≤ C * ∏ i, bs D ^ (n * m i) ∧ ∀ x : Mx D r n, ∃ x₀ ∈ ratMx D r n, ∃ y ∈ Y,
      ∃ ω ∈ K, x = x₀ + (y + (dg (hf D) fun i => (m i : ℤ)).1 ⬝ ω) := by
  classical
  obtain ⟨Ω, C, hΩ, h⟩ := cover_adele _ _ _ (AdelicU.isCMExt_host D)
  choose Y hY h using h
  refine ⟨Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω, (C ^ n) ^ r,
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ, fun m =>
    ⟨Fintype.piFinset fun i => Fintype.piFinset fun _ => Y (m i), ?_, fun x => ?_⟩⟩
  · have h1 : (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin n => Y (m i)).card = ∏ i, (Y (m i)).card ^ n := by
      simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (Nat.cast_le.2 h1.le).trans ?_
    push_cast
    refine (Finset.prod_le_prod (fun _ _ => by positivity) fun i _ =>
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hY (m i)) n).trans (le_of_eq ?_)
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul _ (m _),
      mul_comm n]
  · choose x₀ y hy ω hω e using fun i j => h (m i) (x i j)
    refine ⟨_, rat_mem (of x₀), of y, Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 (hy i), of ω,
      fun i _ j _ => hω i j, ?_⟩
    ext i j
    rw [val_dg, Matrix.add_apply, Matrix.add_apply, diagonal_mul, ← add_assoc]
    exact e i j

def sk (x : Mx D r r) : skewA D r :=
  ⟨half D • (x - adj x), by rw [mem_skewA, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]⟩

theorem continuous_sk : Continuous (sk : Mx D r r → _) := by
  have := (lattice_Mx D r r).1
  have : ContinuousSub (Mx D r r) := IsTopologicalAddGroup.to_continuousSub
  exact ((continuous_id.sub continuous_adj).const_smul (half D)).subtype_mk _

theorem sk_add (x y : Mx D r r) : sk (x + y) = sk x + sk y := Subtype.ext (by
  change half D • (x + y - adj (x + y)) = half D • (x - adj x) + half D • (y - adj y)
  rw [adj_add, ← smul_add, add_sub_add_comm])

theorem sk_coe (x : skewA D r) : sk x.1 = x := Subtype.ext (by
  change half D • (x.1 - adj x.1) = x.1
  rw [mem_skewA.1 x.2, sub_neg_eq_add, smul_add, half_smul_add])

theorem sk_conj (a x : Mx D r r) : sk (a ⬝ x ⬝ adj a) = skewConj a (sk x) := Subtype.ext (by
  change half D • (a ⬝ x ⬝ adj a - adj (a ⬝ x ⬝ adj a)) = a ⬝ (half D • (x - adj x)) ⬝ adj a
  rw [adj_mul, adj_mul, adj_adj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc a (adj x)])

theorem cover_skewA (D : D7) (r : ℕ) : ∃ (K : Set (skewA D r)) (C : ℝ), IsCompact K ∧ ∀ m : Fin r → ℕ,
    ∃ Y : Finset (skewA D r), (Y.card : ℝ) ≤ C * ∏ i, bs D ^ (r * m i) ∧ ∀ x : skewA D r, ∃ x₀ : skewA D r,
      x₀.1 ∈ ratMx D r r ∧ ∃ y ∈ Y, ∃ ω ∈ K, x = x₀ + (y + skewConj (dg (hf D) fun i => (m i : ℤ)).1 ω) := by
  classical
  have hc := AdelicU.isCMExt_host D
  haveI := hc.1
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact D.host.F
  obtain ⟨Ω, C, hΩ, h⟩ := GlobalTheory.T.skewHermitian_adelic_cover_of_adele_cover _ _ _ hc _ _ _ hΩ₀ hcov r
  have hK : IsCompact (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω : Set (Mx D r r)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ
  refine ⟨_, C, hK.image continuous_sk, fun m => ?_⟩
  obtain ⟨Y, hY, h⟩ := h m
  refine ⟨Finset.image (α := Mx D r r) sk Y, (Nat.cast_le.mpr Finset.card_image_le).trans (hY.trans (le_of_eq ?_)),
    fun x => ?_⟩
  · simp only [bs, ← pow_mul, mul_comm _ 2, show (4 : ℝ) = 2 ^ 2 by norm_num]
  · obtain ⟨S, y, hy, ω, hω, e⟩ := h x.1 x.2
    refine ⟨sk (rat S), ratMx_smul _ (sub_mem (rat_mem _) (ratMx_adj (rat_mem _))), _, Finset.mem_image_of_mem _ hy, _,
      ⟨ω, fun i _ j _ => hω i j, rfl⟩, ?_⟩
    rw [← val_dg] at e
    replace e : x.1 = rat S + y + (dg (hf D) fun i => (m i : ℤ)).1 ⬝ ω ⬝ (dg (hf D) fun i => (m i : ℤ)).1 := e
    rw [← sk_conj, adj_dg', ← sk_add, ← sk_add, ← add_assoc, ← e, sk_coe]

end GlobalTheory.GodementSectionReduction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplecticFormInertSupportedPointsAntidiagonal
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameSympl

open Formalism.UG (cT cT_mul cT_one antiJ)
open GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v}

def evW (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) : AE D →+* w.adicCompletion D.host.E :=
  (GlobalTheory.LFun.InertChart.complEquiv hw h).toRingHom.comp (compFin D.host.F D.host.E v)

theorem secW_apply (z : w.adicCompletion D.host.E) :
    secW hw h z = GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z) := rfl

theorem secW_mul_right (z : w.adicCompletion D.host.E) (A : AE D) :
    secW hw h z * A = secW hw h (z * evW hw h A) := by
  rw [secW_apply, secW_apply, GlobalTheory.EmbChart.tensAt_mul_right]
  congr 1
  rw [map_mul (GlobalTheory.LFun.InertChart.complEquiv hw h).symm]
  show _ = _ * (GlobalTheory.LFun.InertChart.complEquiv hw h).symm ((GlobalTheory.LFun.InertChart.complEquiv hw h) _)
  rw [RingEquiv.symm_apply_apply]

theorem evW_secW (z : w.adicCompletion D.host.E) : evW hw h (secW hw h z) = z := by
  show GlobalTheory.LFun.InertChart.complEquiv hw h (compFin D.host.F D.host.E v (GlobalTheory.EmbChart.tensAt D.host.E v
    ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z))) = z
  rw [GlobalTheory.EmbChart.compFin_tensAt, RingEquiv.apply_symm_apply]

theorem evW_incA (a : D.host.E) : evW hw h (incA D a) = algebraMap D.host.E _ a := by
  show GlobalTheory.LFun.toCompl h (compFin D.host.F D.host.E v ((1 : AF D.host.F) ⊗ₜ[D.host.F] a)) = _
  show GlobalTheory.LFun.toCompl h ((evFin D.host.F v 1) ⊗ₜ[D.host.F] a) = _
  rw [map_one, GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

theorem incA_mul_secW (a : D.host.E) (z : w.adicCompletion D.host.E) :
    incA D a * secW hw h z = secW hw h (algebraMap D.host.E _ a * z) := by
  rw [mul_comm, secW_mul_right, evW_incA, mul_comm]

theorem cA_secW {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c)
    (z : w.adicCompletion D.host.E) : cA D (secW hw h z) = secW hw h (c z) := by
  rw [secW_apply, secW_apply]
  show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig (GlobalTheory.EmbChart.tensAt D.host.E v _) = GlobalTheory.EmbChart.tensAt D.host.E v _
  rw [GlobalTheory.EmbChart.sigR_tensAt]
  congr 1
  apply (GlobalTheory.LFun.InertChart.complEquiv hw h).injective
  rw [RingEquiv.apply_symm_apply]
  have := hc ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm z)
  exact this.symm.trans (congrArg c ((GlobalTheory.LFun.InertChart.complEquiv hw h).apply_symm_apply z))

theorem hO_map_secW {S T : HSp D} {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E}
    (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c) (M N : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    hO S T (M.map (secW hw h)) (N.map (secW hw h)) = secW hw h (Matrix.trace
      ((S.gram⁻¹.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin S.rank) (Fin S.rank) _) *
      cT c N * (T.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin T.rank) (Fin T.rank) _) * M)) := by
  simp only [hO, Matrix.map_apply, cA_secW hc, incA_mul_secW, secW_mul_right, evW_incA, evW_secW, ← map_sum]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, Matrix.map_apply, cT, Matrix.transpose_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl fun c _ => Finset.sum_comm) ?_
  rw [Finset.sum_comm]

variable {L : Type} [Field L]

theorem cT_smul' (c : L →+* L) {m n : ℕ} (k : L) (A : Matrix (Fin m) (Fin n) L) : cT c (k • A) = c k • cT c A := by
  ext i j
  simp [cT, Matrix.smul_apply]

theorem inv_eq_of_frame (c : L →+* L) {n : ℕ} {G G' : Matrix (Fin n) (Fin n) L} (hG : G' * G = 1) (a : GL (Fin n) L)
    (ha : cT c a.1 * G * a.1 = antiJ L n) : G' = a.1 * antiJ L n * cT c a.1 := by
  have h1 : G * a.1 = cT c (a⁻¹).1 * antiJ L n := by
    rw [← ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul]
  have h2 : G * (a.1 * antiJ L n * cT c a.1) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.mul_assoc (cT c (a⁻¹).1),
      Formalism.UG.P.fIwasawa_antiJ_mul_antiJ, Matrix.mul_one, ← cT_mul, Units.mul_inv, cT_one]
  rw [← Matrix.mul_one G', ← h2, ← Matrix.mul_assoc, hG, Matrix.one_mul]

theorem trace_frame (c : L →+* L) {n n' : ℕ} (k : L) (aS : GL (Fin n) L) (aT : GL (Fin n') L)
    (GT J' : Matrix (Fin n') (Fin n') L) (J : Matrix (Fin n) (Fin n) L) (hT : cT c aT.1 * GT * aT.1 = J')
    (x y : Matrix (Fin n') (Fin n) L) :
    Matrix.trace (aS.1 * J * cT c aS.1 * cT c (k • (aT.1 * y * (aS⁻¹).1)) * GT * (k • (aT.1 * x * (aS⁻¹).1))) =
      k * c k * Matrix.trace (J * cT c y * J' * x) := by
  rw [cT_smul', cT_mul, cT_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT c aS.1) (cT c (aS⁻¹).1), ← cT_mul, Units.inv_mul, cT_one, Matrix.one_mul,
    ← Matrix.mul_assoc GT aT.1, ← Matrix.mul_assoc (cT c aT.1) (GT * aT.1), ← Matrix.mul_assoc (cT c aT.1) GT, hT, Matrix.trace_mul_comm aS.1]
  simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  ring

theorem hO_uPt {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : IsInertAt D.host.F D.host.E v w} {h : w.under (𝓞 D.host.F) = v} {S T : HSp D}
    {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (k : w.adicCompletion D.host.E)
    {aS : GL (Fin S.rank) (w.adicCompletion D.host.E)} {aT : GL (Fin T.rank) (w.adicCompletion D.host.E)}
    (hc : GlobalTheory.LFun.IsConjAt D.sp.cm.sig h c)
    (hS : cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = antiJ _ S.rank)
    (hT : cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = antiJ _ T.rank)
    (x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E)) :
    hO S T (uPt hw h k aS aT x) (uPt hw h k aS aT y) =
      secW hw h (k * c k * Matrix.trace (antiJ (w.adicCompletion D.host.E) S.rank * cT c y * antiJ (w.adicCompletion D.host.E) T.rank * x)) := by
  have hG : (S.gram⁻¹.map (algebraMap D.host.E (w.adicCompletion D.host.E)) : Matrix (Fin S.rank) (Fin S.rank) _) *
      S.gram.map (algebraMap D.host.E (w.adicCompletion D.host.E)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S),
      Matrix.map_one _ (map_zero _) (map_one _)]
  rw [uPt, uPt, hO_map_secW hc, inv_eq_of_frame c hG aS hS, trace_frame c k aS aT _ _ _ hT]

theorem symplOH_uPt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), IsConjAt D.sp.cm.sig h c → Formalism.UG.cT c aS.1 * S.gram.map (algebraMap D.host.E _) * aS.1 = Formalism.UG.antiJ _ S.rank → Formalism.UG.cT c aT.1 * T.gram.map (algebraMap D.host.E _) * aT.1 = Formalism.UG.antiJ _ T.rank → ∀ x y : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), ψ (symplOH S T (uPt hw h k aS aT x) (uPt hw h k aS aT y)) = thW ψ hw h (k * c k) (2⁻¹ * GlobalTheory.Hk3.locH c 1 (GlobalTheory.SphTheta.antiG _ S.rank) (GlobalTheory.SphTheta.antiG _ T.rank) x y) := by
  intro D ψ v w hw h S T c k aS aT hc hS hT x y
  have h2 : (2 : w.adicCompletion D.host.E) ≠ 0 := by
    have : CharZero (w.adicCompletion D.host.E) := algebraRat.charZero _
    exact two_ne_zero
  have hx : (2⁻¹ : w.adicCompletion D.host.E) • x + (2⁻¹ : w.adicCompletion D.host.E) • x = x := by
    rw [← add_smul, ← two_mul, mul_inv_cancel₀ h2, one_smul]
  have hl : GlobalTheory.Hk3.locH c 1 (GlobalTheory.SphTheta.antiG _ S.rank) (GlobalTheory.SphTheta.antiG _ T.rank) x y =
      Matrix.trace (antiJ (w.adicCompletion D.host.E) S.rank * cT c y * antiJ (w.adicCompletion D.host.E) T.rank * x) := by
    rw [GlobalTheory.Hk3.locH, one_mul]
    rfl
  conv_lhs => rw [← hx, uPt_add, GlobalTheory.SplitScalar.symplOH_add_left, GlobalTheory.SplitScalar.symplOH_add_self]
  rw [thW_apply, symplO, hO_uPt k hc hS hT, hl, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_assoc]

end GlobalTheory.InertFrameSympl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TameLiftResidueCharacterIsTameNotUnramified
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

noncomputable section

namespace GlobalTheory.TameLiftChar

open ValuativeRel

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem val_le_iff (x y : Fv D.host.F v) :
    valuation (Fv D.host.F v) x ≤ valuation (Fv D.host.F v) y ↔ Valued.v x ≤ Valued.v y := by
  haveI : (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [← Valuation.Compatible.vle_iff_le (v := valuation (Fv D.host.F v)),
    Valuation.Compatible.vle_iff_le (v := (Valued.v : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ))))]

theorem val_lt_one_iff (x : Fv D.host.F v) :
    valuation (Fv D.host.F v) x < 1 ↔ Valued.v x < 1 := by
  have h := val_le_iff (D := D) (v := v) 1 x
  rw [map_one, map_one] at h
  rw [← not_le, ← not_le, h]

theorem val_eq_one_iff (x : Fv D.host.F v) :
    valuation (Fv D.host.F v) x = 1 ↔ Valued.v x = 1 := by
  have h1 := val_le_iff (D := D) (v := v) 1 x
  have h2 := val_le_iff (D := D) (v := v) x 1
  rw [map_one, map_one] at h1 h2
  rw [le_antisymm_iff, le_antisymm_iff, h1, h2]

theorem rdQ_one (φ : SplitProj D v) : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (1 : D.host.E) = 1 := by
  show φ (1 ⊗ₜ 1) = 1
  rw [← Algebra.TensorProduct.one_def, map_one]

def rdQHom (φ : SplitProj D v) : D.host.E →+* Fv D.host.F v :=
  φ.toRingHom.comp (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] _).toRingHom

theorem rdQHom_apply (φ : SplitProj D v) (x : D.host.E) : rdQHom φ x = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x := rfl

theorem val_rdQ_le_one (φ : SplitProj D v) (x : 𝓞 D.host.E) : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) ≤ 1 := by
  let w : Valuation (Fv D.host.F v) (WithZero (Multiplicative ℤ)) := Valued.v
  have hx : IsIntegral ℤ (x : D.host.E) := x.2
  obtain ⟨p, hm, hp⟩ := hx
  have hO : IsIntegral w.integer (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x : D.host.E)) := by
    refine ⟨p.map (Int.castRingHom w.integer), hm.map _, ?_⟩
    rw [Polynomial.eval₂_map, ← rdQHom_apply]
    have : (algebraMap w.integer (Fv D.host.F v)).comp (Int.castRingHom _) =
        (rdQHom φ).comp (algebraMap ℤ D.host.E) := RingHom.ext_int _ _
    rw [this, ← Polynomial.hom_eval₂, hp, map_zero]
  exact (Valuation.integer.integers w).mem_of_integral hO

end GlobalTheory.TameLiftChar

open GlobalTheory.TameLiftChar in
theorem GlobalTheory.tameLift_isTame_not_isUnram : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v) (PP : Pl D.host.E) (ξ : (kP PP)ˣ →* ℂˣ), IsProjAt φ PP → ξ ≠ 1 → ∀ ξl : (Fv D.host.F v)ˣ →* ℂˣ, LiftsChar φ PP ξl ξ → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl := by
  intro D v φ PP ξ hP hξ ξl hl
  refine ⟨?_, ?_⟩
  · intro x hx
    have hr : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (x : Fv D.host.F v) ((1 : (kP PP)ˣ) : kP PP) := by
      refine ⟨1, by simp, ?_⟩
      simpa [rdQ_one] using (val_lt_one_iff _).1 hx
    rw [hl x 1 hr, map_one]
  · intro hun
    obtain ⟨k, hk⟩ : ∃ k, ξ k ≠ 1 := by
      by_contra h; push_neg at h; exact hξ (MonoidHom.ext h)
    obtain ⟨x0, hx0⟩ := Ideal.Quotient.mk_surjective (k : kP PP)
    have hnot : x0 ∉ PP.asIdeal := by
      intro hm
      have : ((k : kP PP)) = 0 := by rw [← hx0]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
      exact k.ne_zero this
    have hle := val_rdQ_le_one φ x0
    have hge : ¬ Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E)) < 1 := fun h => hnot ((hP x0).2 h)
    have h1 : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E)) = 1 := le_antisymm hle (not_lt.1 hge)
    have hne : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (x0 : D.host.E) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
    let u : (Fv D.host.F v)ˣ := Units.mk0 _ hne
    have hr : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.RedRel φ PP (u : Fv D.host.F v) (k : kP PP) := ⟨x0, hx0, by simp [u]⟩
    exact hk ((hl u k hr).symm.trans (hun u ((val_eq_one_iff _).2 h1)))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelModerateGrowthBothVariables
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section
open GlobalTheory.Size
namespace GlobalTheory.Core.Rk.ThetaGrowthBoth

theorem thetaKO_modGrowth₂ : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → GlobalTheory.Grow.ModGrowth₂ S T fun g h => thetaKO om g h f := by
  intro D ψ S T χS χT om hω f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D S.rank T.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne S T
  obtain ⟨C, -, hC⟩ := (H S T rfl rfl).real ψ hθ hU
  exact ⟨C * (sobO ψ θ μ 𝓕 d f).toReal, A, fun g h => (hC χS χT om hω μ 𝓕 hμ f hl).2 g h⟩

end GlobalTheory.Core.Rk.ThetaGrowthBoth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumNonsplitPlaceVacuumAtPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lattice_vacuum_nonsplit_place_vacuum_at_prime : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → Formalism.DivisionValues.conjPl w = w → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ), VacFin ψ S T v f → IsVacAt ψ S T w f := by
  first | exact @GlobalTheory.VacInertAt.isVacAt_of_vacFin | exact GlobalTheory.VacInertAt.isVacAt_of_vacFin | (intros; apply GlobalTheory.VacInertAt.isVacAt_of_vacFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumSplitPlaceVacuumAtPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (hyp IsVacAt UnrPl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lattice_vacuum_split_place_vacuum_at_prime : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → Formalism.DivisionValues.conjPl w ≠ w → ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ), VacFin ψ S T v f → IsVacAt ψ S T w f := by
  first | exact @GlobalTheory.VacSplit.isVacAt_of_vacFin | exact GlobalTheory.VacSplit.isVacAt_of_vacFin | (intros; apply GlobalTheory.VacSplit.isVacAt_of_vacFin <;> assumption)
end

