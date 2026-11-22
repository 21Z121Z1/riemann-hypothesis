import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0149
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsSpan
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0150
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardUnimodularGluingsTwoLinesLe
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0151
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0152
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeCarryIffForallPlaceStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLattice_carry_iff_forall_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L M : Submodule (𝓞 E) (Fin n → E)), IsLat L → IsLat M → ∀ y : GL (Fin n) (E ⊗[F] Ad F), (∀ x, x ∈ hat F L ↔ y.1 *ᵥ x ∈ hat F M) ↔ ∀ v : HeightOneSpectrum (𝓞 F), ∀ x, x ∈ loc v L ↔ (bc (prV (E := E) v) y).1 *ᵥ x ∈ loc v M := by
  first | exact @GlobalTheory.St.G.Carry.carry_iff | exact GlobalTheory.St.G.Carry.carry_iff | (intros; apply GlobalTheory.St.G.Carry.carry_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSpec
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

noncomputable section

namespace GlobalTheory.AdelicLattice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem incl_mem_lamAf (L : Submodule (𝓞 E) (Fin n → E)) {x : Fin n → E} (hx : x ∈ L) :
    (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ lamAf (F := F) L :=
  Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

theorem exists_approx (L : Submodule (𝓞 E) (Fin n → E)) (g : ℕ) (hg : 1 ≤ g)
    (y : Fin n → E ⊗[F] Af F) (hy : y ∈ lamAf (F := F) L) :
    ∃ x ∈ L, ∃ z ∈ lamAf (F := F) L,
      y = (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) + (g : E ⊗[F] Af F) • z := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, x.2, 0, zero_mem _, by simp⟩
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by funext i; simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, z, hz, rfl⟩ := ha
    obtain ⟨x', hx', z', hz', rfl⟩ := hb
    refine ⟨x + x', add_mem hx hx', z + z', add_mem hz hz', ?_⟩
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add]
    ring
  | smul s a _ ha =>
    obtain ⟨x, hx, z, hz, rfl⟩ := ha
    obtain ⟨r, hr, w, hw, e⟩ := Formalism.UG.P.csSpan_approx (F := F) (E := E) Formalism.UG.P.csGlob_intAdApprox
      (g : 𝓞 F) (Nat.cast_ne_zero.2 (by omega)) s.2
    rw [GlobalTheory.AutInhab.levelafC_natCast] at e
    refine ⟨(⟨r, hr⟩ : 𝓞 E) • x, L.smul_mem _ hx,
      (⟨w, hw⟩ : IntAf F E) • (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) + s • z,
      add_mem (Submodule.smul_mem _ _ (incl_mem_lamAf L hx)) (Submodule.smul_mem _ _ hz), ?_⟩
    funext i
    show (s : E ⊗[F] Af F) * (Formalism.UG.inclE (F := F) (Af F) (x i) + (g : E ⊗[F] Af F) * z i) =
      Formalism.UG.inclE (F := F) (Af F) (r * x i) + (g : E ⊗[F] Af F) *
        (w * Formalism.UG.inclE (F := F) (Af F) (x i) + (s : E ⊗[F] Af F) * z i)
    rw [map_mul]
    linear_combination Formalism.UG.inclE (F := F) (Af F) (x i) * e

theorem incl_mem_iff (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ lamAf (F := F) L ↔ x ∈ L := by
  refine ⟨fun h => ?_, incl_mem_lamAf L⟩
  rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin n) L (Module.Finite.iff_fg.2 hfg) hspan]
  show ((1⁻¹ : GL (Fin n) (E ⊗[F] Af F)) : Matrix (Fin n) (Fin n) _) *ᵥ
      (fun i => Formalism.UG.inclE (F := F) (Af F) (x i)) ∈ Formalism.UG.latS (F := F) (Af F) (IntAf F E) L
  rw [inv_one, Units.val_one, one_mulVec]
  refine Submodule.span_mono ?_ h
  rintro _ ⟨y, rfl⟩
  exact ⟨y, y.2, rfl⟩

theorem span_lamAf (L : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    Submodule.span (E ⊗[F] Af F) (lamAf (F := F) L : Set (Fin n → E ⊗[F] Af F)) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨m, hm, hy⟩ := GlobalTheory.AutInhab.lamAf_absorbs (F := F) L hspan y
  obtain ⟨u, hu⟩ := GlobalTheory.AutInhab.isUnit_natCast (F := F) (E := E) m hm
  have : y = ((u⁻¹ : (E ⊗[F] Af F)ˣ) : E ⊗[F] Af F) • ((m : E ⊗[F] Af F) • y) := by
    rw [smul_smul, ← hu, Units.inv_mul, one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hy)

theorem adelicLattice_spec : ∀ (I : AutInst) (g : ℕ), 1 ≤ g → (∀ y ∈ I.Lf, ∃ x ∈ I.L, ∃ z ∈ I.Lf, y = (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) + (g : (I.E ⊗[I.F] Af I.F)) • z) ∧ (∀ x : Fin I.n → I.E, (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) ∈ I.Lf ↔ x ∈ I.L) ∧ Submodule.span (I.E ⊗[I.F] Af I.F) (I.Lf : Set (Fin I.n → (I.E ⊗[I.F] Af I.F))) = ⊤ ∧ I.Lf.FG ∧ ∀ y : Fin I.n → (I.E ⊗[I.F] Af I.F), ∃ m : ℕ, 1 ≤ m ∧ (m : (I.E ⊗[I.F] Af I.F)) • y ∈ I.Lf :=
  fun I g hg => ⟨exists_approx I.L g hg, incl_mem_iff I.L I.L_fg I.L_span, span_lamAf I.L I.L_span,
    GlobalTheory.AutInhab.lamAf_fg I.L I.L_fg, GlobalTheory.AutInhab.lamAf_absorbs I.L I.L_span⟩

end GlobalTheory.AdelicLattice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeSizeConsequencesOfWordIndependentHypsStatement
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudeSizeConsequences_of_wordIndependentHyps : ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ), D.host.rdE ≤ large₂.sc.b → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → Sizes D large₂ Cl Cg CT := by
  first | exact @GlobalTheory.Amp.SizesProof.sizes_of_hyp | exact GlobalTheory.Amp.SizesProof.sizes_of_hyp | (intros; apply GlobalTheory.Amp.SizesProof.sizes_of_hyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AtPBijective
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.RefCov

def crd (k r j : ℕ) (β : Fin r → ℕ) (q : (UTin β → ℂ) × PTop k r j) : Mat k r :=
  pTop k r j q.2 * uEmb k r (upperIn β q.1)

abbrev Crd (ι : Type) (k r j : ℕ) (β : Fin r → ℕ) :=
  (UTin β → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → Fin (k + 1) → ℂ) ×
    (({p : UT r // j ≤ p.1.1.val} → ι → ℂ) × ({a : Fin r // j ≤ a.val} → ι → ℝ))

def atP {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} (p : Crd ι k r j β) (v : ι) : (UTin β → ℂ) × PTop k r j :=
  (fun i => p.1 i v, fun a => p.2.1 a v, fun s => p.2.2.1 s v, fun a => p.2.2.2 a v)

def CC {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} (p : Crd ι k r j β) : ι → Mat k r := fun v => crd k r j β (atP p v)

theorem usage₂ {ι : Type} {k r j : ℕ} {β : Fin r → ℕ} :
    Function.Bijective (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun q => (fun i v => (q v).1 i, fun a v => (q v).2.1 a,
    fun s v => (q v).2.2.1 s, fun a v => (q v).2.2.2 a), fun _ => rfl, fun _ => rfl⟩

end GlobalTheory.DegVol.RefCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselRootDilationNormalizesContractsUnipotent
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.Dilation

variable {k r : ℕ}

def dd (k r : ℕ) (τ : ℝ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then (τ : ℂ) ^ (r - i.val) else if i.val ≤ r + k then 1 else ((τ : ℂ) ^ (i.val - (r + k)))⁻¹

def wt (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ :=
  if i.val < r then ((r - i.val : ℕ) : ℤ) else if i.val ≤ r + k then 0 else -((i.val - (r + k) : ℕ) : ℤ)

theorem dil_eq (τ : ℝ) : dil k r τ = Matrix.diagonal (dd k r τ) := rfl

theorem dd_eq_zpow {τ : ℝ} (hτ : τ ≠ 0) (i : Fin (2 * r + k + 1)) :
    dd k r τ i = (τ : ℂ) ^ wt k r i := by
  unfold dd wt
  split_ifs
  · rw [_root_.zpow_natCast]
  · rw [_root_.zpow_zero]
  · rw [_root_.zpow_neg, _root_.zpow_natCast]

theorem dd_inv_mul {τ : ℝ} (hτ : τ ≠ 0) (i j : Fin (2 * r + k + 1)) :
    dd k r τ⁻¹ i * dd k r τ j = (τ : ℂ) ^ (wt k r j - wt k r i) := by
  have h0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  rw [dd_eq_zpow (inv_ne_zero hτ), dd_eq_zpow hτ, Complex.ofReal_inv, _root_.inv_zpow', ← _root_.zpow_add₀ h0,
    neg_add_eq_sub]

theorem dd_mul_inv {τ : ℝ} (hτ : τ ≠ 0) (i : Fin (2 * r + k + 1)) :
    dd k r τ i * dd k r τ⁻¹ i = 1 := by
  have h0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  rw [dd_eq_zpow hτ, dd_eq_zpow (inv_ne_zero hτ), Complex.ofReal_inv, _root_.inv_zpow', ← _root_.zpow_add₀ h0,
    add_neg_cancel, _root_.zpow_zero]

theorem star_dd (τ : ℝ) (i : Fin (2 * r + k + 1)) : star (dd k r τ i) = dd k r τ i := by
  unfold dd
  split_ifs <;> simp

theorem dd_pair {τ : ℝ} (hτ : τ ≠ 0) {i j : Fin (2 * r + k + 1)} (h : i.val < r ∨ j.val < r)
    (hs : i.val + j.val = 2 * r + k) : dd k r τ i * dd k r τ j = 1 := by
  have h0 : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ
  have hw : wt k r i + wt k r j = 0 := by
    have := i.isLt
    have := j.isLt
    unfold wt
    split_ifs <;> omega
  rw [dd_eq_zpow hτ, dd_eq_zpow hτ, ← _root_.zpow_add₀ h0, hw, _root_.zpow_zero]

theorem dd_middle (τ : ℝ) {i : Fin (2 * r + k + 1)} (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    dd k r τ i = 1 := by
  unfold dd
  rw [if_neg (by omega), if_pos h2]

theorem dil_entry (a b : ℝ) (m : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (dil k r a * m * dil k r b) i j = dd k r a i * m i j * dd k r b j := by
  rw [dil_eq, dil_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem dil_mul_inv {τ : ℝ} (hτ : τ ≠ 0) : dil k r τ * dil k r τ⁻¹ = 1 := by
  rw [dil_eq, dil_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact dd_mul_inv hτ i

theorem dil_inv {τ : ℝ} (hτ : τ ≠ 0) : (dil k r τ)⁻¹ = dil k r τ⁻¹ := by
  exact Matrix.inv_eq_right_inv (dil_mul_inv hτ)

theorem uh_mul {g h : Mat k r} (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) :
    g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  calc (g * h)ᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

theorem dil_mem {τ : ℝ} (hτ : τ ≠ 0) : dil k r τ ∈ UH (Hpk k r) := by
  show (dil k r τ)ᴴ * Hpk k r * dil k r τ = Hpk k r
  ext i j
  rw [dil_eq, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.star_apply, star_dd]
  by_cases h1 : (i.val < r ∨ j.val < r) ∧ i.val + j.val = 2 * r + k
  · rw [mul_right_comm, dd_pair hτ h1.1 h1.2, one_mul]
  · by_cases h2 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
    · obtain ⟨hr, hk, rfl⟩ := h2
      rw [dd_middle τ hr hk, one_mul, mul_one]
    · have h0 : Hpk k r i j = 0 := by
        simp only [Hpk]
        rw [if_neg (fun hc => h1 ⟨Or.inl hc.1, hc.2⟩), if_neg (fun hc => h1 ⟨Or.inr hc.1, hc.2⟩),
          if_neg h2]
      rw [h0, mul_zero, zero_mul]

theorem Hpk_row {i p t : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val)
    (hs : i.val + p.val = 2 * r + k) : Hpk k r p t = if t = i then 1 else 0 := by
  have hpo : ¬ (r ≤ p.val ∧ p.val ≤ r + k) := by omega
  simp only [Hpk]
  rcases eq_or_ne t i with rfl | hti
  · rw [if_pos rfl]
    rcases h with h | h
    · rw [if_neg (by omega), if_pos ⟨h, by omega⟩]
    · rw [if_pos ⟨by omega, by omega⟩]
  · have hv : t.val ≠ i.val := fun e => hti (Fin.ext e)
    rw [if_neg hti, if_neg (by omega), if_neg (by omega), if_neg (fun hc => hpo ⟨hc.1, hc.2.1⟩)]

theorem uw_col {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {p : Fin (2 * r + k + 1)} (hp : p.val < r ∨ r + k < p.val) (s : Fin (2 * r + k + 1)) :
    h s p = if s = p then 1 else 0 := by
  have hcol : ∀ q : Fin (2 * r + k + 1), h *ᵥ bvec q = bvec q → h s q = if s = q then 1 else 0 := by
    intro q hq
    have e := congrFun hq s
    simpa [bvec, Matrix.mulVec_single_one, Pi.single_apply] using e
  have hpl := p.isLt
  rcases hp with hp | hp
  · have hq : eI k r ⟨p.val, hp⟩ = p := Fin.ext rfl
    have := (hh.2.1 ⟨p.val, hp⟩).1
    rw [hq] at this
    exact hcol p this
  · have hq : esI k r ⟨2 * r + k - p.val, by omega⟩ = p := by
      apply Fin.ext
      show 2 * r + k - (2 * r + k - p.val) = p.val
      omega
    have := (hh.2.1 ⟨2 * r + k - p.val, by omega⟩).2
    rw [hq] at this
    exact hcol p this

theorem uw_zero {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {i j : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    h i j = 0 := by
  have hil := i.isLt
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  let p : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have hpv : p.val = 2 * r + k - i.val := rfl
  have hpo : p.val < r ∨ r + k < p.val := by omega
  have hip : i.val + p.val = 2 * r + k := by omega
  have hcol := uw_col hh hpo
  have hrow : ∀ t, Hpk k r p t = if t = i then 1 else 0 := fun t => Hpk_row hi hip
  have hleft : ∀ t, (hᴴ * Hpk k r) p t = Hpk k r p t := by
    intro t
    rw [Matrix.mul_apply, Finset.sum_eq_single p]
    · simp [Matrix.conjTranspose_apply, hcol]
    · intro s _ hs
      simp [Matrix.conjTranspose_apply, hcol, hs]
    · simp
  have e := congrFun (congrFun hU p) j
  rw [Matrix.mul_apply] at e
  simp only [hleft, hrow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  have hji : j ≠ i := fun hc => by subst hc; omega
  rw [if_neg hji] at e
  exact e

theorem dil_comm {z : Fin (2 * r + k + 1) → ℂ} (τ : ℝ) {h : Mat k r} (hh : h ∈ UWset k r z) :
    dil k r τ * h = h * dil k r τ := by
  ext i j
  rw [dil_eq, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [uw_col hh hj i]
    split_ifs with e
    · subst e
      rw [one_mul, mul_one]
    · rw [mul_zero, zero_mul]
  · have hj' : r ≤ j.val ∧ j.val ≤ r + k := by omega
    by_cases hi : i.val < r ∨ r + k < i.val
    · rw [uw_zero hh hi hj'.1 hj'.2, mul_zero, zero_mul]
    · rw [dd_middle τ (by omega) (by omega), dd_middle τ hj'.1 hj'.2, one_mul, mul_one]

private theorem conj_mem_lemma {τ : ℝ} (hτ : τ ≠ 0) (m : Mat k r) (i j : Fin (2 * r + k + 1))
    (h : m i j = if i = j then 1 else 0) :
    (dil k r τ * m * dil k r τ⁻¹) i j = if i = j then 1 else 0 := by
  rw [dil_entry, h]
  split_ifs with e
  · subst e
    rw [mul_one, dd_mul_inv hτ]
  · rw [mul_zero, zero_mul]

theorem conj_mem {τ : ℝ} (hτ : τ ≠ 0) {m : Mat k r} (hm : m ∈ Nset k r) :
    dil k r τ * m * dil k r τ⁻¹ ∈ Nset k r := by
  have hU : m ∈ UH (Hpk k r) := hm.1
  have hc : ∀ (a : Fin r) (i : Fin (2 * r + k + 1)), a.val ≤ i.val →
      m i (eI k r a) = if i = eI k r a then 1 else 0 := hm.2.1
  have hb : ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      m i j = if i = j then 1 else 0 := hm.2.2
  refine ⟨uh_mul (uh_mul (dil_mem hτ) hU) (dil_mem (inv_ne_zero hτ)), ?_, ?_⟩
  · intro a i hai
    exact conj_mem_lemma hτ m i _ (hc a i hai)
  · intro i j h1 h2 h3
    exact conj_mem_lemma hτ m i j (hb i j h1 h2 h3)

theorem wt_lt {i j : Fin (2 * r + k + 1)} (hij : i.val < j.val) (hn : ¬ (r ≤ i.val ∧ j.val ≤ r + k)) :
    wt k r j + 1 ≤ wt k r i := by
  unfold wt
  split_ifs <;> omega

private theorem apply_self_eq_one_of_mem_Nset {m : Mat k r} (hm : m ∈ Nset k r) (i : Fin (2 * r + k + 1)) :
    m i i = if i = i then 1 else 0 :=
  Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_upper hm i i le_rfl

theorem contract {τ : ℝ} (hτ : 1 ≤ τ) {m : Mat k r} (hm : m ∈ Nset k r) (i j : Fin (2 * r + k + 1)) :
    ‖((dil k r τ)⁻¹ * m * dil k r τ - 1) i j‖ ≤ τ⁻¹ * ‖(m - 1) i j‖ := by
  have hpos : 0 < τ := by linarith
  have hτ0 : τ ≠ 0 := hpos.ne'
  have hb : ∀ i j : Fin (2 * r + k + 1), r ≤ j.val → j.val ≤ r + k → r ≤ i.val →
      m i j = if i = j then 1 else 0 := hm.2.2
  rw [dil_inv hτ0, Matrix.sub_apply, Matrix.sub_apply, dil_entry, Matrix.one_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hij' : i.val < j.val := hij
    rw [if_neg hij.ne, sub_zero, sub_zero]
    by_cases hmid : r ≤ i.val ∧ j.val ≤ r + k
    · have h0 : m i j = 0 := by
        have e := hb i j (by omega) hmid.2 hmid.1
        rwa [if_neg hij.ne] at e
      rw [h0]
      simp
    · have hw := wt_lt (k := k) (r := r) hij' hmid
      rw [mul_right_comm, dd_inv_mul hτ0, norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [norm_zpow, Complex.norm_real, Real.norm_of_nonneg hpos.le, ← _root_.zpow_neg_one]
      exact _root_.zpow_le_zpow_right₀ hτ (by omega)
  · have h1 : m i i = 1 := by simpa using apply_self_eq_one_of_mem_Nset hm i
    rw [h1, if_pos rfl, mul_one, dd_inv_mul hτ0, sub_self, _root_.zpow_zero]
    simp
  · have h0 : m i j = 0 := by
      have e := Formalism.FourierDecayAlt.P.UnipotentUpperFacts.N_upper hm i j hij.le
      rwa [if_neg hij.ne'] at e
    rw [if_neg hij.ne', h0]
    simp

theorem main : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), inWb k r z → (∀ τ : ℝ, 0 < τ → dil k r τ ∈ GG k r ∧ (∀ h ∈ UWset k r z, dil k r τ * h = h * dil k r τ) ∧ (∀ m ∈ Nset k r, dil k r τ * m * (dil k r τ)⁻¹ ∈ Nset k r ∧ (dil k r τ)⁻¹ * m * dil k r τ ∈ Nset k r)) ∧ (∀ τ : ℝ, 1 ≤ τ → ∀ m ∈ Nset k r, ∀ i j, ‖((dil k r τ)⁻¹ * m * dil k r τ - 1) i j‖ ≤ τ⁻¹ * ‖(m - 1) i j‖) := by
  intro k r z _
  refine ⟨fun τ hτ => ⟨dil_mem hτ.ne', fun h hh => dil_comm τ hh, fun m hm => ⟨?_, ?_⟩⟩,
    fun τ hτ m hm i j => contract hτ hm i j⟩
  · rw [dil_inv hτ.ne']
    exact conj_mem hτ.ne' hm
  · have e := conj_mem (inv_ne_zero hτ.ne') hm
    rwa [inv_inv, ← dil_inv hτ.ne'] at e

end GlobalTheory.SgInf.Dilation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellExponentialChartStrictDifferentiableSummaStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCellExponentialChart_strictDifferentiable_summary : ∀ (k r : ℕ), chart k r 0 = 1 ∧ ContinuousOn (chart k r) (Metric.ball 0 1) ∧ ∀ i j, ∃ D : EE k r →L[ℝ] ℂ, HasStrictFDerivAt (fun v => chart k r v i j) D 0 ∧ ∀ v, D v = dchart k r v i j := by
  first | exact @GlobalTheory.CellDens.Deriv.chart_strict | exact GlobalTheory.CellDens.Deriv.chart_strict | (intros; apply GlobalTheory.CellDens.Deriv.chart_strict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFiltrationSizePropertiesStatement
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalLatticeFiltration_size_properties : ∀ (I : AutInst) (x : I.GA) (t : ℝ), 0 < t → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLe I x t) ∧ IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (stepLt I x t) ∧ stepLt I x t ≤ stepLe I x t ∧ (∀ t', t < t' → stepLe I x t ≤ stepLt I x t') ∧ (stepLe I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLe I x t) ≤ t) ∧ (stepLt I x t ≠ ⊥ → largestSize (bas I) (frm I x) (stepLt I x t) < t) ∧ (∀ N, stepLe I x t < N → N ≤ lamX I x → t < sizeQ (bas I) (frm I x) N (stepLe I x t)) ∧ (∀ N, stepLt I x t < N → N ≤ lamX I x → t ≤ sizeQ (bas I) (frm I x) N (stepLt I x t)) ∧ (1 ≤ I.n → 0 < least I x ∧ (stepLe I x t = ⊥ ↔ t < least I x) ∧ (stepLt I x t = ⊥ ↔ t ≤ least I x)) := by
  first | exact @GlobalTheory.CountSteps.steps | exact GlobalTheory.CountSteps.steps | (intros; apply GlobalTheory.CountSteps.steps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardUnimodularGluingsTwoLinesLeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_unimodular_gluings_two_lines_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (β₁ β₂ : E) (N₁ N₂ : Submodule (𝓞 E) E) (𝔫 : Ideal (𝓞 E)), star β₁ = β₁ → star β₂ = β₂ → β₁ ≠ 0 → β₂ ≠ 0 → Submodule.IsLattice E N₁ → Submodule.IsLattice E N₂ → Submodule.span (𝓞 E) {t | ∃ x ∈ N₁, ∃ y ∈ N₁, t = star x * β₁ * y} = Submodule.map (Algebra.linearMap (𝓞 E) E) 𝔫 → ENat.card {M : Submodule (𝓞 E) (Fin 2 → E) // Submodule.IsLattice E M ∧ (∀ x, x ∈ M ↔ ∀ y ∈ M, star y ⬝ᵥ ((Matrix.diagonal ![β₁, β₂]) *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) ∧ (∀ t, t ∈ N₁ ↔ ![t, 0] ∈ M) ∧ ∀ t, t ∈ N₂ ↔ ![0, t] ∈ M} ≤ (Ideal.absNorm 𝔫 : ENat) := by
  first | exact @GlobalTheory.GlueLines.card_gluings_le | exact GlobalTheory.GlueLines.card_gluings_le | (intros; apply GlobalTheory.GlueLines.card_gluings_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellRep
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ENNReal

namespace GlobalTheory.CellRep

lemma det_upUni {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ Formalism.FourierDecayAlt.C2.UTset m) : u.det = 1 := by
  have hb : u.BlockTriangular id := fun i j h => hu.1 i j h
  rw [Matrix.det_of_upperTriangular hb]
  simp [hu.2]

theorem cell_rep : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : MatKR k r) (p : Point ℂ (r + 1)), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → γ ∈ UH (Hpk k r) → IsInCell (ZhatO k r z z' γ) p → ∃ n ∈ Nset k r, ∃ n' ∈ Nset k r, ∃ g₀ ∈ UH (Hpk k r), γ = n * g₀ * n' ∧ ZhatO k r z z' g₀ = ptMat p := by
  intro k r z z' γ p hz hz' hT hT' hγ ⟨L, U, hL, hU, hZ⟩
  set d : Fin (r + 1) → ℂ := fun b => (-1 : ℂ) ^ (r - b.val) with hd
  have hdd : ∀ b, d b * d b = 1 := fun b => by
    simp only [hd]; rw [← mul_pow]; simp
  set D : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal d with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal]; simp [hdd]
  have hO : ∀ g, ZhatO k r z z' g = Zhat k r z z' g * D := fun g => by
    ext a b
    rw [hD, Matrix.mul_diagonal, mul_comm]; rfl
  have hLU : Lᴴ ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1) :=
    ⟨fun i j h => by simp [Matrix.conjTranspose_apply, (hL j i).1 h],
     fun i => by simp [Matrix.conjTranspose_apply, (hL i i).2 rfl]⟩
  have hUU : U ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1) := ⟨fun i j h => (hU i j).1 h, fun i => (hU i i).2 rfl⟩
  have hU' : D * U * D ∈ Formalism.FourierDecayAlt.C2.UTset (r + 1) :=
    ⟨fun i j h => by simp [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, (hU i j).1 h],
     fun i => by simp [hD, Matrix.mul_diagonal, Matrix.diagonal_mul, (hU i i).2 rfl, hdd]⟩
  obtain ⟨ha, -, hau⟩ := Formalism.FourierDecayAlt.P.c2_tau_mem k r z ⟨hz, hT⟩ _ hLU
  obtain ⟨hb, -, hbu⟩ := Formalism.FourierDecayAlt.P.c2_tau_mem k r z' ⟨hz', hT'⟩ _ hU'
  set a := Formalism.FourierDecayAlt.C2.tauM k r z Lᴴ
  set b := Formalism.FourierDecayAlt.C2.tauM k r z' (D * U * D)
  have hS : ∀ (w : Fin (2 * r + k + 1) → ℂ) (n : MatKR k r), n ∈ Nset k r → n ∈ Sset k r w :=
    fun w n hn => ⟨1, ⟨WeylGroupFacts.uh_one, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩,
      Matrix.one_mulVec _⟩, n, hn, (Matrix.one_mul n).symm⟩
  have hai := WeylGroupFacts.mem_n_inv ha
  have hbi := WeylGroupFacts.mem_n_inv hb
  have hau' : IsUnit a.det := WeylGroupFacts.isUnit_of_uh ha.1
  have hbu' : IsUnit b.det := WeylGroupFacts.isUnit_of_uh hb.1
  have hg : a * γ * b⁻¹ ∈ UH (Hpk k r) := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul ha.1 hγ) hbi.1
  have he : γ = a⁻¹ * (a * γ * b⁻¹) * b := by
    rw [Matrix.mul_assoc a, Matrix.nonsing_inv_mul_cancel_left _ _ hau',
      Matrix.nonsing_inv_mul_cancel_right _ _ hbu']
  refine ⟨a⁻¹, hai, b, hb, a * γ * b⁻¹, hg, he, ?_⟩
  have hE := Formalism.FourierDecayAlt.P.zhat_equivalence k r z z' ⟨hz, hT⟩ ⟨hz', hT'⟩ a (hS z a ha) b (hS z' b hb)
    (a * γ * b⁻¹)
  rw [← he, hau, hbu, Matrix.conjTranspose_conjTranspose] at hE
  have h1 : L * ZhatO k r z z' (a * γ * b⁻¹) * U = L * ptMat p * U := by
    rw [← hZ, hO, hO γ, hE]
    simp only [Matrix.mul_assoc, hDD, Matrix.mul_one]
  have hLu : IsUnit L.det := by
    have := det_upUni hLU
    rw [Matrix.det_conjTranspose] at this
    have h2 : L.det = 1 := by simpa using congrArg star this
    rw [h2]; exact isUnit_one
  have hUu : IsUnit U.det := by rw [det_upUni hUU]; exact isUnit_one
  have h2 := congrArg (fun X => L⁻¹ * (X * U⁻¹)) h1
  simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hUu, Matrix.nonsing_inv_mul_cancel_left _ _ hLu] using h2

end GlobalTheory.CellRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoeffEqZeroOfLipschitzUnitaryFlowDecayStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_eq_zero_of_lipschitz_unitary_flow_decay : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (I : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (U : ℝ → V →ₗ[ℂ] V) (C : ℝ) (v : V), (∀ x, 0 ≤ I x x) → U 0 = LinearMap.id → (∀ s t, U (s + t) = (U s).comp (U t)) → (∀ s x y, I (U s x) (U s y) = I x y) → (∀ s x, |s| ≤ 1 → (I (U s x - x) (U s x - x)).re ≤ C * s ^ 2 * (I x x).re) → (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖I v (U s v)‖ ≤ A * Real.exp (-(e * |s|))) → I v v = 0 := by
  first | exact @GlobalTheory.LipFlow.coeff_eq_zero | exact GlobalTheory.LipFlow.coeff_eq_zero | (intros; apply GlobalTheory.LipFlow.coeff_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompleteIsotropicFrameSignatureEigenvectorsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_isotropicFrame_signature_eigenvectors : ∀ (n : ℕ) (ε : Fin n → Bool) (p q : ℕ), (univ.filter fun a => ε a = true).card = p → (univ.filter fun a => ε a = false).card = q → ∀ (a : ℕ) (j : Fin a → ℕ) (T : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ), (∀ i, (T i)ᴴ * T i = 1) → (∀ i k, i ≠ k → (T i)ᴴ * T k = 0) → (∀ i k, (T i)ᴴ * Formalism.REAL.Jm ε * T k = 0) → ∃ (P : Matrix (Fin n) (Fin (p - ∑ i, j i)) ℂ) (Q : Matrix (Fin n) (Fin (q - ∑ i, j i)) ℂ), (∀ i, (T i)ᴴ * P = 0) ∧ (∀ i, (T i)ᴴ * Q = 0) ∧ Pᴴ * P = 1 ∧ Qᴴ * Q = 1 ∧ Formalism.REAL.Jm ε * P = P ∧ Formalism.REAL.Jm ε * Q = -Q ∧ (∑ i, (T i * (T i)ᴴ + Formalism.REAL.Jm ε * T i * (T i)ᴴ * Formalism.REAL.Jm ε)) + P * Pᴴ + Q * Qᴴ = 1 := by
  first | exact @GlobalTheory.IsoFrame.complete_isotropic_frame | exact GlobalTheory.IsoFrame.complete_isotropic_frame | (intros; apply GlobalTheory.IsoFrame.complete_isotropic_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CompletedTensorDiscreteSeriesIrreducibleFormalDeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedTensorDiscreteSeries_irreducible_formalDegree : TensorRep := by
  first | exact @GlobalTheory.Dec.tensorRep | exact GlobalTheory.Dec.tensorRep | (intros; apply GlobalTheory.Dec.tensorRep <;> assumption)
end

