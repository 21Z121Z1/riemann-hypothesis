import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import GroundTheory.AutomorphicForms.JacquetAdmissible
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0013

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.SmGLBridge

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]

def glReindex {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) :
    GL a k ≃* GL b k :=
  Units.mapEquiv (Matrix.reindexAlgEquiv k k e).toMulEquiv

theorem continuous_glReindex {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) : Continuous (glReindex (k := k) e) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · show Continuous fun g : GL a k => Matrix.reindex e e (g : Matrix a a k)
    exact Units.continuous_val.matrix_reindex e e
  · show Continuous fun g : GL a k => Matrix.reindex e e ((g⁻¹ : GL a k) : Matrix a a k)
    exact Units.continuous_coe_inv.matrix_reindex e e

theorem glReindex_symm {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (e : a ≃ b) (g : GL b k) : (glReindex (k := k) e).symm g = glReindex e.symm g := by
  apply Units.ext
  ext i j
  rfl

end GlobalTheory.CompanionTheory.SmGLBridge

namespace GlobalTheory.CompanionTheory.SmGLBridge

theorem irreducibleAdmissible :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GlobalTheory.SmGL.IrreducibleAdmissible k := by
  intro k _ _ _ _ n _ _ V _ _ π hsm hirr
  let e : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
  let ψ : GL (Fin (Fintype.card n)) k ≃* GL n k := glReindex e
  have hψ : Continuous ψ := continuous_glReindex e
  have hψs : Continuous ψ.symm :=
    (continuous_glReindex (k := k) e.symm).congr (fun g => (glReindex_symm e g).symm)
  let π' : Representation ℂ (GL (Fin (Fintype.card n)) k) V := π.comp ψ.toMonoidHom
  have hsm' : GroundTheory.Automorphic.IsSmooth π' := by
    intro v
    have hs : (↑(GroundTheory.Automorphic.stabilizerOf π' v) : Set (GL (Fin (Fintype.card n)) k)) =
        ψ ⁻¹' {g | π g v = v} := by
      ext g
      simp only [SetLike.mem_coe, GroundTheory.Automorphic.mem_stabilizerOf, Set.mem_preimage, Set.mem_setOf_eq]
      exact Iff.rfl
    rw [hs]
    exact (hsm v).preimage hψ
  haveI : IsSimpleOrder (Subrepresentation π) := hirr
  let f : Subrepresentation π' ≃o Subrepresentation π :=
    { toFun := fun W => ⟨W.toSubmodule, fun g v hv => by
          have h := W.apply_mem_toSubmodule (ψ.symm g) hv
          simpa [π'] using h⟩
      invFun := fun W => ⟨W.toSubmodule, fun g v hv => W.apply_mem_toSubmodule (ψ g) hv⟩
      left_inv := fun W => rfl
      right_inv := fun W => rfl
      map_rel_iff' := Iff.rfl }
  haveI : π'.IsIrreducible := f.isSimpleOrder
  have had := GroundTheory.Automorphic.Parabolic.isAdmissible_of_isIrreducible hsm'
  refine ⟨hsm, fun K hKo hKc => ?_⟩
  let K' : Subgroup (GL (Fin (Fintype.card n)) k) := K.comap ψ.toMonoidHom
  let Hm : GL (Fin (Fintype.card n)) k ≃ₜ GL n k :=
    { toEquiv := ψ.toEquiv, continuous_toFun := hψ, continuous_invFun := hψs }
  have hK'o : IsOpen (K' : Set (GL (Fin (Fintype.card n)) k)) := hKo.preimage hψ
  have hK'c : IsCompact (K' : Set (GL (Fin (Fintype.card n)) k)) := Hm.isCompact_preimage.mpr hKc
  have hfd := had.2 K' hK'c hK'o
  have heq : GlobalTheory.PRep.fixed π K = GroundTheory.Automorphic.fixedVectors π' K' := by
    ext v
    rw [GroundTheory.Automorphic.mem_fixedVectors]
    show (∀ h : ↥K, π (h : GL n k) v = ((1 : ↥K →* ℂˣ) h : ℂ) • v) ↔ _
    constructor
    · intro hv g hg
      have h1 := hv ⟨ψ g, hg⟩
      simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1
      exact h1
    · intro hv h
      have h1 := hv (ψ.symm h) (by simpa [K'] using h.2)
      simp only [MonoidHom.one_apply, Units.val_one, one_smul]
      simpa [π'] using h1
  rw [heq]
  exact hfd

end GlobalTheory.CompanionTheory.SmGLBridge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsClosedCartierLocusSupportStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_cartier_locus_support : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData), Smooth g → IsIntegral X → Smooth (Z.subschemeι ≫ g) → IsClosed {x : X | x ∈ Z.support ∧ CartAt Z x} ∧ IsClosed {x : X | x ∈ Z.support ∧ ¬ CartAt Z x} := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.isClosed_cartAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasureInvertibleIntegralMatrices
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.QL.VolK

theorem card_scaled (q r : ℕ) (hq : 0 < q) :
    (((∏ i : Fin r, (q ^ r - q ^ (i : ℕ)) : ℕ)) : ℝ) * (q : ℝ) ^ (-((r * r : ℕ) : ℤ)) = qE q 1 r := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hq1 : 1 ≤ q := hq
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ r - q ^ i) r, Nat.cast_prod]
  have h1 : ∀ i ∈ Finset.range r, (((q ^ r - q ^ i : ℕ)) : ℝ)
      = (q : ℝ) ^ r * (1 - (q : ℝ) ^ (-(((r - i : ℕ)) : ℤ))) := by
    intro i hi
    have hi' : i ≤ r := (Finset.mem_range.1 hi).le
    rw [Nat.cast_sub (Nat.pow_le_pow_right hq1 hi'), mul_sub, mul_one]
    push_cast
    congr 1
    rw [← zpow_natCast (q : ℝ) r, ← zpow_add₀ hq0, ← zpow_natCast (q : ℝ) i]
    congr 1
    push_cast [Nat.cast_sub hi']
    ring
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have h2 : ((q : ℝ) ^ r) ^ r * (q : ℝ) ^ (-((r * r : ℕ) : ℤ)) = 1 := by
    rw [← pow_mul, ← zpow_natCast (q : ℝ) (r * r), ← zpow_add₀ hq0]
    simp
  have h3 : ∏ i ∈ Finset.range r, (1 - (q : ℝ) ^ (-(((r - i : ℕ)) : ℤ))) = qE q 1 r := by
    unfold qE
    refine Finset.prod_nbij' (fun i => r - i) (fun s => r - s) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      have := Finset.mem_range.1 hi
      simp only [Finset.mem_Icc]; omega
    · intro s hs
      have := Finset.mem_Icc.1 hs
      simp only [Finset.mem_range]; omega
    · intro i hi
      have := Finset.mem_range.1 hi
      show r - (r - i) = i
      omega
    · intro s hs
      have := Finset.mem_Icc.1 hs
      show r - (r - s) = s
      omega
    · intro i _
      rfl
  rw [h3]
  calc _ = (((q : ℝ) ^ r) ^ r * (q : ℝ) ^ (-((r * r : ℕ) : ℤ))) * qE q 1 r := by ring
    _ = _ := by rw [h2, one_mul]

section

variable {F : Type} [Field F] [ValuativeRel F]

def red (x : F) : 𝓀[F] :=
  open Classical in if h : x ∈ 𝒪[F] then IsLocalRing.residue 𝒪[F] ⟨x, h⟩ else 0

theorem red_of_mem {x : F} (h : x ∈ 𝒪[F]) : red x = IsLocalRing.residue 𝒪[F] ⟨x, h⟩ := by
  simp [red, h]

def redM {r : ℕ} (x : Matrix (Fin r) (Fin r) F) : Matrix (Fin r) (Fin r) 𝓀[F] := x.map red

def toO {r : ℕ} {x : Matrix (Fin r) (Fin r) F} (h : x ∈ intMat 𝒪[F] r r) :
    Matrix (Fin r) (Fin r) 𝒪[F] := fun i j => ⟨x i j, h i j⟩

theorem redM_eq_map {r : ℕ} {x : Matrix (Fin r) (Fin r) F} (h : x ∈ intMat 𝒪[F] r r) :
    redM x = (IsLocalRing.residue 𝒪[F]).mapMatrix (toO h) := by
  ext i j
  simp [redM, toO, red_of_mem (h i j)]

theorem map_toO {r : ℕ} {x : Matrix (Fin r) (Fin r) F} (h : x ∈ intMat 𝒪[F] r r) :
    (𝒪[F].subtype).mapMatrix (toO h) = x := by
  ext i j
  simp [toO]

theorem red_eq_iff {ϖ : F} (hlt : ∀ x : F, ValuativeRel.valuation F x < 1 ↔ ∃ o ∈ 𝒪[F], x = ϖ * o)
    {x y : F} (hx : x ∈ 𝒪[F]) (hy : y ∈ 𝒪[F]) : red x = red y ↔ ∃ o ∈ 𝒪[F], x - y = ϖ * o := by
  rw [← hlt, red_of_mem hx, red_of_mem hy, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one (v := ValuativeRel.valuation F)]
  rfl

theorem redM_eq_iff {r : ℕ} {ϖ : F}
    (hlt : ∀ x : F, ValuativeRel.valuation F x < 1 ↔ ∃ o ∈ 𝒪[F], x = ϖ * o)
    {x y : Matrix (Fin r) (Fin r) F} (hx : x ∈ intMat 𝒪[F] r r) (hy : y ∈ intMat 𝒪[F] r r) :
    redM x = redM y ↔ x - y ∈ (IIset 𝒪[F] ϖ : Set (Matrix (Fin r) (Fin r) F)) := by
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    exact (red_eq_iff hlt (hx i j) (hy i j)).1 this
  · intro h
    ext i j
    exact (red_eq_iff hlt (hx i j) (hy i j)).2 (h i j)

theorem mem_Jset_iff {r : ℕ} {x : Matrix (Fin r) (Fin r) F} (h : x ∈ intMat 𝒪[F] r r) :
    x ∈ Jset (GLint 𝒪[F] r) ↔ IsUnit (redM x).det := by
  have hdet : (redM x).det = IsLocalRing.residue 𝒪[F] (toO h).det := by
    rw [redM_eq_map h, RingHom.map_det]
  rw [hdet, isUnit_map_iff]
  constructor
  · rintro ⟨g, ⟨-, hg'⟩, hgx⟩
    have hgx' : (g : Matrix (Fin r) (Fin r) F) = x := hgx
    have hg'' : ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) ∈ intMat 𝒪[F] r r := hg'
    have hmul : toO h * toO hg'' = 1 := by
      have h1 : (𝒪[F].subtype).mapMatrix (toO h * toO hg'') = (𝒪[F].subtype).mapMatrix 1 := by
        rw [map_mul, map_toO, map_toO, map_one, ← hgx']
        exact Units.mul_inv g
      exact Matrix.map_injective (f := 𝒪[F].subtype) Subtype.val_injective h1
    exact Matrix.isUnit_det_of_right_inverse hmul
  · intro hu
    obtain ⟨u, hu'⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hu
    let φ : Matrix (Fin r) (Fin r) 𝒪[F] →* Matrix (Fin r) (Fin r) F :=
      RingHom.toMonoidHom (𝒪[F].subtype).mapMatrix
    have hval : φ (u : Matrix (Fin r) (Fin r) 𝒪[F]) = x := by
      rw [hu']
      exact map_toO h
    refine ⟨Units.map φ u, ⟨?_, ?_⟩, hval⟩
    · intro i j
      have : ((Units.map φ u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = x := hval
      rw [this]
      exact h i j
    · intro i j
      exact (((u⁻¹ : GL (Fin r) 𝒪[F]) : Matrix (Fin r) (Fin r) 𝒪[F]) i j).2

end

theorem vol_GLint : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ r : ℕ, ∀ (dx : Measure (Matrix (Fin r) (Fin r) F)), dx.IsAddLeftInvariant → dx (intMat O r r) = 1 → MeasurableSet (Jset (GLint O r)) ∧ dx (Jset (GLint O r)) = ENNReal.ofReal (qE q 1 r) := by
  intro F _ _ _ _ _ _ O ϖ nrm q h r dx hinv hone
  obtain ⟨hBor, hIopen, -, -, -, -⟩ := GlobalTheory.T.matrix_additive_haar_normalized h r r
  have hP := GlobalTheory.T.measure_uniformizer_multiple_matrices h r r dx hinv hone
  have hlt := h.lt_one
  have hcard := h.card
  have hne := h.ne
  have hO := h.O_eq
  subst hO
  haveI := hBor
  have hϖ : ϖ ∈ 𝒪[F] := by
    have : ValuativeRel.valuation F ϖ < 1 := (hlt ϖ).2 ⟨1, one_mem _, by simp⟩
    exact this.le
  have hPI : ∀ {x : Matrix (Fin r) (Fin r) F}, x ∈ (IIset 𝒪[F] ϖ : Set (Matrix (Fin r) (Fin r) F)) →
      x ∈ intMat 𝒪[F] r r := by
    intro x hx i j
    obtain ⟨o, ho, e⟩ := hx i j
    rw [e]
    exact mul_mem hϖ ho
  have hPopen : IsOpen (IIset 𝒪[F] ϖ : Set (Matrix (Fin r) (Fin r) F)) := by
    have e : (IIset 𝒪[F] ϖ : Set (Matrix (Fin r) (Fin r) F))
        = (fun x : Matrix (Fin r) (Fin r) F => ϖ⁻¹ • x) ⁻¹' intMat 𝒪[F] r r := by
      ext x
      constructor
      · intro hx i j
        obtain ⟨o, ho, e⟩ := hx i j
        simpa [e, hne] using ho
      · intro hx i j
        refine ⟨_, hx i j, ?_⟩
        simp [hne]
    rw [e]
    exact hIopen.preimage (continuous_const_smul _)
  have hlift : ∀ g : GL (Fin r) 𝓀[F], ∃ L ∈ intMat 𝒪[F] r r,
      redM L = (g : Matrix (Fin r) (Fin r) 𝓀[F]) := by
    intro g
    choose a ha using fun i j => IsLocalRing.residue_surjective
      ((g : Matrix (Fin r) (Fin r) 𝓀[F]) i j)
    refine ⟨fun i j => (a i j : F), fun i j => (a i j).2, ?_⟩
    ext i j
    show red (a i j : F) = _
    rw [red_of_mem (a i j).2]
    exact ha i j
  choose L hLI hLr using hlift
  have hfib : ∀ (g : GL (Fin r) 𝓀[F]) (x : Matrix (Fin r) (Fin r) F),
      x ∈ (fun x => -L g + x) ⁻¹' (IIset 𝒪[F] ϖ : Set (Matrix (Fin r) (Fin r) F)) →
      x ∈ intMat 𝒪[F] r r ∧ redM x = (g : Matrix (Fin r) (Fin r) 𝓀[F]) := by
    intro g x hx
    have hx' : x - L g ∈ (IIset 𝒪[F] ϖ : Set (Matrix (Fin r) (Fin r) F)) := by
      have : -L g + x = x - L g := neg_add_eq_sub _ _
      simpa [this] using hx
    have hxI : x ∈ intMat 𝒪[F] r r := fun i j => by
      have h1 := add_mem (hPI hx' i j) (hLI g i j)
      simpa using h1
    exact ⟨hxI, ((redM_eq_iff hlt hxI (hLI g)).2 hx').trans (hLr g)⟩
  have hJ : Jset (GLint 𝒪[F] r)
      = ⋃ g : GL (Fin r) 𝓀[F], (fun x => -L g + x) ⁻¹' (IIset 𝒪[F] ϖ : Set (Matrix (Fin r) (Fin r) F)) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      have hxI : x ∈ intMat 𝒪[F] r r := by
        obtain ⟨g, hg, rfl⟩ := hx
        exact hg.1
      obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).2 ((mem_Jset_iff hxI).1 hx)
      refine ⟨g, ?_⟩
      have h1 : redM x = redM (L g) := by rw [hLr, hg]
      have h2 := (redM_eq_iff hlt hxI (hLI g)).1 h1
      have : -L g + x = x - L g := neg_add_eq_sub _ _
      simpa [this] using h2
    · rintro ⟨g, hg⟩
      obtain ⟨hxI, hx⟩ := hfib g x hg
      rw [mem_Jset_iff hxI, hx]
      exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  have hcont : ∀ g : GL (Fin r) 𝓀[F], Continuous fun x : Matrix (Fin r) (Fin r) F => -L g + x :=
    fun g => continuous_const.add continuous_id
  have hmeas : ∀ g : GL (Fin r) 𝓀[F], MeasurableSet
      ((fun x => -L g + x) ⁻¹' (IIset 𝒪[F] ϖ : Set (Matrix (Fin r) (Fin r) F))) :=
    fun g => (hPopen.preimage (hcont g)).measurableSet
  refine ⟨hJ ▸ MeasurableSet.iUnion hmeas, ?_⟩
  letI : Fintype 𝓀[F] := Fintype.ofFinite _
  letI : Fintype (GL (Fin r) 𝓀[F]) := Fintype.ofFinite _
  have hdisj : Pairwise (Function.onFun Disjoint fun g : GL (Fin r) 𝓀[F] =>
      (fun x => -L g + x) ⁻¹' (IIset 𝒪[F] ϖ : Set (Matrix (Fin r) (Fin r) F))) := by
    intro g g' hgg
    refine Set.disjoint_left.2 fun x hx hx' => hgg (Units.ext ?_)
    exact (hfib g x hx).2.symm.trans (hfib g' x hx').2
  have hq : 0 < q := by
    rw [hcard]
    exact Nat.card_pos
  have hGL : Fintype.card (GL (Fin r) 𝓀[F]) = ∏ i : Fin r, (q ^ r - q ^ (i : ℕ)) := by
    rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field, hcard, Nat.card_eq_fintype_card]
  rw [hJ, measure_iUnion hdisj hmeas, tsum_fintype]
  have hg : ∀ g : GL (Fin r) 𝓀[F], dx ((fun x => -L g + x) ⁻¹' (IIset 𝒪[F] ϖ : Set (Matrix (Fin r) (Fin r) F)))
      = ENNReal.ofReal ((q : ℝ) ^ (-((r * r : ℕ) : ℤ))) := fun g => by
    rw [measure_preimage_add dx (-L g), hP]
  simp only [hg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← card_scaled q r hq, ← hGL, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

end GlobalTheory.CompanionTheory.QL.VolK
end
end

