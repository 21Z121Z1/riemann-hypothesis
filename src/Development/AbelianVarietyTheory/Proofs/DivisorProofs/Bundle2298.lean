import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsAtSmallPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2249
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymplecticFormBasisChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsAtSmallPlaceStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reads_at_small_place : InRange fun _ _ _ _ p j P W w => SmallAt p j P w → ReadsAt p j P W w := by
  first | exact @GlobalTheory.FrameRead.reads_of_small | exact GlobalTheory.FrameRead.reads_of_small | (intros; apply GlobalTheory.FrameRead.reads_of_small <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionEqBasePointStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_eq_basePoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (x : Sp R ⟶ X) (g₀ : Sp S ⟶ t.G.left) (v : Sp (DualNumber R) ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ x → IsTanAtG t x v → IsTranslate t φ g₀ v w → spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w = g₀ := by
  first | exact @GlobalTheory.LogKS.IsTranslate.fst_comp | exact GlobalTheory.LogKS.IsTranslate.fst_comp | (intros; apply GlobalTheory.LogKS.IsTranslate.fst_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePullOfIsFinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.RootDiagAmple

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem relAmple_pull_of_isFinite {A G : Over S} [IsProper A.hom] (χ : A ⟶ G) [IsFinite χ.left]
    {D : LB G.left} (hD : D.IsLB) (h : Out.RelAmple G D) : Out.RelAmple A (D.pull χ.left) := by
  refine relAmple_of_isAmpleLB A (pull_isLB hD _) fun V hV => ?_
  have le : A.hom ⁻¹ᵁ V ≤ χ.left ⁻¹ᵁ (G.hom ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, Over.w]
  have le' : χ.left ⁻¹ᵁ (G.hom ⁻¹ᵁ V) ≤ A.hom ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, Over.w]
  have e : A.hom ⁻¹ᵁ V = χ.left ⁻¹ᵁ (G.hom ⁻¹ᵁ V) := le_antisymm le le'
  rw [e]
  have h₁ := (isAmpleLB_of_relAmple G hD h V hV).pull_of_isFinite (χ.left ∣_ (G.hom ⁻¹ᵁ V))
  refine (isAmpleLB_congr (pull_isLB (pull_isLB hD _) _) (pull_isLB (pull_isLB hD _) _) ?_).1 h₁
  refine (cls_eq_iff (pull_isLB (pull_isLB hD _) _) (pull_isLB (pull_isLB hD _) _)).1 ?_
  rw [cls_pull (pull_isLB hD _), cls_pull (pull_isLB hD _), cls_pull hD, cls_pull hD, ← pull_comp, ← pull_comp,
    morphismRestrict_ι]

theorem relAmple_of_relAmple_pow {A : Over S} [IsProper A.hom] {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) (h : Out.RelAmple A M) : Out.RelAmple A L := by
  rw [relAmple_iff_isAmpleLB A hM] at h
  refine relAmple_of_isAmpleLB A hL fun U hU => (isAmpleLB_pow_iff (pull_isLB hL _) hd).1 ?_
  refine (isAmpleLB_congr (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)
    ((cls_eq_iff (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)).1 ?_)).2 (h U hU)
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

end GlobalTheory.RootDiagAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarLeOneOfDimZero
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SUVol.Degenerate

theorem realSU_subsingleton {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (h : Ψ.card = 0 ∨ r = 1) :
    Subsingleton (realSU Ψ G) := by
  refine ⟨fun g g' => ?_⟩
  have key : ∀ g : realSU Ψ G, g = 1 := by
    intro g
    apply Subtype.ext
    funext τ
    rcases h with h | h
    · exact absurd (Finset.card_pos.2 ⟨τ.1, τ.2⟩) (by omega)
    · subst h
      apply Units.ext
      have hd := (g.2 τ).1
      rw [Matrix.det_unique] at hd
      ext a b
      rw [Subsingleton.elim a default, Subsingleton.elim b default]
      simpa using hd
  rw [key g, key g']

theorem realLie_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (h : Ψ.card = 0 ∨ r = 1)
    (X : Ψ → Fin r → Fin r → ℂ) (hX : X ∈ realLie Ψ G) : X = 0 := by
  funext τ
  rcases h with h | h
  · exact absurd (Finset.card_pos.2 ⟨τ.1, τ.2⟩) (by omega)
  · subst h
    have ht := (hX τ).1
    rw [Matrix.trace_fin_one] at ht
    funext a b
    rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
    simpa using ht

theorem fromFrame_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (hdet : ∀ τ, (mat x τ).det ≠ 0)
    (Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (hY : fromFrame x Y = 0) : Y = 0 := by
  ext ⟨τ, a, b⟩
  have h1 := congrFun hY τ
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.2 (hdet τ)
  have h2 : Matrix.of (fun a b => Y (τ, a, b)) = 0 := by
    have e : (mat x τ)⁻¹ * (mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹) * mat x τ =
        Matrix.of (fun a b => Y (τ, a, b)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
        Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    rw [← e]
    have h1' : (mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = 0 := h1
    rw [h1', Matrix.mul_zero, Matrix.zero_mul]
  have := congrFun (congrFun h2 a) b
  simpa using this

end GlobalTheory.SUVol.Degenerate

open GlobalTheory.SUVol.Degenerate in

theorem GlobalTheory.SUVol.Degenerate.riemHaar_le_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → (∀ τ, (mat x τ).det ≠ 0) → Ψ.card * (r ^ 2 - 1) = 0 → ∀ S : Set (realSU Ψ G), riemHaar Ψ G x S ≤ 1 := by
  intro E _ _ _ r Ψ G x hr hdet hc S
  have h : Ψ.card = 0 ∨ r = 1 := by
    rcases Nat.mul_eq_zero.1 hc with h | h
    · exact Or.inl h
    · right
      have : r ^ 2 ≤ 1 := by omega
      nlinarith
  haveI := realSU_subsingleton Ψ G h
  haveI : CompactSpace (realSU Ψ G) := Finite.compactSpace
  set K := (realLie Ψ G).comap (fromFrame x) with hK
  haveI hKs : Subsingleton K := by
    refine ⟨fun Y Y' => ?_⟩
    have hz : ∀ Y : K, Y = 0 := fun Y => by
      apply Subtype.ext
      exact fromFrame_eq_zero x hdet Y.1 (realLie_eq_zero Ψ G h _ Y.2)
    rw [hz Y, hz Y']

  have hν : ∀ s, riemLie Ψ G x s ≤ 1 := by
    intro s
    set b := (stdOrthonormalBasis ℝ K).toBasis
    have hb : b.addHaar Set.univ = 1 := by
      rw [Module.Basis.addHaar, ← Set.Nonempty.eq_univ (b.parallelepiped).nonempty]
      exact Measure.addHaarMeasure_self
    calc riemLie Ψ G x s ≤ riemLie Ψ G x Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ 1 := by
        unfold riemLie
        by_cases hm : AEMeasurable (fun Y : K => fromFrame x Y.1) b.addHaar
        · rw [Measure.map_apply_of_aemeasurable hm MeasurableSet.univ, Set.preimage_univ, hb]
        · rw [Measure.map_of_not_aemeasurable hm]; simp
  set μ := (Measure.haar : Measure (realSU Ψ G))
  have hu0 : μ Set.univ ≠ 0 := (isOpen_univ.measure_ne_zero μ Set.univ_nonempty)
  have hut : μ Set.univ ≠ ⊤ := (isCompact_univ.measure_lt_top).ne
  have hball : ∀ ε : ℝ, 0 < ε → grpBall (realSU Ψ G) ε = Set.univ := by
    intro ε hε
    ext g
    simp only [Set.mem_univ, iff_true]
    rw [Subsingleton.elim g 1]
    intro τ a b
    simpa using hε
  have hlim : Filter.limsup (fun ε : ℝ => riemLie Ψ G x (tanBall Ψ r ε) / μ (grpBall (realSU Ψ G) ε))
      (nhdsWithin 0 (Set.Ioi 0)) ≤ 1 / μ Set.univ := by
    refine Filter.limsup_le_of_le (h := ?_)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hball ε hε]
    exact ENNReal.div_le_div_right (hν _) _
  show riemHaar Ψ G x S ≤ 1
  unfold riemHaar tangentHaar
  rw [Measure.smul_apply, smul_eq_mul]
  calc _ ≤ (1 / μ Set.univ) * μ Set.univ :=
        mul_le_mul' hlim (measure_mono (Set.subset_univ S))
    _ = 1 := ENNReal.div_mul_cancel hu0 hut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxGe
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem eq_zero_of_skew_of_I_smul_skew {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    (M : Matrix (Fin r) (Fin r) ℂ)
    (h1 : ∀ u w, hermC τ G (M *ᵥ u) w + hermC τ G u (M *ᵥ w) = 0)
    (h2 : ∀ u w, hermC τ G ((Complex.I • M) *ᵥ u) w + hermC τ G u ((Complex.I • M) *ᵥ w) = 0) :
    M = 0 := by
  have hl : ∀ (c : ℂ) v w, hermC τ G (c • v) w = c * hermC τ G v w := by
    intro c v w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hr : ∀ (c : ℂ) v w, hermC τ G v (c • w) = starRingEnd ℂ c * hermC τ G v w := by
    intro c v w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hA : ∀ u w, hermC τ G (M *ᵥ u) w = 0 := by
    intro u w
    have e1 := h1 u w
    have e2 := h2 u w
    rw [smul_mulVec, smul_mulVec, hl, hr, Complex.conj_I] at e2
    have : Complex.I * (2 * hermC τ G (M *ᵥ u) w) = 0 := by linear_combination e2 + Complex.I * e1
    simpa [Complex.I_ne_zero] using this
  have hGt : (G.map τ).det ≠ 0 := by
    have e := RingHom.map_det τ G
    rw [RingHom.mapMatrix_apply] at e
    rw [← e]; exact (map_ne_zero τ).2 hG
  have hv : ∀ u, M *ᵥ u = 0 := by
    intro u
    refine Matrix.eq_zero_of_vecMul_eq_zero hGt ?_
    funext b
    have := hA u (Pi.single b 1)
    simpa [hermC, Matrix.vecMul, dotProduct, Pi.single_apply] using this
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

theorem finrank_comap_realLie_le (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    (hr : 1 ≤ r) (hG : G.det ≠ 0) (hx : ∀ τ, (mat x τ).det ≠ 0) :
    Module.finrank ℝ ((realLie Ψ G).comap (fromFrame x)) ≤ Ψ.card * (r ^ 2 - 1) := by
  set W := (realLie Ψ G).comap (fromFrame x) with hW
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  have hsm : ∀ (c : ℂ) (V : EuclideanSpace ℂ (Ψ × Fin r × Fin r)),
      fromFrame x (c • V) = c • fromFrame x V := by
    intro c V
    funext τ
    have e : Matrix.of (fun a b => (c • V) (τ, a, b)) = c • Matrix.of (fun a b => V (τ, a, b)) := rfl
    show (mat x τ * Matrix.of (fun a b => (c • V) (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) =
      c • (mat x τ * Matrix.of (fun a b => V (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
    rw [e, Matrix.mul_smul, Matrix.smul_mul]
  have hIW : ∀ V, V ∈ W → Complex.I • V ∈ W → V = 0 := by
    intro V h1 h2
    have h1' : fromFrame x V ∈ realLie Ψ G := h1
    have h2' : fromFrame x (Complex.I • V) ∈ realLie Ψ G := h2
    rw [hsm] at h2'
    have hM : ∀ τ, Matrix.of (fromFrame x V τ) = 0 := fun τ =>
      eq_zero_of_skew_of_I_smul_skew hG _ (h1' τ).2 (h2' τ).2
    refine PiLp.ext fun p => ?_
    obtain ⟨τ, a, b⟩ := p
    have e : (mat x τ * Matrix.of (fun a b => V (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ) = 0 := hM τ
    have := key1 τ (Matrix.of (fun a b => V (τ, a, b)))
    rw [e, Matrix.mul_zero, Matrix.zero_mul] at this
    have := congrFun (congrFun this a) b
    simpa using this.symm
  let L : (W × W) →ₗ[ℝ] EuclideanSpace ℂ (Ψ × Fin r × Fin r) :=
    { toFun := fun p => (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) + Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r))
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, smul_add]
        rw [smul_comm] }
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp
    have hp' : (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) + Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = 0 := hp
    have e1 : (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = Complex.I • ((-p.2 : W) : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) := by
      rw [Submodule.coe_neg, smul_neg]; exact eq_neg_of_add_eq_zero_left hp'
    have h3 : Complex.I • ((-p.2 : W) : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) ∈ W := e1 ▸ p.1.2
    have h4 := hIW _ (-p.2).2 h3
    have h5 : p.2 = 0 := by
      have : -p.2 = 0 := Subtype.ext h4
      simpa using this
    have h6 : p.1 = 0 := by
      apply Subtype.ext
      rw [e1, h4, smul_zero]; rfl
    exact Prod.ext h6 h5
  let tr : EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] (Ψ → ℂ) :=
    { toFun := fun Y τ => ∑ a, Y (τ, a, a)
      map_add' := by
        intro Y Z; funext τ; simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c Y; funext τ; simp [Finset.smul_sum] }
  have htrW : ∀ Y ∈ W, tr Y = 0 := by
    intro Y hY
    have hY' : fromFrame x Y ∈ realLie Ψ G := hY
    funext τ
    have ht := (hY' τ).1
    have e : Matrix.of (fromFrame x Y τ) = mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹ := rfl
    rw [e, Matrix.trace_mul_cycle, Matrix.nonsing_inv_mul _ (hx τ).isUnit, Matrix.one_mul] at ht
    show ∑ a, Y (τ, a, a) = (0 : Ψ → ℂ) τ
    simpa [Matrix.trace] using ht
  have hrange : L.range ≤ LinearMap.ker tr := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.mem_ker]
    have e : L p = (p.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) + Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) := rfl
    rw [e, map_add]
    have h2 : tr (Complex.I • (p.2 : EuclideanSpace ℂ (Ψ × Fin r × Fin r))) = Complex.I • tr p.2 := by
      funext τ; simp [tr, Finset.mul_sum]
    rw [h2, htrW _ p.1.2, htrW _ p.2.2, smul_zero, add_zero]
  have hsurj : LinearMap.range tr = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨WithLp.toLp 2 (fun p : Ψ × Fin r × Fin r =>
      if p.2.1 = ⟨0, hr⟩ ∧ p.2.2 = ⟨0, hr⟩ then c p.1 else 0), ?_⟩
    funext τ
    simp [tr]
  have hdimE : Module.finrank ℝ (EuclideanSpace ℂ (Ψ × Fin r × Fin r)) = 2 * (Ψ.card * (r * r)) := by
    rw [(WithLp.linearEquiv 2 ℝ (Ψ × Fin r × Fin r → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Fintype.card_prod, Fintype.card_coe, mul_comm]
  have hdimP : Module.finrank ℝ (Ψ → ℂ) = 2 * Ψ.card := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, Fintype.card_coe, mul_comm]
  have h1 := LinearMap.finrank_range_add_finrank_ker tr
  rw [hsurj, finrank_top, hdimE, hdimP] at h1
  have h2 := Submodule.finrank_mono hrange
  rw [LinearMap.finrank_range_of_inj hLinj, Module.finrank_prod] at h2
  have h3 : Ψ.card * (r ^ 2 - 1) = Ψ.card * (r * r) - Ψ.card := by
    rw [Nat.mul_sub_one, sq]
  rw [h3]
  omega

end GlobalTheory.CovTop.VolUp

namespace GlobalTheory.CovTop.VolUp

theorem riemLie_frameBox_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r), 1 ≤ r → G.det ≠ 0 → (∀ τ, (mat x τ).det ≠ 0) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ((ε / ((Ψ.card : ℝ) * (r : ℝ) ^ 2)) ^ (Ψ.card * (r ^ 2 - 1))) ≤ riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < ε} := by
  intro E _ _ _ r Ψ G x hr hG hx ε hε hε1
  set W := (realLie Ψ G).comap (fromFrame x) with hW
  unfold riemLie
  have hf : Measurable (fun Y : W => fromFrame x Y.1) :=
    ((fromFrame x).comp W.subtype).continuous_of_finiteDimensional.measurable
  refine le_trans ?_ (Measure.le_map_apply hf.aemeasurable _)
  rw [OrthonormalBasis.addHaar_eq_volume]
  have hdim := finrank_comap_realLie_le Ψ G x hr hG hx
  set N := Module.finrank ℝ W with hN
  obtain ⟨b⟩ : Nonempty (OrthonormalBasis (Fin N) ℝ W) := ⟨stdOrthonormalBasis ℝ W⟩
  have key1 : ∀ τ (A : Matrix (Fin r) (Fin r) ℂ),
      (mat x τ)⁻¹ * (mat x τ * A * (mat x τ)⁻¹) * mat x τ = A := fun τ A => by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_right _ _ (hx τ).isUnit,
      Matrix.nonsing_inv_mul_cancel_left _ _ (hx τ).isUnit]
  set η : ℝ := ε / ((Ψ.card : ℝ) * (r : ℝ) ^ 2) with hη
  have hη0 : 0 ≤ η := by positivity
  have hcr : (N : ℝ) ≤ (Ψ.card : ℝ) * (r : ℝ) ^ 2 := by
    have : N ≤ Ψ.card * r ^ 2 := hdim.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    exact_mod_cast this
  have hη1 : η ≤ 1 := by
    rcases Nat.eq_zero_or_pos Ψ.card with h0 | h0
    · simp [hη, h0]
    · have : (1 : ℝ) ≤ (Ψ.card : ℝ) * (r : ℝ) ^ 2 := by
        have : 1 ≤ Ψ.card * r ^ 2 := Nat.one_le_iff_ne_zero.2 (by positivity)
        exact_mod_cast this
      exact div_le_one_of_le₀ (hε1.trans this) (by positivity)
  have hNη : (N : ℝ) * η ≤ ε := by
    calc (N : ℝ) * η ≤ ((Ψ.card : ℝ) * (r : ℝ) ^ 2) * η := mul_le_mul_of_nonneg_right hcr hη0
      _ ≤ ε := by
        rcases eq_or_ne ((Ψ.card : ℝ) * (r : ℝ) ^ 2) 0 with h0 | h0
        · rw [h0, zero_mul]; exact hε.le
        · rw [hη, mul_div_cancel₀ _ h0]
  let C : Set (Fin N → ℝ) := Set.univ.pi fun _ => Set.Ioo (-(η / 2)) (η / 2)
  have hmp : MeasurePreserving (fun Y : W => (b.repr Y).ofLp) volume volume :=
    (PiLp.volume_preserving_ofLp _).comp b.measurePreserving_repr
  have hC : volume ((fun Y : W => (b.repr Y).ofLp) ⁻¹' C) = ENNReal.ofReal η ^ N := by
    rw [hmp.measure_preimage (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet,
      Real.volume_pi_Ioo]
    simp [Finset.prod_const]
  calc ENNReal.ofReal (η ^ (Ψ.card * (r ^ 2 - 1))) = ENNReal.ofReal η ^ (Ψ.card * (r ^ 2 - 1)) :=
        ENNReal.ofReal_pow hη0 _
    _ ≤ ENNReal.ofReal η ^ N := pow_le_pow_right_of_le_one' (ENNReal.ofReal_le_one.2 hη1) hdim
    _ = volume ((fun Y : W => (b.repr Y).ofLp) ⁻¹' C) := hC.symm
    _ ≤ _ := by
      refine measure_mono fun Y hY => ?_
      simp only [Set.mem_preimage, C, Set.mem_pi, Set.mem_univ, Set.mem_Ioo, true_implies] at hY
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      intro τ a c
      have e : Matrix.of (fromFrame x Y.1 τ) =
          mat x τ * Matrix.of (fun a b => Y.1 (τ, a, b)) * (mat x τ)⁻¹ := rfl
      rw [e, key1]
      have h1 : ‖(Y.1 : EuclideanSpace ℂ (Ψ × Fin r × Fin r)) (τ, a, c)‖ ≤ ‖Y‖ := PiLp.norm_apply_le _ _
      have h2 : ‖Y‖ ≤ ∑ i, |(b.repr Y).ofLp i| := by
        calc ‖Y‖ = ‖∑ i, (b.repr Y).ofLp i • b i‖ := by rw [b.sum_repr]
          _ ≤ ∑ i, ‖(b.repr Y).ofLp i • b i‖ := norm_sum_le _ _
          _ = ∑ i, |(b.repr Y).ofLp i| := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs]
      have h3 : ∑ i, |(b.repr Y).ofLp i| ≤ (N : ℝ) * (η / 2) := by
        calc ∑ i, |(b.repr Y).ofLp i| ≤ ∑ _i : Fin N, η / 2 :=
              Finset.sum_le_sum fun i _ => (abs_lt.2 (hY i)).le
          _ = (N : ℝ) * (η / 2) := by simp
      simp only [Matrix.of_apply]
      linarith

end GlobalTheory.CovTop.VolUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowGoodWeightDictionaryStatement
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_good_weight_dictionary : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → RecTied D L → ∀ i : Fin D.R.m, GoodW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i) := by
  first | exact @GlobalTheory.CovTop.goodW_at | exact GlobalTheory.CovTop.goodW_at | (intros; apply GlobalTheory.CovTop.goodW_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLatticeFinitelyGenerated
section
set_option synthInstance.maxHeartbeats 400000
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.LatAllFG

theorem fg_latOf_congr {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R] [Algebra (𝓞 K) R]
    [IsScalarTower (𝓞 K) K R] {C C' : Submodule K R} (hC : C = C')
    (Vs : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → Set (R → EReal)) (hV : ∀ la, ∀ v ∈ Vs la, IsVal la v)
    (h : (latOf C Vs hV).FG) : (latOf C' Vs hV).FG := by
  subst hC; exact h

theorem latW_fg {D : D7} (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j) (hn : 0 < w.n) :
    (latW (T.U j) (wtZ (wtA w) w.n)).FG := by
  have h := (GlobalTheory.SupFull.fullAt_of_pins D T.toCore hT.pins j hj (hT.unf j hj _ T.good_σ₀) w hn).1
  unfold GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation.supLat GlobalTheory.IndefiniteRowSideFullHecke.KappaLatticeEvaluation.latIn at h
  have h2 := Submodule.fg_of_fg_map_injective _ Subtype.val_injective h
  exact fg_latOf_congr (cuspW_wtZ (Xo := T.Q.Xo j) (c := T.Q.c) (U := T.U j) (wtA w) w.n).symm _ _ h2

theorem fg_span_image {K L V W : Type} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module L W] [Module (𝓞 L) W] [IsScalarTower (𝓞 L) L W]
    (ι : V →ₛₗ[algebraMap K L] W) (M : Submodule (𝓞 K) V) (hM : M.FG) :
    (Submodule.span (𝓞 L) (ι '' (M : Set V))).FG := by
  classical
  obtain ⟨s, hs⟩ := hM
  refine ⟨s.image ι, le_antisymm ?_ ?_⟩
  · rw [Finset.coe_image]
    exact Submodule.span_mono (Set.image_mono (hs ▸ Submodule.subset_span))
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      have e : ι (c • y) = (RingOfIntegers.mapRingHom (algebraMap K L) c) • ι y := by
        rw [← algebraMap_smul K c y, ι.map_smulₛₗ, ← algebraMap_smul L (RingOfIntegers.mapRingHom (algebraMap K L) c) (ι y)]
        rfl
      rw [e]
      exact Submodule.smul_mem _ _ hy

end GlobalTheory.CovTop.LatAllFG

open GlobalTheory.CovTop.LatAllFG in

theorem GlobalTheory.CovTop.latAll_fg_at : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz),
    p.Rows → RecTied D L → ∀ i : Fin D.R.m, (latAll p.R.toRealDat i).FG := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p _ _ i
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, i.2⟩
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hn : 0 < (p.κ i).n := by
    rw [(p.fw.kap i τ).2.2]
    have := D.R.three_m_lt_t
    rw [Ranks.nV]
    omega
  have hW := latW_fg p.T p.fw.laws _ hj (p.κ i) hn
  obtain ⟨ι, -, -, himg⟩ := GlobalTheory.T.exists_semilinear_emb_supLattice_onto_realisation _ _ _ _ _ _ _ _ _ p.fw i
  unfold latAll
  rw [← himg]
  exact fg_span_image ι _ hW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowNormHasGramStatement
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_norm_has_gram : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → RecTied D L → ∀ i : Fin D.R.m, HasGram (nrmR p.R.toRealDat i) := by
  first | exact @GlobalTheory.CovTop.GramPt.hasGram_at | exact GlobalTheory.CovTop.GramPt.hasGram_at | (intros; apply GlobalTheory.CovTop.GramPt.hasGram_at <;> assumption)
end

