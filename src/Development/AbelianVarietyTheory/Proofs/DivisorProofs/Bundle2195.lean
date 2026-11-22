import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.FiniteNotLocFrOne
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormEqNegOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCoefficientPolySimpleSubquotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2107
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantExponentsMatchingWeightBarGap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.WtMatchArithBar

theorem exists_shift {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (f : Fin (p + q) → ℤ) (hf : Antitone f)
    (hg0 : 1 ≤ GlobalTheory.CompHS.gap f (p - 1))
    (N M k : ℕ) (hN : 0 < N) (hk : 2 * M + N ≤ k + 1) :
    ∃ w : ℤ, (∀ i : Fin (p + q), (i : ℕ) < p → 0 ≤ ((k : ℤ) + 1) * f i + N * w - M) ∧
      (∀ i : Fin (p + q), p ≤ (i : ℕ) → 0 ≤ -(((k : ℤ) + 1) * f i) - N * w - M) := by
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  set X : ℤ := ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ - M with hX
  refine ⟨-(X / N), fun i hi => ?_, fun i hi => ?_⟩
  · have h1 : f i ≥ f ⟨p - 1, by omega⟩ := hf (by simp [Fin.le_def]; omega)
    have h2 : ((k : ℤ) + 1) * f ⟨p - 1, by omega⟩ ≤ ((k : ℤ) + 1) * f i := mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 := Int.emod_nonneg X (by omega : (N : ℤ) ≠ 0)
    have h4 := Int.emod_add_mul_ediv X (N : ℤ)
    linarith
  · have h1 : f i ≤ f ⟨p, by omega⟩ := hf (by simp [Fin.le_def]; omega)
    have hg := hg0
    unfold GlobalTheory.CompHS.gap at hg
    rw [dif_pos (by omega)] at hg
    have e : (⟨p - 1 + 1, by omega⟩ : Fin (p + q)) = ⟨p, by omega⟩ := Fin.ext (by simp; omega)
    rw [e] at hg
    have h2 : ((k : ℤ) + 1) * f i ≤ ((k : ℤ) + 1) * (f ⟨p - 1, by omega⟩ - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h3 := Int.emod_lt_of_pos X (by omega : (0 : ℤ) < N)
    have h4 := Int.emod_add_mul_ediv X (N : ℤ)
    have hk' : (2 * M + N : ℤ) ≤ k + 1 := by exact_mod_cast hk
    nlinarith

open GlobalTheory.AllWt in

theorem exists_dom_exponents_bar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw), 1 ≤ Dw.p → 1 ≤ Dw.q → (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ GlobalTheory.CompHS.gap (la τ) (Dw.p - 1)) → ∀ (N M k : ℕ), 0 < N → 2 * M + N ≤ k + 1 → ∃ (w : GlobalTheory.AllWt.Psi H → ℤ) (a : (E →+* ℂ) × ℕ → ℕ), Dom a (2 * M) ∧ (fun i => (ex Dw a (2 * M) i : ℤ)) = (k + 1) • GlobalTheory.AllWt.exOf Dw la 0 + GlobalTheory.AllWt.exOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) M := by
  intro E _ _ _ H Dw la hp hq hanti hgap N M k hN hk
  have key : ∀ σ : Psi H, ∃ w : ℤ,
      (∀ i : Fin (Dw.p + Dw.q), (i : ℕ) < Dw.p → 0 ≤ ((k : ℤ) + 1) * la σ i + N * w - M) ∧
      (∀ i : Fin (Dw.p + Dw.q), Dw.p ≤ (i : ℕ) → 0 ≤ -(((k : ℤ) + 1) * la σ i) - N * w - M) :=
    fun σ => exists_shift hp hq (la σ) (hanti σ) (hgap σ) N M k hN hk
  choose w hwb hws using key
  have hantiσ : ∀ (σ : Psi H) (i j : Fin (Dw.p + Dw.q)), i ≤ j → la σ j ≤ la σ i :=
    fun σ _ _ h => hanti σ h
  set val : (E →+* ℂ) × ℕ → ℤ := fun x => ((k : ℤ) + 1) * (wtOf Dw la 0).1 x +
    (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 x with hval
  have vbig : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.p),
      val (σ.1, i) = ((k : ℤ) + 1) * la σ ⟨i, by omega⟩ + (N * w σ - M) := by
    intro σ i hi
    simp only [hval]
    rw [wtOf_big _ _ σ i hi, wtOf_big _ _ σ i hi]
    simp [GlobalTheory.FlatLine.parWt]
  have vsmall : ∀ (σ : Psi H) (i : ℕ) (hi : i < Dw.q),
      val (conjEmb σ.1, i) = -(((k : ℤ) + 1) * la σ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩) - N * w σ - M := by
    intro σ i hi
    simp only [hval]
    rw [wtOf_small _ _ σ i hi, wtOf_small _ _ σ i hi]
    simp [GlobalTheory.FlatLine.parWt]
    ring
  have split : ∀ τ : E →+* ℂ, (∃ σ : Psi H, σ.1 = τ ∧ Dw.mult τ = Dw.p) ∨
      (∃ σ : Psi H, conjEmb σ.1 = τ ∧ Dw.mult τ = Dw.q) := by
    intro τ
    by_cases h : τ (H.rt : E) = H.rt0
    · exact Or.inl ⟨⟨τ, h⟩, rfl, by simp [Datum.mult, h]⟩
    · exact Or.inr ⟨⟨conjEmb τ, conj_mem h⟩, conjEmb_conjEmb τ, by simp [Datum.mult, h]⟩
  have nonneg : ∀ (τ : E →+* ℂ) (i : ℕ), i < Dw.mult τ → 0 ≤ val (τ, i) := by
    intro τ i hi
    rcases split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩
    · rw [hm] at hi; rw [vbig σ i hi]; have := hwb σ ⟨i, by omega⟩ hi; linarith
    · rw [hm] at hi; rw [vsmall σ i hi]; exact hws σ _ (by simp)
  have mono : ∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → val (τ, j) ≤ val (τ, i) := by
    intro τ i j hij hj
    have hk0 : (0 : ℤ) ≤ (k : ℤ) + 1 := by positivity
    rcases split τ with ⟨σ, rfl, hm⟩ | ⟨σ, rfl, hm⟩
    · rw [hm] at hj
      rw [vbig σ i (by omega), vbig σ j hj]
      have := hantiσ σ ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp [Fin.le_def]; omega)
      nlinarith
    · rw [hm] at hj
      rw [vsmall σ i (by omega), vsmall σ j hj]
      have := hantiσ σ ⟨Dw.p + (Dw.q - 1 - j), by omega⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩
        (by simp [Fin.le_def]; omega)
      nlinarith
  refine ⟨w, fun x => if x.2 < Dw.mult x.1 then (val x).toNat else 0, ⟨fun τ => ?_, even_two_mul M⟩, ?_⟩
  · intro i j hij
    simp only
    split_ifs with hj hi hi
    · exact Int.toNat_le_toNat (mono τ i j hij hj)
    · omega
    · exact Nat.zero_le _
    · exact le_refl _
  · funext x
    rcases x with _ | ⟨τ, i⟩
    · simp [ex, exOf, exZ, wtOf]
    · have hi : (i : ℕ) < Dw.mult τ := i.2
      show (((if (i : ℕ) < Dw.mult τ then (val (τ, (i : ℕ))).toNat else 0 : ℕ)) : ℤ) = _
      rw [if_pos hi, Int.toNat_of_nonneg (nonneg τ i hi)]
      rw [Pi.add_apply, Pi.smul_apply]
      show _ = (k + 1) • (wtOf Dw la 0).1 (τ, (i : ℕ)) +
        (wtOf Dw (GlobalTheory.FlatLine.parWt Dw fun τ => (N : ℤ) * w τ) (M : ℤ)).1 (τ, (i : ℕ))
      rw [nsmul_eq_mul]
      simp only [hval]
      push_cast
      ring

end GlobalTheory.WtMatchArithBar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSmulIdemOfBdd
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatLine

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.L2.Pj GlobalTheory.AllWt

theorem isAlgebraic_of_norm_bdd {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Algebra K ℂ]
    (P₀ : Ω →ₐ[K] ℂ) {b : Ω} {C : ℝ} (h : ∀ P : Ω →ₐ[K] ℂ, ‖P b‖ ≤ C) : IsAlgebraic K b := by
  by_contra hb
  have hb0 : P₀ b ≠ 0 := fun h0 => hb ((map_eq_zero P₀).1 h0 ▸ isAlgebraic_zero)
  have hpos : 0 < ‖P₀ b‖ := norm_pos_iff.2 hb0
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ‖P₀ b‖)
  have hN0 : (N : K) ≠ 0 := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (le_trans (norm_nonneg _) (h P₀)) hpos.le) hN
    exact_mod_cast (Nat.cast_pos.1 this).ne'
  have hi : AlgebraicIndepOn K id ({b} : Set Ω) := algebraicIndependent_unique_type_iff.2 hb
  obtain ⟨T, hT, hbas⟩ := exists_isTranscendenceBasis_superset hi
  have hw : AlgebraicIndependent K fun i : T => P₀ i := hbas.1.map' P₀.injective
  have hw2 : AlgebraicIndependent K fun i : T => Polynomial.aeval (P₀ i) (Polynomial.C (N : K) * Polynomial.X) :=
    hw.polynomial_aeval_of_transcendental fun _ => Polynomial.transcendental _
      (by rw [Polynomial.natDegree_C_mul_X _ hN0]; exact one_ne_zero)
      (by rw [Polynomial.leadingCoeff_C_mul_X]; exact mem_nonZeroDivisors_of_ne_zero hN0)
  letI : Algebra (MvPolynomial T K) Ω := (MvPolynomial.aeval fun i : T => (i : Ω)).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial T K) ℂ := (MvPolynomial.aeval fun i : T =>
    Polynomial.aeval (P₀ i) (Polynomial.C (N : K) * Polynomial.X)).toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial T K) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hbas.1
  haveI : FaithfulSMul (MvPolynomial T K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hw2
  haveI : Algebra.IsAlgebraic (MvPolynomial T K) Ω :=
    haveI := hbas.isAlgebraic
    ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hbas.1.aevalEquiv.symm.toRingHom) (g := RingHom.id Ω)
      (Algebra.IsAlgebraic.isAlgebraic y) hbas.1.aevalEquiv.symm.injective (RingHom.ext fun z => by
        obtain ⟨p, rfl⟩ := hbas.1.aevalEquiv.surjective z
        simp [RingHom.algebraMap_toAlgebra]))⟩
  let Q : Ω →ₐ[MvPolynomial T K] ℂ := IsAlgClosed.lift
  let P : Ω →ₐ[K] ℂ := { Q.toRingHom with
    commutes' := fun a => by
      have := Q.commutes (MvPolynomial.C a)
      simpa [RingHom.algebraMap_toAlgebra] using this }
  have h1 : P b = (N : ℂ) * P₀ b := by
    show Q b = _
    have := Q.commutes (MvPolynomial.X ⟨b, hT rfl⟩)
    simpa [RingHom.algebraMap_toAlgebra, map_natCast] using this
  have h2 := h P
  rw [h1, norm_mul, Complex.norm_natCast] at h2
  have h3 : C < N * ‖P₀ b‖ := (div_lt_iff₀ hpos).1 hN
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem exists_eq_smul_idem_of_bdd {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hF : FnAlgClosed Xo c) {Z : Comp Xo c} {g : Rul Xo c} (hg : g ∈ secZ Xo c 0) (hs : g ∈ suppOn Z) {C : ℝ}
    (hb : ∀ z ∈ framesOn U Z, ‖rdU U g z.1 z.2‖ ≤ C) : ∃ a : c.F, g = a • idem Z := by
  obtain ⟨hL, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨⟨P₀⟩, hP⟩ := GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r U hσ hU h Z
  have hi := idem_mem_secZ Z
  rw [secZ_zero_eq] at hg hi
  have key : ∀ P : Om Z →ₐ[c.F] CAt σ, ‖toC (P (evC h Z g))‖ ≤ C := fun P => by
    obtain ⟨k, x, y', t, hm, ht⟩ := hP P
    obtain ⟨w, -, hw⟩ := GlobalTheory.CompBij.rdU_eq_of_reads U h k Z x P y' t hm ht 0 0
    have hz : (⟨k, x.1⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z :=
      ⟨x.2, liesOn_frBor ht (liesOn_frMap hm (liesOn_genFr h Z))⟩
    have h1 := hw _ hi
    have h2 : rdU U (idem Z) k x = 1 := by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_idem (S := CAt σ) hz.2 (haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ); hL.test _ _)
    have h3 : evC h Z (idem Z) = 1 := evR_idem (liesOn_genFr h Z) (hL.test _ _)
    rw [h2, h3, map_one, mul_one] at h1
    rw [← hw g hg, h1]
    exact (congrArg norm (one_mul _)).trans_le (hb _ hz)
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨a, ha⟩ := hF Z _ (isAlgebraic_of_norm_bdd (K := c.F) (b := evC h Z g) P₀ fun P => key P)
  refine ⟨a, sub_eq_zero.1 (GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _
    (sub_mem hg (Submodule.smul_mem _ _ hi)) fun Z' => ?_)⟩
  by_cases hZ : Z' = Z
  · subst hZ
    have h3 : evC h Z' (idem Z') = 1 := evR_idem (liesOn_genFr h Z') (hL.test _ _)
    have h4 := evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) g ((-a) • idem Z')
      (genFr h Z')
    have h5 := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (-a) (idem Z')
      (genFr h Z')
    rw [sub_eq_add_neg, ← neg_smul]
    refine h4.trans ?_
    rw [h5]
    show evC h Z' g + algebraMap _ _ (-a) * evC h Z' (idem Z') = 0
    rw [h3, ← ha, map_neg, mul_one, add_neg_cancel]
  · exact evC_eq_zero h hZ (sub_mem hs (Submodule.smul_mem _ _ (idem_mem_suppOn Z)))

end GlobalTheory.FlatLine

namespace GlobalTheory.CovTop

theorem koecher_unit_const : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (g h : Rul Y.d.Xo₂ Y.d.c₂), g ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 → h ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 → GlobalTheory.FlatLine.idem Z * g = g → GlobalTheory.FlatLine.idem Z * h = h → g * h = GlobalTheory.FlatLine.idem Z → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 g z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 h z ≤ C) → ∃ a : Y.d.c₂.F, g = a • GlobalTheory.FlatLine.idem Z := by
  intro _ D T j Y e o hY _ Z g h hg _ hgi _ _ hB
  have hσ := goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom
  obtain ⟨C, hC⟩ := hB _ hσ
  have hs : g ∈ GlobalTheory.AllWt.suppOn Z := by
    rw [← hgi, mul_comm]
    exact GlobalTheory.AllWt.mul_mem_suppOn _ (GlobalTheory.FlatLine.idem_mem_suppOn Z)
  exact GlobalTheory.FlatLine.exists_eq_smul_idem_of_bdd (Y.U _) hσ (hY.unf _ hσ) hY.geo hg hs (C := C) fun z hz => by
    have h1 := (hC z hz).1
    rwa [GlobalTheory.FlatLine.homN_zero] at h1

end GlobalTheory.CovTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnramifiedCurve
section
set_option autoImplicit false

namespace GlobalTheory.RefSum.UnramCurveField

section
open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.FieldSize.RayExistCurve
open scoped IntermediateField

theorem not_dvd_discr_of_unramIn (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] {n q : ℕ} (hq : q.Prime) (hn : ¬ q ∣ n) (hK : ¬ (q : ℤ) ∣ discr K)
    (hL : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ Ideal.span {(n : 𝓞 K)} → GlobalTheory.NT.UnramIn L 𝔭) :
    ¬ (q : ℤ) ∣ discr L := by
  have hqz : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hq
  refine (not_dvd_discr_iff_forall_mem L (𝓞 L) hqz).2 fun P hP hqP => ?_
  have hqp : ((q : ℤ) : 𝓞 K) ∈ P.under (𝓞 K) := by
    rw [Ideal.mem_under, map_intCast]; exact hqP
  have hp0 : P.under (𝓞 K) ≠ ⊥ := fun e => by
    rw [e, Ideal.mem_bot] at hqp
    exact hq.ne_zero (by exact_mod_cast hqp)
  have h1 : Algebra.IsUnramifiedAt ℤ (P.under (𝓞 K)) :=
    (not_dvd_discr_iff_forall_mem K (𝓞 K) hqz).1 hK _ inferInstance hqp
  let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨P.under (𝓞 K), inferInstance, hp0⟩
  have hnd : ¬ 𝔭.asIdeal ∣ Ideal.span {(n : 𝓞 K)} := by
    rw [Ideal.dvd_span_singleton]
    intro hnp
    obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (n : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)
    have h2 : ((a * q + b * n : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal := by
      rw [Int.cast_add, Int.cast_mul, Int.cast_mul]
      exact add_mem (Ideal.mul_mem_left _ _ hqp) (Ideal.mul_mem_left _ _ (by rwa [Int.cast_natCast]))
    rw [hab, Int.cast_one] at h2
    exact 𝔭.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have : P.LiesOver 𝔭.asIdeal := ⟨rfl⟩
  have h3 : Algebra.IsUnramifiedAt (𝓞 K) P := GlobalTheory.NT.isUnramifiedAt_of_unramIn (hL 𝔭 hnd) P
  exact Algebra.IsUnramifiedAt.comp (P.under (𝓞 K)) P

theorem exists_field_of_rayField (hRF : GlobalTheory.NT.RayField) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n q : ℕ) (hn : 3 ≤ n) (hq : q.Prime) (hqn : ¬ q ∣ n) (hqd : ¬ q ∣ H.d) :
    ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ GlobalTheory.CompRat.CurveOver H F' n := by
  have hdm := H.d_mod
  have hd0 : 0 < H.d := H.d_prime.pos
  obtain ⟨hfin, h2⟩ := finrank_adjoin hd0 H.sqrt_neg_disc_sq
  have hr0 : H.rt0 ∈ ℚ⟮H.rt0⟯ := IntermediateField.mem_adjoin_simple_self ℚ H.rt0
  generalize ℚ⟮H.rt0⟯ = K₀ at hfin h2 hr0
  have hNF : NumberField K₀ := NumberField.mk
  have hr : (⟨H.rt0, hr0⟩ : K₀) ^ 2 = -(H.d : K₀) := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  have hD : discr K₀ = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 H.d_prime.squarefree (by omega) hr
  have hTC : IsTotallyComplex K₀ := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h1 : InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩ ^ 2 = -(H.d : ℝ) := by
      rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd0
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩)]
  obtain ⟨w, hw, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 H.d_prime.squarefree (by omega) hr
  let φ : K₀ →+* ℂ := algebraMap K₀ ℂ
  have hw' : φ w = (1 + H.rt0) / 2 := by
    have := congrArg φ hw
    rw [map_mul, map_add, map_one, map_ofNat] at this
    change _ = 1 + H.rt0 at this
    linear_combination this / 2
  have hc : ∀ a b : ℤ, φ ((a : 𝓞 K₀) + b * w : 𝓞 K₀) = a + b * ((1 + H.rt0) / 2) := fun a b => by
    rw [← hw']
    simp
  have hn0 : (n : 𝓞 K₀) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨L, _, _, _, hL⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hRF K₀ (Ideal.span {(n : 𝓞 K₀)})
    (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let ψ : L →ₐ[K₀] ℂ := IsAlgClosed.lift
  let e₀ : L ≃ₐ[K₀] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  have hfR : FiniteDimensional K₀ ψ.fieldRange := e₀.toLinearEquiv.finiteDimensional
  have hLR := fun (_ : NumberField ψ.fieldRange) => hL.of_algEquiv e₀
  generalize ψ.fieldRange = R at hfR hLR
  have hNR : NumberField R := NumberField.of_module_finite K₀ R
  obtain ⟨hab, hR⟩ := hLR hNR
  change IsRay R (Ideal.span {(n : 𝓞 K₀)}) at hR
  have hdR : ¬ (q : ℤ) ∣ discr R :=
    not_dvd_discr_of_unramIn K₀ R hq hqn (by rwa [hD, dvd_neg, Int.natCast_dvd_natCast]) hR.1
  refine ⟨R.restrictScalars ℚ, hNR, hdR, ?_⟩
  refine (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn E H _ n (by omega)).1
    (R.algebraMap_mem (⟨H.rt0, hr0⟩ : K₀)) fun P hP => ?_
  have hW := GlobalTheory.FieldSize.InRayAny.weberSet_subset K₀ h2 (by omega) P (fun z => ?_) n hn R hR
  · exact ⟨hW (Set.mem_insert _ _), fun s hs => hW (Set.mem_insert_of_mem _
      ⟨_, (hP _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩
  · rw [hP]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, hc s.1 s.2⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨a, b, rfl⟩ := hgen a
      exact ⟨(a, b), hc a b⟩

end

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem exists_unram_curveOver : Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n q : ℕ), 3 ≤ n → q.Prime → ¬ q ∣ 2 * n * H.d → ∃ (F' : IntermediateField ℚ ℂ) (_ : NumberField F'), ¬ (q : ℤ) ∣ discr F' ∧ GlobalTheory.CompRat.CurveOver H F' n :=
  fun h E _ _ _ H n q hn hq hnd => exists_field_of_rayField h.p8 E H n q hn hq
    (fun e => hnd ((e.mul_left 2).mul_right _)) (fun e => hnd (e.mul_left _))

end GlobalTheory.RefSum.UnramCurveField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalHarmonicCongrColumnPolynomial
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefGlob

theorem sum_smul_mem_HaO {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k] (O : Subring k) (cc : Ty → Ty)
    (isX : Ty → Prop) (a : Ty → ℕ → ℕ) {m : ℕ} (x : Fin m → k) (P : Fin m → MvPolynomial (Letter Ty r n) k)
    (hx : ∀ i, x i ∈ O) (hP : ∀ i, P i ∈ HaO r n k O cc isX a) : ∑ i, x i • P i ∈ HaO r n k O cc isX a := by
  classical
  refine ⟨⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hP i).1.1, fun σ i i' hi t => ?_,
    fun q hq => ?_⟩, fun q => ?_⟩
  · rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, (hP j).1.2.1 σ i i' hi t]
  · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hq)
    exact (hP j).1.2.2 q (MvPolynomial.support_smul hj)
  · rw [MvPolynomial.coeff_sum]
    exact O.sum_mem fun j _ => by
      rw [MvPolynomial.coeff_smul, smul_eq_mul]
      exact O.mul_mem (hx j) ((hP j).2 q)

theorem exists_integer_congr {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (T₀ : CDVR)
    (io₀ : K →+* T₀.Fr) (ho : OverLa w T₀.V io₀ 1)
    (hini : ∀ (T : CDVR) (io : K →+* T.Fr) (e : ℕ), OverLa w T.V io e → ∃ (g : T₀.V →+* T.V) (χ : T₀.Fr →+* T.Fr),
      IsLocalHom g ∧ χ.comp io₀ = io ∧ χ.comp (algebraMap T₀.V T₀.Fr) = (algebraMap T.V T.Fr).comp g ∧
        ∀ ϖ : T₀.V, Irreducible ϖ → vV (K' := T.Fr) T.V (algebraMap T.V T.Fr (g ϖ)) = e)
    (d : ℕ) (hd : d ≠ 0) (v : T₀.V) :
    ∃ (x : 𝓞 K) (z : T₀.V), io₀ (x : K) = algebraMap T₀.V T₀.Fr v + (d : T₀.Fr) * algebraMap T₀.V T₀.Fr z := by
  obtain ⟨k, h, e⟩ := GlobalTheory.DefPt.Model.denseIn_of_initial w T₀ io₀ hini (algebraMap T₀.V T₀.Fr v) (d : T₀.V) (Nat.cast_ne_zero.2 hd)
  have hval : ∀ y : K, valV T₀.V (io₀ y) = w.valuation K y := fun y => by
    rw [GlobalTheory.PlaceCompletion.valV_eq_pow_of_overLa ho, pow_one]
  have hk : io₀ k = algebraMap T₀.V T₀.Fr (v - d * h) := by rw [map_sub, e]; ring
  have hk1 : w.valuation K k ≤ 1 := by
    rw [← hval, hk]
    exact GlobalTheory.PlaceCompletion.valV_algebraMap_le_one _
  have hdK : (d : K) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hd0 : w.valuation K (d : K) ≠ 0 := by simpa using hd
  obtain ⟨x, hx⟩ := w.exists_valuation_sub_lt_of_integer hk1 (Units.mk0 _ hd0)
  obtain ⟨z, hz⟩ := GlobalTheory.PlaceCompletion.exists_algebraMap_eq_of_valV_le_one (V := T₀.V)
    (x := io₀ ((algebraMap (𝓞 K) K x - k) / d)) (by
      rw [hval, map_div₀]
      exact div_le_one_of_le₀ hx.le zero_le)
  refine ⟨x, z - h, ?_⟩
  have h2 : io₀ (x : K) = io₀ k + (d : T₀.Fr) * algebraMap T₀.V T₀.Fr z := by
    rw [hz, ← map_natCast io₀, ← map_mul, ← map_add, mul_div_cancel₀ _ hdK]
    exact congrArg io₀ (by simp)
  rw [h2, hk]
  simp only [map_sub, map_mul, map_natCast]
  ring

section Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {c : Coeff l} {T₀ T : CDVR} (g : T₀.V →+* T.V) (χ : T₀.Fr →+* T.Fr)
  (hχ : ∀ x, χ (algebraMap T₀.V T₀.Fr x) = algebraMap T.V T.Fr (g x))

include hχ

theorem isCols_map {io₀ : c.F →+* T₀.Fr} {p n : ℕ} {cx : Lt1 Dw → ℕ} {B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T₀.V}
    (hB : IsCols c T₀ io₀ p cx B) : IsCols c T (χ.comp io₀) p cx fun f b j => g (B f b j) := by
  obtain ⟨blk, hb⟩ := hB
  refine ⟨blk, fun f => ?_⟩
  obtain ⟨h1, ⟨r, h2⟩, h3⟩ := hb f
  refine ⟨fun b j hj => (congrArg g (h1 b j hj)).trans (map_zero g), ⟨r, ?_⟩, fun N => ?_⟩
  · have := h2.map g
    rw [RingHom.map_det] at this
    exact this
  · obtain ⟨x, hx1, hx2, hx3⟩ := h3 N
    refine ⟨x, hx1, fun b j => ?_, hx3⟩
    obtain ⟨z, hz⟩ := hx2 b j
    refine ⟨g z, ?_⟩
    rw [RingHom.comp_apply, hz, hχ]
    simp only [map_add, map_mul, map_pow, map_natCast]

theorem map_polyT {n : ℕ} (cx : Lt1 Dw → ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T₀.V) :
    MvPolynomial.map χ (polyT B cx) = polyT (fun f b j => g (B f b j)) cx := by
  simp only [polyT, polyP, map_prod, map_pow]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [RingHom.map_det]
  congr 2
  ext ρ i : 2
  simp [GlobalTheory.CombMinor.cMat, hχ]

end Push

theorem exists_harmA_congr_polyT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ N : ℕ, ∃ P₁ ∈ harmA (Dw := Dw) c a n, ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∃ (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V) (R : MvPolynomial (LtN Dw n) T.Fr), IsCols c T io p (gap Dw a) B ∧ R ∈ FFV (Dw := Dw) T a n ∧ MvPolynomial.map io P₁ = polyT B (gap Dw a) + ((p : T.Fr) ^ N) • R := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro p hp la a ha n hn N
  obtain ⟨T₀, io₀, ho₀, -, hini⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion c.F la.1
  obtain ⟨B₀, hB₀⟩ := GlobalTheory.IsoCols.exists_isCols E H Dw l Xo c p la T₀ io₀ 1 ho₀ (gap Dw a) n
    (le_trans (Finset.sum_le_sum fun f _ => by split_ifs <;> simp) hn)
  obtain ⟨-, k, cf, Pi, hPi, hsum⟩ := GlobalTheory.totalDegree_le_and_exists_combination_of_mem_FFV E H Dw l Xo c T₀ io₀ a n _
    (polyT_mem_FFV ha hB₀)
  choose x z hxz using fun i => exists_integer_congr la.1 T₀ io₀ ho₀ hini (p ^ N)
    (pow_ne_zero N hp.out.ne_zero) (cf i)
  refine ⟨∑ i, (x i : c.F) • Pi i, sum_smul_mem_HaO _ _ _ _ _ _ (fun i => (x i).2) hPi, fun T io e ho => ?_⟩
  obtain ⟨g, χ, -, rfl, h2, -⟩ := hini T io e ho
  have hχ : ∀ y, χ (algebraMap T₀.V T₀.Fr y) = algebraMap T.V T.Fr (g y) := RingHom.congr_fun h2
  refine ⟨fun f b j => g (B₀ f b j), ∑ i, algebraMap T.V T.Fr (g (z i)) • MvPolynomial.map (χ.comp io₀) (Pi i),
    isCols_map g χ hχ hB₀, sum_smul_mem_HaO _ _ _ _ _ _ (fun i => ⟨_, rfl⟩)
      (fun i => PullbackSections.ffvMap E H Dw l c a n _ (hPi i) T _), ?_⟩
  rw [← map_polyT g χ hχ, hsum, map_sum, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_map, RingHom.comp_apply, hxz i,
    map_add, hχ, map_natCast, Nat.cast_pow, map_pow]
  ring

end GlobalTheory.RefGlob
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixCoefficientPolySimpleSubquotientStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matrixCoefficientPoly_simpleSubquotient : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → GlobalTheory.HighWt.CoefIn O N lam → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], SubQ O N lam ϖ Gm → ∀ w : ι → Fin N → ℕ, (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → ∀ (φ : Gm →+ O ⧸ Ideal.span {ϖ}) (z₀ : Gm), φ z₀ ≠ 0 → (∀ τ (a : alg O N lam), IsProj O N lam τ (w τ) a → a • z₀ = z₀) → (∀ (c : O) (z : Gm), φ (algebraMap O (alg O N lam) c • z) = Ideal.Quotient.mk (Ideal.span {ϖ}) c * φ z) → (∀ τ (v : Fin N → ℕ) (a : alg O N lam), IsProj O N lam τ v a → v ≠ w τ → ∀ z, φ (a • z) = 0) → ∃ Pz : Gm →+ MvPolynomial (BVar N ι) (O ⧸ Ideal.span {ϖ}), (∀ (c : O) (z : Gm), Pz (algebraMap O (alg O N lam) c • z) = C (Ideal.Quotient.mk (Ideal.span {ϖ}) c) * Pz z) ∧ (∀ (g : ι → GL (Fin N) O) (z : Gm), Pz (grpA O N lam g • z) = blockSub (O ⧸ Ideal.span {ϖ}) N (fun τ => (((g τ)⁻¹ : GL (Fin N) O) : Matrix (Fin N) (Fin N) O).map (Ideal.Quotient.mk (Ideal.span {ϖ}))) (Pz z)) ∧ (∀ τ (v : Fin N → ℕ) (a : alg O N lam), IsProj O N lam τ v a → ∀ z, Pz (a • z) = weightedHomogeneousComponent (blockW N τ) v (Pz z)) ∧ (∀ z τ, toBlock (O ⧸ Ideal.span {ϖ}) N τ (Pz z) ∈ dualWeyl (MvPolynomial (OVar N τ) (O ⧸ Ideal.span {ϖ})) N N (w τ)) ∧ Pz z₀ ≠ 0 := by
  first | exact @GlobalTheory.HighWtEmb.exists_coefPoly | exact GlobalTheory.HighWtEmb.exists_coefPoly | (intros; apply GlobalTheory.HighWtEmb.exists_coefPoly <;> assumption)
end

