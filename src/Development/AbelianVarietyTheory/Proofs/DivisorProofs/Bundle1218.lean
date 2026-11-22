import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivAtSelfDualLatticeIffHasElementaryDivisors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceOrdEqAlongEtaleTower
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0011
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0010
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0013
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivAtSelfDualLatticeIffHasElementaryDivisorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divAt_selfDual_lattice_iff_hasElementaryDivisors : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU D.host.E V.rank ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ) (x : UA D.host.E V.rank),
      IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → x ∈ locU V.rank P →
      (DivAt V e (ϖ : D.host.E) d (cj j h₀ x) ↔ d.length = V.rank ∧ HasDiv (Ov D.host.E P) d (cLoc P x)) := by
  first | exact @GlobalTheory.DivTransfer.divAt_cj_iff | exact GlobalTheory.DivTransfer.divAt_cj_iff | (intros; apply GlobalTheory.DivTransfer.divAt_cj_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowMemSectionsOfMulPowMemStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.div_pow_mem_sections_of_mul_pow_mem : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (N m : ℕ) (u : X.functionField), u ∈ P.H N m → u * t ^ N / s ^ m ∈ P.H 0 (b * N) → u / s ^ m ∈ P.H N 0 := by
  first | exact @GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow | exact GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow | (intros; apply GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryCharacterTrivialOfSiegelStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledUnitary_character_trivial_of_siegel : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ c : UG (cA σ) (dbl (incM F J)) →* ℂˣ, Continuous c → (∀ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix _ _ (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 → c p = 1) → c = 1 := by
  first | exact @GlobalTheory.SiegelChar.eq_one_of_siegel | exact GlobalTheory.SiegelChar.eq_one_of_siegel | (intros; apply GlobalTheory.SiegelChar.eq_one_of_siegel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdIntegralMonicCoprimeDerivativeBezoutFactor
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem monic_dvd_integral_factor_bezout : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (P₀ : (w.adicCompletionIntegers E)[X]), P₀.Monic →
    IsCoprime P₀ (derivative P₀) → ∀ Q₁ : (w.adicCompletion E)[X],
    Q₁ ∣ P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∃ (Q₁₀ Q₂₀ A B : (w.adicCompletionIntegers E)[X]) (c : w.adicCompletion E), c ≠ 0 ∧ P₀ = Q₁₀ * Q₂₀ ∧
      A * Q₁₀ + B * Q₂₀ = 1 ∧ Q₁ = C c * Q₁₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
  intro E _ _ w P₀ hP hc Q₁ hQ
  have hinj : Function.Injective (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := IsFractionRing.injective (w.adicCompletionIntegers E) (w.adicCompletion E)
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (w.adicCompletion E) hP hQ
  have hPm : (P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))).Monic := hP.map _
  have hQ0 : Q₁ ≠ 0 := by
    rintro rfl
    exact hPm.ne_zero (zero_dvd_iff.mp hQ)
  have hlc : Q₁.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
  have hgm' : g.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = Q₁ * C Q₁.leadingCoeff⁻¹ := by
    calc _ = g.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) * C Q₁.leadingCoeff * C Q₁.leadingCoeff⁻¹ := by
          rw [mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, mul_one]
      _ = Q₁ * C Q₁.leadingCoeff⁻¹ := by rw [hg]
  have hgmon : g.Monic := by
    apply Polynomial.monic_of_injective hinj
    rw [hgm']
    exact monic_mul_leadingCoeff_inv hQ0
  have hdvd : g ∣ P₀ := by
    rw [← map_dvd_map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) hinj hgmon]
    exact dvd_trans ⟨C Q₁.leadingCoeff, hg.symm⟩ hQ
  obtain ⟨Q₂, hQ₂⟩ := hdvd
  obtain ⟨a, b, hab⟩ := hc
  refine ⟨g, Q₂, a * Q₂ + b * derivative Q₂, b * derivative g, Q₁.leadingCoeff, hlc, hQ₂, ?_, ?_⟩
  · rw [hQ₂, derivative_mul] at hab
    linear_combination hab
  · exact hg.symm.trans (mul_comm _ _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceCentreOnBaseOfEtaleTowerOverNormalLocal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem Place.ord_eq_zero_iff_isUnit {L : Type} [Field L] {cL : ℂ →+* L} (P : Place cL) {u : P.ring}
    (hu : u ≠ 0) : P.ord (u : L) = 0 ↔ IsUnit u := by
  refine ⟨fun h => ?_, P.ord_eq_zero⟩
  have hu' : (u : L) ≠ 0 := fun e => hu (Subtype.ext e)
  have hi : (u : L)⁻¹ ∈ P.ring := by
    rw [← P.ord_nonneg_iff (inv_ne_zero hu'), P.ord_inv, h, neg_zero]
  exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ hu'))

theorem Place.exists_centre_of_isPrimeOf : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (T : Subring L) (P : Place cL), P.IsPrimeOf T →
    ∃ q : Ideal T, q.IsPrime ∧ q.height = 1 ∧ ∀ t : T, t ≠ 0 → (P.ord (t : L) = 0 ↔ t ∉ q) := by
  intro L _ cL T P hP
  have hC : ∀ t : T, (t : L) ∈ P.ring := fun t => hP.1 _ t.2
  let f : T →+* P.ring := T.subtype.codRestrict P.ring hC
  let q : Ideal T := (IsLocalRing.maximalIdeal P.ring).comap f
  haveI hq : q.IsPrime := Ideal.comap_isPrime _ _
  have hmem : ∀ t : T, t ∉ q ↔ IsUnit (f t) := fun t => by
    simp only [q, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  have hf : ∀ t : T, ((f t : P.ring) : L) = t := fun t => rfl
  have hord : ∀ t : T, t ≠ 0 → (P.ord (t : L) = 0 ↔ t ∉ q) := fun t ht => by
    rw [hmem t]
    have h0 : f t ≠ 0 := by
      intro e
      apply ht
      apply Subtype.ext
      rw [← hf t, e]
      simp
    have h1 := P.ord_eq_zero_iff_isUnit h0
    rw [hf t] at h1
    exact h1
  letI : Algebra T P.ring := f.toAlgebra
  haveI : IsLocalization.AtPrime P.ring q :=
    { map_units := fun y => (hmem y).1 y.2
      surj := fun z => by
        obtain ⟨a, ha, b, hb, hb0, hbo, e⟩ := hP.2 z z.2
        have hb' : (⟨b, hb⟩ : T) ∉ q :=
          (hord ⟨b, hb⟩ (fun e' => hb0 (congrArg Subtype.val e'))).1 hbo
        exact ⟨(⟨a, ha⟩, ⟨⟨b, hb⟩, hb'⟩), Subtype.ext e⟩
      exists_of_eq := fun {x y} e => ⟨1, by
        have h' : ((algebraMap T P.ring x : P.ring) : L) = ((algebraMap T P.ring y : P.ring) : L) :=
          congrArg Subtype.val e
        have : x = y := Subtype.ext h'
        rw [this]⟩ }
  have hd := IsLocalization.AtPrime.ringKrullDim_eq_height q P.ring
  rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at hd
  refine ⟨q, hq, ?_, hord⟩
  exact_mod_cast hd.symm

end GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem IsEtTower.flat {K L : Type} [Field K] [Field L] {cK : ℂ →+* K} {cL : ℂ →+* L} {r : ℕ}
    {R : Subring K} {T : Subring L} {ι : R →+* T} {ψ : T →+* R} {τ : Fin r → T}
    (h : IsEtTower cK R cL T ι ψ τ) : IsNoetherianRing R ∧ ι.Flat := by
  letI := (cK.codRestrict R h.base.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := h.base.essFiniteType
  haveI hR : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  refine ⟨hR, ?_⟩
  let B := MvPolynomial (Fin r) R
  let e : B →+* T := MvPolynomial.eval₂Hom ι τ
  letI : Algebra B T := e.toAlgebra
  letI : Algebra R T := ι.toAlgebra
  haveI : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq fun a => by
    show ι a = e (MvPolynomial.C a)
    exact (MvPolynomial.eval₂_C _ _ _).symm
  haveI : Algebra.FormallyEtale B T := h.etale
  have hc : (cL.codRestrict T h.top.const_mem) = e.comp ((algebraMap R B).comp (cK.codRestrict R h.base.const_mem)) := by
    refine RingHom.ext fun a => Subtype.ext ?_
    have h2 : e (MvPolynomial.C (cK.codRestrict R h.base.const_mem a)) = ι ⟨cK a, h.base.const_mem a⟩ :=
      MvPolynomial.eval₂_C _ _ _
    show cL a = ((e ((algebraMap R B) (cK.codRestrict R h.base.const_mem a)) : T) : L)
    rw [MvPolynomial.algebraMap_eq, h2, h.const]
  haveI : Algebra.EssFiniteType B T := by
    have h1 := h.top.essFiniteType
    rw [hc] at h1
    exact RingHom.EssFiniteType.of_comp _ h1
  haveI : Module.Flat B T := GlobalTheory.SmoothDescent.flat_of_formallySmooth_of_essFiniteType B T
  haveI : Module.Flat R T := Module.Flat.trans R B T
  exact RingHom.flat_algebraMap_iff.2 inferInstance

end GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

theorem centre_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL),
  IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T →
  (∀ g : R, g ≠ 0 → P.ord (ι g : L) = 0) ∨
  ∃ P0 : Place cK, P0.IsPrimeOf R ∧ ∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ P.ord (ι g : L) = 0) := by
  intro K L _ _ cK cL r R T ι ψ τ P h hP
  obtain ⟨-, hF⟩ := h.flat
  obtain ⟨q, hq, hq1, hqo⟩ := Place.exists_centre_of_isPrimeOf cL T P hP
  letI : Algebra R T := ι.toAlgebra
  haveI : Module.Flat R T := hF
  haveI : Algebra.HasGoingDown R T := Algebra.HasGoingDown.of_flat
  let p : Ideal R := q.comap ι
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  haveI : q.LiesOver p := ⟨rfl⟩
  have hinj : Function.Injective ι := fun a b e => by simpa [h.retr] using congrArg ψ e
  have hι : ∀ g : R, g ≠ 0 → (P.ord (ι g : L) = 0 ↔ g ∉ p) := fun g hg =>
    hqo (ι g) ((map_ne_zero_iff ι hinj).2 hg)
  by_cases hp0 : p = ⊥
  · left
    intro g hg
    exact (hι g hg).2 (by rw [hp0]; simpa using hg)
  · right
    have hp1 : p.height = 1 := by
      apply le_antisymm
      · rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
        intro p' hp' hlt
        haveI := hp'
        rw [Nat.cast_one, ENat.lt_one_iff_eq_zero, Ideal.height_eq_zero_iff_eq_bot]
        by_contra hne
        obtain ⟨Q, hQq, hQ, hQo⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := T) q hlt
        haveI := hQ
        have hQ0 : Q ≠ ⊥ := by
          rintro rfl
          apply hne
          rw [hQo.over]
          ext x
          simp only [Ideal.under, Ideal.mem_comap, Ideal.mem_bot]
          exact ⟨fun e => hinj (e.trans (map_zero ι).symm), fun e => by simp [e]⟩
        have h1 : 1 ≤ Q.height := ENat.one_le_iff_ne_zero.2 (mt Ideal.height_eq_zero_iff_eq_bot.1 hQ0)
        have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hQq
        rw [hq1] at h2
        have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) h2
        exact absurd h3 (by decide)
      · exact ENat.one_le_iff_ne_zero.2 (mt Ideal.height_eq_zero_iff_eq_bot.1 hp0)
    obtain ⟨P0, h0, h0o⟩ := GlobalTheory.T.exists_place_isPrimeOf_of_height_one_normal_localModel cK R h.base h.normal p inferInstance hp1
    exact ⟨P0, h0, fun g hg => (h0o g hg).trans (hι g hg).symm⟩

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceDiscKaehlerWedgePermNegStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvrPlace_disc_kaehlerWedge_perm_neg : ∀ {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ) (x : Fin n → K) (σ : Equiv.Perm (Fin n))
  (E : Place c) (φ : K →₀ ℚ), E.disc (dForm c (x ∘ σ)) φ = E.disc (dForm c x) φ ∧ E.disc (-dForm c x) φ = E.disc (dForm c x) φ := by
  first | exact @GlobalTheory.FieldPair.disc_dForm_perm_neg | exact GlobalTheory.FieldPair.disc_dForm_perm_neg | (intros; apply GlobalTheory.FieldPair.disc_dForm_perm_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceOrdEqAlongEtaleTowerStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvrPlace_ord_eq_along_etaleTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (P : Place cL) (P0 : Place cK),
  IsEtTower cK R cL T ι ψ τ → P.IsPrimeOf T → P0.IsPrimeOf R →
  (∀ g : R, g ≠ 0 → (P0.ord (g : K) = 0 ↔ P.ord (ι g : L) = 0)) →
  ∀ g : R, g ≠ 0 → P.ord (ι g : L) = P0.ord (g : K) := by
  first | exact @GlobalTheory.FieldPair.UnramOrd.ord_eq_of_etTower | exact GlobalTheory.FieldPair.UnramOrd.ord_eq_of_etTower | (intros; apply GlobalTheory.FieldPair.UnramOrd.ord_eq_of_etTower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrPlaceTopFormOrdersApiStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvrPlace_topForm_orders_api : ∀ {k K : Type} [Field k] [CharZero k] [Field K] (c : k →+* K) (n : ℕ) (x : Fin n → K), TrBasis c x →
  IsFreeGen K (dForm c x) ∧
  ∀ E : Place c, (∃ ω : Forms E.const n, IsFreeGen E.ring ω) ∧
    (∀ η : Forms c n, η ≠ 0 → E.IsFormOrd η (E.formOrd η)) ∧
    (∀ (η : Forms c n) (f : K), η ≠ 0 → f ≠ 0 → E.formOrd (f • η) = E.ord f + E.formOrd η) ∧
    (∀ (η : Forms c n) (a : ℤ), η ≠ 0 → E.IsFormOrd η a → E.formOrd η = a) := by
  first | exact @GlobalTheory.FieldPair.formOrd_api | exact GlobalTheory.FieldPair.formOrd_api | (intros; apply GlobalTheory.FieldPair.formOrd_api <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqDiscreteSeriesOfLowestKTypeCasimir
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.PsCo.PcEF

theorem eq_discreteSeries_of_lowestKType_casimir : DatumEquiv := by
  intro n ε lam hgap H _ _ _ σ hσ hirr V hV hV0 hc X _ _ D hD
  haveI : CompleteSpace X := hD.1
  have hσD : IsURepOn (UJset ε) D := hD.2.2.1
  have hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v :=
    kStable_of_isKStableSub hσ (isDerivedOn_smE hσ) V hV.1 hV.2.1
  obtain ⟨V', hV', hV0', hVK', hc'⟩ := arb_datum hD (casOnSmooth_of_isDS hD hgap)
  have htop := data_closGen_eq_top hgap hσ (isDerivedOn_smE hσ) hV hc hVK hirr hV0
  have htop' := data_closGen_eq_top hgap hσD (isDerivedOn_smE hσD) hV' hc' hVK' hD.2.2.2.1 hV0'
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap hσ (isDerivedOn_smE hσ) hV hc hVK hV0
    hσD (isDerivedOn_smE hσD) hV' hc' hVK' hV0'
  refine ⟨((LinearIsometryEquiv.ofTop _ _ htop).symm.trans U).trans (LinearIsometryEquiv.ofTop _ _ htop'),
    fun g hg x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.ofTop_apply]
  apply hU g hg
  simp only [LinearIsometryEquiv.ofTop_symm_apply_coe]

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfEvEqOfSmoothOfRelativeDimension
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory

theorem eq_of_ev_eq_of_smoothOfRelativeDimension :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ) (D : ℕ), SmoothOfRelativeDimension D p → ∀ (W : Y.Opens) (a b : Γ(Y, W)), (∀ y ∈ ptsIn p (RingHom.id ℂ) W, ev p (RingHom.id ℂ) W a y = ev p (RingHom.id ℂ) W b y) → a = b := by
  intro Y p D hp W a b hab
  have hsm : Smooth p := SmoothOfRelativeDimension.smooth D p
  have hred : IsReduced Y :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ Y p hsm).1
  refine TopCat.Presheaf.IsSheaf.section_ext Y.IsSheaf fun x hx => ?_
  obtain ⟨U, hU, hxU, hUW⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (show x ∈ W from hx)
  replace hU : IsAffineOpen U := hU
  refine ⟨U, hUW, hxU, ?_⟩
  have hc : (algX p U).FiniteType := by
    have h1 : (p.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    exact h1.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).2)
  let : Algebra ℂ Γ(Y, U) := (algX p U).toAlgebra
  have : Algebra.FiniteType ℂ Γ(Y, U) := hc
  change resG Y hUW a = resG Y hUW b
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_algHom_complex _ fun e => ?_
  have hm := ofHom_mem (p := p) (σ := RingHom.id ℂ) hU e.toRingHom (fun c => e.commutes c)
  have h := hab _ (ptsIn_mono hUW hm)
  rw [← ev_res hUW hm, ← ev_res hUW hm, ev_ofHom, ev_ofHom] at h
  rw [map_sub, sub_eq_zero]
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOrEqOfUnderMaximalRealSubfieldEqCMField
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.FiberTwo

theorem eq_or_eq_of_under_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (w u u' : Pl E) (hu : u ≠ w)
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)))
    (h' : u'.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u' = w ∨ u' = u := by
  have hr := Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E
  have hc := IsCMField.complexConj_ne_one (K := E)
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr hc w u).1 h with h1 | h1
  · exact absurd h1 hu
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E) hr hc w u').1 h' with h2 | h2
  · exact Or.inl h2
  · exact Or.inr ((GlobalTheory.Mem.Chr.existsUnique_conjPl _ w).unique h2 h1)

end GlobalTheory.BCT.FiberTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalRingOfVarietyPoint
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory

theorem essFiniteType_of_isLocModel : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K),
    IsLocModel (algebraMap ℂ K) R → Algebra.EssFiniteType ℂ K := by
  intro K _ _ R h
  letI : Algebra ℂ R := ((algebraMap ℂ K).codRestrict R h.const_mem).toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := h.essFiniteType
  haveI : IsScalarTower ℂ R K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsFractionRing R K := IsFractionRing.of_field R K fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := h.frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by
      show z = a / b
      rw [eq_div_iff hb0, e]⟩
  haveI : Algebra.EssFiniteType R K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors R)
  exact Algebra.EssFiniteType.comp ℂ R K

end GlobalTheory
end

