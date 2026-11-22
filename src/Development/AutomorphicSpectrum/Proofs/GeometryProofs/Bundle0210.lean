import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0208
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwistedGramMatricesMatch
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0071
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0033
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricNumberZeroFinrank
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg

open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointResidue (exists_homog exists_homog_mem aeval_div)
open GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionsNonzero (chartMono isMultiHomog_chartMono mem_mCoordIdeal_of_aeval_eq_zero)
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart (chartMono_notMem)
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_X fracHom fracHom_apply fracHom_eq_zero_iff mem_locRing_iff div_mem_locRing)

theorem length_toNat_of_addEquiv {M κ : Type*} [AddCommGroup M] [Module ℤ M] [Field κ] (e : M ≃+ κ)
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) κ] :
    (Module.length ℤ M).toNat = Module.finrank (ZMod p) κ := by
  let l : M ≃ₗ[ℤ] κ := { e with map_smul' := fun n x => by simpa using map_intCast_smul e ℤ ℤ n x }
  rw [l.length_eq, Module.length_eq_of_surjective (R := ZMod p) (S := ℤ) (M := κ)
    (fun z => ⟨(z.cast : ℤ), by simp⟩), Module.length_eq_rank, Cardinal.toNat_toENat]
  rfl

attribute [local instance 2000] Ring.toIntAlgebra

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)]
variable {P W : Ideal (MRing J)} [P.IsPrime] [W.IsPrime]

def dehom (hPW : P ≤ W) (c : ∀ k, J k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) : MRing J →+* locRing P W := by
  classical
  exact (aeval (R := ℤ) fun p : Σ k, J k =>
    (⟨fracHom P (X p) / fracHom P (X ⟨p.1, c p.1⟩),
      div_mem_locRing hPW (homog_X p.1 p.2) (homog_X p.1 (c p.1)) (hc p.1)⟩ : locRing P W)).toRingHom

theorem frac_chart_ne_zero (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) :
    fracHom P (X ⟨k, c k⟩ : MRing J) ≠ 0 := fun h =>
  hc k (hPW (fracHom_eq_zero_iff.1 h))

theorem coe_dehom (hPW : P ≤ W) (c : ∀ k, J k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (f : MRing J) :
    ((dehom hPW c hc f : locRing P W) : FractionRing (MRing J ⧸ P)) =
      aeval (fun p : Σ k, J k => fracHom P (X p) / fracHom P (X ⟨p.1, c p.1⟩)) f := by
  classical
  have h : (locRing P W).subtype.comp (dehom hPW c hc) =
      (aeval (R := ℤ) (fun p : Σ k, J k => fracHom P (X p) / fracHom P (X ⟨p.1, c p.1⟩))).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => ?_
    simp [dehom]
  exact RingHom.congr_fun h f

theorem fracHom_eq_aeval (f : MRing J) :
    fracHom P f = aeval (fun p : Σ k, J k => fracHom P (X p)) f := by
  have h : fracHom P = (aeval (R := ℤ) (fun p : Σ k, J k => fracHom P (X p))).toRingHom :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by simp
  exact RingHom.congr_fun h f

theorem dehom_form (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) {G : MRing J} {n : B → ℕ}
    (hG : IsMultiHomog G n) :
    ((dehom hPW c hc G : locRing P W) : FractionRing (MRing J ⧸ P)) * fracHom P (chartMono c n) = fracHom P G := by
  have hD : fracHom P (chartMono c n) = ∏ k, fracHom P (X ⟨k, c k⟩ : MRing J) ^ n k := by
    simp [chartMono, map_prod, map_pow]
  have hD0 : ∏ k, fracHom P (X ⟨k, c k⟩ : MRing J) ^ n k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (frac_chart_ne_zero hPW hc k)
  rw [coe_dehom, aeval_div (fun p : Σ k, J k => fracHom P (X p)) c G n hG, hD, ← fracHom_eq_aeval,
    mul_assoc, inv_mul_cancel₀ hD0, mul_one]

theorem dehom_X_chart (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) :
    dehom hPW c hc (X ⟨k, c k⟩) = 1 := by
  apply Subtype.ext
  rw [coe_dehom, aeval_X]
  exact div_self (frac_chart_ne_zero hPW hc k)

variable [IsLocalRing (locRing P W)]

theorem dehom_mem_maximalIdeal_iff (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    {G : MRing J} {n : B → ℕ} (hG : IsMultiHomog G n) :
    dehom hPW c hc G ∈ maximalIdeal (locRing P W) ↔ G ∈ W :=
  regularityLocalFlat_holds.mem_maximalIdeal_iff hPW _ hG (isMultiHomog_chartMono c n)
    (chartMono_notMem ‹W.IsPrime› hc n) (dehom_form hPW hc hG)

def theta (hPW : P ≤ W) (c : ∀ k, J k) (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) :
    MRing J →+* ResidueField (locRing P W) :=
  (residue (locRing P W)).comp (dehom hPW c hc)

theorem theta_eq_zero_iff (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    {G : MRing J} {n : B → ℕ} (hG : IsMultiHomog G n) : theta hPW c hc G = 0 ↔ G ∈ W :=
  (residue_eq_zero_iff _).trans (dehom_mem_maximalIdeal_iff hPW hc hG)

theorem theta_X_chart (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) :
    theta hPW c hc (X ⟨k, c k⟩) = 1 := by
  simp [theta, dehom_X_chart]

theorem ker_theta (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    (hWh : IsMultiHomogIdeal W) :
    RingHom.ker (theta hPW c hc) = W ⊔ Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) := by
  set I0 := Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) with hI0
  have hIk : I0 ≤ RingHom.ker (theta hPW c hc) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    simp [SetLike.mem_coe, RingHom.mem_ker, theta_X_chart]
  apply le_antisymm
  · intro f hf
    have hχ : ∀ k, Ideal.Quotient.mk I0 (X ⟨k, c k⟩) = 1 := fun k => by
      rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨k, rfl⟩
    obtain ⟨n, G, hG, hGf⟩ := exists_homog _ c hχ f
    have hd : G - f ∈ I0 := Ideal.Quotient.eq.mp hGf
    have hG0 : G ∈ RingHom.ker (theta hPW c hc) := by simpa using add_mem (hIk hd) hf
    have hGW : G ∈ W := (theta_eq_zero_iff hPW hc hG).1 hG0
    have e : f = G - (G - f) := by ring
    rw [e]
    exact sub_mem (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hd)
  · refine sup_le ?_ hIk
    intro f hf
    obtain ⟨n, G, hGW, hG, e⟩ := exists_homog_mem (theta hPW c hc) c (theta_X_chart hPW hc) hWh hf
    rw [RingHom.mem_ker, ← e]
    exact (theta_eq_zero_iff hPW hc hG).2 hGW

theorem theta_surjective (hPW : P ≤ W) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    (hmax : (RingHom.ker (theta hPW c hc)).IsMaximal) : Function.Surjective (theta hPW c hc) := by
  intro z
  obtain ⟨x, rfl⟩ := residue_surjective z
  obtain ⟨u, v, a, hu, hv, hvW, hx⟩ := (mem_locRing_iff hPW).1 x.2
  have hvk : v ∉ RingHom.ker (theta hPW c hc) := fun h => hvW ((theta_eq_zero_iff hPW hc hv).1 h)
  obtain ⟨g, i, hi, hgi⟩ := hmax.exists_inv hvk
  have hD0 : fracHom P (chartMono c a) ≠ 0 := fun h =>
    chartMono_notMem ‹W.IsPrime› hc a (hPW (fracHom_eq_zero_iff.1 h))
  have h1 : dehom hPW c hc u = x * dehom hPW c hc v := by
    apply Subtype.ext
    apply mul_right_cancel₀ hD0
    rw [dehom_form hPW hc hu, ← hx, Subring.coe_mul, mul_assoc, dehom_form hPW hc hv]
  have h2 : theta hPW c hc g * theta hPW c hc v = 1 := by
    have := congrArg (theta hPW c hc) hgi
    rwa [map_add, map_mul, RingHom.mem_ker.1 hi, add_zero, map_one] at this
  refine ⟨u * g, ?_⟩
  have h3 : theta hPW c hc u = residue _ x * theta hPW c hc v := by
    simp only [theta, RingHom.comp_apply, h1, map_mul]
  rw [map_mul, h3, mul_assoc, mul_comm (theta hPW c hc v), h2, mul_one]

omit [P.IsPrime] [W.IsPrime] in

def chartHom {K : Type} [Field K] (w : (Σ k, J k) → K) (c : ∀ k, J k) : MRing J →+* chartRingZ w c :=
  (aeval (R := ℤ) fun p : Σ k, J k =>
    (⟨w p / w ⟨p.1, c p.1⟩, Algebra.subset_adjoin ⟨p, rfl⟩⟩ : chartRingZ w c)).toRingHom

theorem coe_chartHom {K : Type} [Field K] (w : (Σ k, J k) → K) (c : ∀ k, J k) (f : MRing J) :
    ((chartHom w c f : chartRingZ w c) : K) = aeval (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩) f := by
  have h : (chartRingZ w c).val.toRingHom.comp (chartHom w c) =
      (aeval (R := ℤ) (fun p : Σ k, J k => w p / w ⟨p.1, c p.1⟩)).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => ?_
    simp [chartHom]
  exact RingHom.congr_fun h f

theorem chartHom_surjective {K : Type} [Field K] (w : (Σ k, J k) → K) (c : ∀ k, J k) :
    Function.Surjective (chartHom w c) := by
  rintro ⟨r, hr⟩
  rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval] at hr
  obtain ⟨f, hf⟩ := (AlgHom.mem_range _).mp hr
  exact ⟨f, Subtype.ext ((coe_chartHom w c f).trans hf)⟩

theorem ker_chartHom_le {K : Type} [Field K] {w : (Σ k, J k) → K} {c : ∀ k, J k} {W : Ideal (MRing J)}
    (hPW : mCoordIdeal w ≤ W) (hwc : ∀ k, w ⟨k, c k⟩ ≠ 0) :
    RingHom.ker (chartHom w c) ≤ W ⊔ Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) := by
  set I0 := Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing J) - 1) with hI0
  have hspan : I0 ≤ RingHom.ker (chartHom w c) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    apply Subtype.ext
    rw [coe_chartHom]
    simp [hwc k]
  intro f hf
  have hχ : ∀ k, Ideal.Quotient.mk I0 (X ⟨k, c k⟩) = 1 := fun k => by
    rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
    exact Ideal.subset_span ⟨k, rfl⟩
  obtain ⟨n, G, hG, hGf⟩ := exists_homog _ c hχ f
  have hd : G - f ∈ I0 := Ideal.Quotient.eq.mp hGf
  have hG0 : chartHom w c G = 0 := by simpa using add_mem (hspan hd) hf
  have hGv : aeval w G = 0 := by
    have h1 := congrArg Subtype.val hG0
    rw [coe_chartHom, aeval_div w c G n hG] at h1
    exact (mul_eq_zero.1 h1).resolve_right
      (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hwc k)))
  have hGW : G ∈ W := hPW (mem_mCoordIdeal_of_aeval_eq_zero w hG hGv)
  have e : f = G - (G - f) := by ring
  rw [e]
  exact sub_mem (Ideal.mem_sup_left hGW) (Ideal.mem_sup_right hd)

theorem ker_theta_isMaximal {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    [IsFunctionField (ZMod p) K] {w : (Σ k, J k) → K} {W : Ideal (MRing J)} [(mCoordIdeal w).IsPrime] [W.IsPrime]
    [IsLocalRing (locRing (mCoordIdeal w) W)] (hbir : Birational w) (hPW : mCoordIdeal w ≤ W)
    {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (hWh : IsMultiHomogIdeal W)
    {k : B} {i : J k} (hw : w ⟨k, i⟩ ≠ 0) (hX : (X ⟨k, i⟩ : MRing J) ∈ W) :
    (RingHom.ker (theta hPW c hc)).IsMaximal := by
  have hwc : ∀ k, w ⟨k, c k⟩ ≠ 0 := fun k h => hc k (hPW ((X_mem_iff w k _).2 h))
  have hs := chartHom_surjective w c
  have hker := ker_theta hPW hc hWh
  have hle : RingHom.ker (chartHom w c) ≤ RingHom.ker (theta hPW c hc) := by
    rw [hker]
    exact ker_chartHom_le hPW hwc
  haveI : (RingHom.ker (theta hPW c hc)).IsPrime := RingHom.ker_isPrime _
  have hq : (Ideal.map (chartHom w c) (RingHom.ker (theta hPW c hc))).IsPrime :=
    Ideal.map_isPrime_of_surjective hs hle
  have h0 : Ideal.map (chartHom w c) (RingHom.ker (theta hPW c hc)) ≠ ⊥ := by
    intro h
    have hx : (X ⟨k, i⟩ : MRing J) ∈ RingHom.ker (theta hPW c hc) := by
      rw [hker]
      exact Ideal.mem_sup_left hX
    have h1 := Ideal.mem_map_of_mem (chartHom w c) hx
    rw [h, Ideal.mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    rw [coe_chartHom, aeval_X] at h2
    exact div_ne_zero hw (hwc k) h2
  haveI := chart_prime_isMaximal (p := p) w hbir c hwc _ hq h0
  have h3 := Ideal.comap_isMaximal_of_surjective (chartHom w c) hs
    (K := Ideal.map (chartHom w c) (RingHom.ker (theta hPW c hc)))
  have hle' : Ideal.comap (chartHom w c) ⊥ ≤ RingHom.ker (theta hPW c hc) := hle
  rwa [Ideal.comap_map_of_surjective (chartHom w c) hs, sup_eq_left.2 hle'] at h3

theorem geoNum_zero_eq_finrank : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (k : B) (c : J k), w ⟨k, c⟩ ≠ 0 → ∀ W ∈ divSupp (mCoordIdeal w) (X ⟨k, c⟩), ∀ (b : Fin 0 → B → ℤ) [IsLocalRing (locRing (mCoordIdeal w) W)] [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], geoNum 0 W b = (Module.finrank (ZMod p) (ResidueField (locRing (mCoordIdeal w) W)) : ℤ) := by
  intro B _ J _ p _ K _ _ _ w hbir k i hw W hW b _ _
  classical
  obtain ⟨hmin, hrel⟩ := hW
  haveI hWp : W.IsPrime := hmin.1.1
  haveI hPp : (mCoordIdeal w).IsPrime := RingHom.ker_isPrime _
  have hPW : mCoordIdeal w ≤ W := le_sup_left.trans hmin.1.2
  have hX : (X ⟨k, i⟩ : MRing J) ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hWh : IsMultiHomogIdeal W :=
    isMultiHomogIdeal_of_mem_minimalPrimes (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal w)
      (homog_X k i) hmin
  have hc : ∀ k, (X ⟨k, (hrel k).choose⟩ : MRing J) ∉ W := fun k => (hrel k).choose_spec
  have hmax := ker_theta_isMaximal (p := p) hbir hPW hc hWh hw hX
  have hsurj := theta_surjective hPW hc hmax
  rw [geoNum, dif_pos hrel]
  congr 1
  exact length_toNat_of_addEquiv
    ((Ideal.quotEquivOfEq (ker_theta hPW hc hWh).symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)).toAddEquiv p

end GlobalTheory.CompanionTheory.Ar.GeoDeg.ResDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermFrobeniusTorsionSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf.PeOne

theorem homAt_comp' {X : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X) {A B C : Type} [CommRing A] [Algebra S A]
    [CommRing B] [Algebra S B] [CommRing C] [Algebra S C] (f : A →ₐ[S] B) (g : B →ₐ[S] C) :
    homAt x0 (g.comp f) = homAt x0 g ≫ homAt x0 f := by
  ext1
  simp only [homAt, spMap, Over.comp_left, Over.homMk_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem jetSubstP_mk_X {S : Type} [CommRing S] {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (i : κ) :
    jetSubstP m φ (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (φ i - MvPolynomial.C (MvPolynomial.constantCoeff (φ i))) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]

theorem jetCopy_mkX {S : Type} [CommRing S] {d n : ℕ} (m : ℕ) (i : Fin n) (j : Fin d) :
    jetCopy (S := S) d m i (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, j)) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval _ (MvPolynomial.X _)) = _
  rw [MvPolynomial.aeval_X]

theorem constantCoeff_psIn {S : Type} [CommRing S] {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n')
    (f : MvPowerSeries (Fin n × Fin d) S) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPolynomial.constantCoeff (psIn d m r f) = 0 := by
  unfold psIn
  rw [MvPolynomial.constantCoeff_rename, psTrunc, map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [MvPolynomial.constantCoeff_monomial]
  split_ifs with h
  · subst h
    simpa using hf
  · rfl

end GlobalTheory.CompanionTheory.Ar.Coc.Pf.PeOne

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

open PeOne in

theorem peG_act_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ), (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) ^ p = 1 → ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)) (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val (peG t x d g.x g.e (p + m + 1) ![fun j => psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (homAt x (jq w p m)).left z J = 1 := by
  intro E _ _ _ H _ hstar X0 t k _ p _ _ x d g w m hp z J hJ
  have hring : (jq w p m).comp (jetSubstP (p + m + 1) fun q : Fin 2 × Fin d =>
      (![fun j => psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j),
        fun j => MvPolynomial.X ((1 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) k) q.1 q.2) =
      ((jq w p m).comp (jetCopy d (p + m + 1) (1 : Fin 2))).comp (jetSubstP (p + m + 1) fun q : Fin 2 × Fin d =>
        (![fun _ => 0, fun j => MvPolynomial.X ((0 : Fin 1), j)] : Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) k)
          q.1 q.2) := by
    refine Ideal.Quotient.algHom_ext k (MvPolynomial.algHom_ext fun q => ?_)
    obtain ⟨a, j⟩ := q
    show _ = _
    simp only [AlgHom.comp_apply]
    refine Eq.trans (congrArg (jq w p m) (jetSubstP_mk_X _ _ _)) ?_
    refine Eq.trans ?_ (congrArg (fun u => jq w p m (jetCopy d (p + m + 1) (1 : Fin 2) u)) (jetSubstP_mk_X _ _ _)).symm
    fin_cases a
    · have h0 := GlobalTheory.T.germ_frobenius_torsion_jet E H hstar X0 t k p x d g w m hp j
      have hc := constantCoeff_psIn (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j) (g.B.A.const _ _)
      simp [hc, h0]
    · simp [jetCopy_mkX]
  have hcomp := congrArg (fun f => (homAt x f).left) hring
  simp only [homAt_comp', Over.comp_left] at hcomp
  refine (val_pull hJ _ _ _).trans ?_
  rw [hcomp]
  refine (val_pull hJ _ _ _).symm.trans ?_
  exact (val_corr hJ (g.axes _).1 _).trans (val_one _)

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistEigenCompat
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_component_twist_eigen_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      m.φ ≫ k.φ ≫ A.m.φ = u.φ ≫ Y.m.φ → mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ →
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ →
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) → (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) → (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) → (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) →
      ∀ z : Sp ℂ ⟶ A'.X, A'.Interior z → ∀ (r : ℕ) (b : Fin r → A.Li) (Γ : Matrix (Fin r) (Fin r) ℂ),
        M₁.GramAt t.PP.L z b Γ ↔ A'.M.GramAt A'.t.PP.L z (fun i => φ (b i)) Γ := by
  first | exact @PositivityTheory.UnitarySelfGeneration.twisted_gram_matrices_match | exact PositivityTheory.UnitarySelfGeneration.twisted_gram_matrices_match
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalPointSpecializesComponent
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.Coef

section General

variable {X : Scheme.{0}} {K R : Type} [CommRing K] [CommRing R] [IsLocalRing R]

def cst (g : X ⟶ Sp K) (x : X) : K →+* X.presheaf.stalk x :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp g.appTop.hom).comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

theorem stalkClosedPointTo_germ_top (z : Sp R ⟶ X) (t : Γ(X, ⊤)) :
    (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom t) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom t) := by
  have h : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  exact congrArg (fun q => q.hom t) h

theorem val_cst (z : Sp R ⟶ X) (g : X ⟶ Sp K) (φ : K →+* R) (h : z ≫ g = spMap φ) (k : K) :
    (Scheme.stalkClosedPointTo z).hom (cst g (centre z) k) = φ k := by
  show (Scheme.stalkClosedPointTo z).hom ((X.presheaf.germ ⊤ (centre z) trivial).hom
    (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k))) = φ k
  rw [stalkClosedPointTo_germ_top]
  have h2 : z.appTop.hom (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k)) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) := by
    have h' : z ≫ g = Spec.map (CommRingCat.ofHom φ) := h
    rw [← h']; simp only [Scheme.Hom.comp_appTop]; rfl
  rw [h2]
  have h3 := congrArg (fun q => q.hom k) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (φ k) =
      (Spec.map (CommRingCat.ofHom φ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) := h3
  rw [← h3']
  simp

variable {Ω : Type} [Field Ω]

theorem genMap_cst (ξ : Sp Ω ⟶ X) (g : X ⟶ Sp K) (φ : K →+* Ω) (h : ξ ≫ g = spMap φ) (p : Cpt ξ) (k : K) :
    genMap ξ p (cst g p.1 k) = φ k := by
  have h1 : genMap ξ p (cst g p.1 k) = (Scheme.stalkClosedPointTo ξ).hom (cst g (centre ξ) k) :=
    congrArg (Scheme.stalkClosedPointTo ξ).hom
      (X.presheaf.germ_stalkSpecializes_apply (show p.1 ∈ (⊤ : X.Opens) from trivial) p.2 _)
  rw [h1, val_cst ξ g φ h]

theorem exists_lift {ξ : Sp Ω ⟶ X} {F : Type} [Field F] [NumberField F] (hξ : IsCptGen ξ) (hN : NormalCpt ξ)
    (p : Cpt ξ) (inc : F →+* Ω) (hq : ∀ n : ℕ, 0 < n → IsUnit (n : X.presheaf.stalk p.1)) :
    ∃ κ : F →+* X.presheaf.stalk p.1, (genMap ξ p).comp κ = inc := by
  haveI : CharZero Ω := charZero_of_injective_ringHom inc.injective
  have hinv : ∀ n : ℕ, 0 < n → ((n : Ω))⁻¹ ∈ regAt ξ p := by
    intro n hn
    obtain ⟨u, hu⟩ := hq n hn
    refine ⟨(u⁻¹ : _ˣ), ?_⟩
    have h1 : genMap ξ p u = (n : Ω) := by rw [hu, map_natCast]
    have h2 : genMap ξ p (u⁻¹ : _ˣ) * genMap ξ p u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [h1] at h2
    exact eq_inv_of_mul_eq_one_left h2
  have hmem : ∀ r : ℚ, Rat.castHom Ω r ∈ regAt ξ p := by
    intro r
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
    exact mul_mem (intCast_mem _ _) (hinv r.den r.den_pos)
  let ψ : ℚ →+* regAt ξ p := (Rat.castHom Ω).codRestrict _ hmem
  have hint : ∀ a : F, inc a ∈ regAt ξ p := by
    intro a
    refine hN p _ ⟨(minpoly ℚ a).map ψ, (minpoly.monic (Algebra.IsIntegral.isIntegral a)).map ψ, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (regAt ξ p) Ω).comp ψ = inc.comp (algebraMap ℚ F) := Subsingleton.elim _ _
    rw [e, ← Polynomial.hom_eval₂]
    have := minpoly.aeval ℚ a
    rw [Polynomial.aeval_def] at this
    rw [this, map_zero]
  have hb : Function.Bijective (genMap ξ p).rangeRestrict :=
    ⟨fun a b hab => hξ.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩
  refine ⟨(RingEquiv.ofBijective _ hb).symm.toRingHom.comp (inc.codRestrict (genMap ξ p).range hint), ?_⟩
  ext a
  exact congrArg Subtype.val ((RingEquiv.ofBijective _ hb).apply_symm_apply (inc.codRestrict (genMap ξ p).range hint a))

end General

theorem exists_coef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (T : Type) [CommRing T] [IsLocalRing T] (y : Sp T ⟶ Xo.XF c) (c₀ : c.F →+* T), y ≫ pullback.snd _ _ = spMap c₀ → centre y ∈ U → ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))), (genMap (Z.ξ₀ ≫ Y.j) ⟨_, h⟩).comp κ = Z.inc ∧ (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = c₀ := by
  intro E _ _ _ H D l Xo c U O _ β Y Z T _ _ y c₀ hy hU
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have h0 : genPt Z.ξ₀ ⤳ centre y := (Z.closure _).1 hU
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := h0.map Y.j.continuous
  refine ⟨h, ?_⟩
  have hN : NormalCpt (Z.ξ₀ ≫ Y.j) := XR.normalCpt_of_isCptGen Z.gen Y.normal
  have hq : ∀ n : ℕ, 0 < n → IsUnit (n : Y.X.presheaf.stalk (centre (y ≫ Y.j))) := by
    intro n hn
    haveI : IsLocalHom (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom := Scheme.isLocalHom_stalkClosedPointTo _
    have e : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom (n : Y.X.presheaf.stalk (centre (y ≫ Y.j))) =
        c₀ (n : c.F) := (map_natCast _ n).trans (map_natCast c₀ n).symm
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom _
      ((congrArg IsUnit e).mpr ((IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')).map c₀))
  obtain ⟨κ, hκ⟩ := exists_lift Z.gen hN ⟨centre (y ≫ Y.j), h⟩ Z.inc hq
  refine ⟨κ, hκ, ?_⟩
  let π := genMap Z.ξ₀ ⟨centre y, h0⟩
  let s : c.F →+* (Xo.XF c).presheaf.stalk (centre y) := (Y.j.stalkMap (centre y)).hom.comp κ
  let t : c.F →+* (Xo.XF c).presheaf.stalk (centre y) := cst (pullback.snd _ _) (centre y)
  have hD : GlobalTheory.CompanionTheory.Ar.Dominates Z.ξ₀ (Z.ξ₀ ≫ Y.j) Y.j (RingHom.id Z.Ω) := by
    show Z.ξ₀ ≫ Y.j = Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) ≫ Z.ξ₀ ≫ Y.j
    have e : CommRingCat.ofHom (RingHom.id Z.Ω) = 𝟙 _ := rfl
    rw [e, Spec.map_id, Category.id_comp]
  have hs : π.comp s = Z.inc := by
    ext a
    exact (PullReg.stalkMap_comp_genMap hD ⟨centre y, h0⟩ h (κ a)).trans (congrArg (fun f => f a) hκ)
  have ht : π.comp t = Z.inc := by
    ext a
    exact genMap_cst Z.ξ₀ (pullback.snd _ _) Z.inc Z.over_inc ⟨centre y, h0⟩ a
  have est : s = t := GlobalTheory.T.number_field_maps_local_ring_unique c.F _ Z.Ω π s t (hs.trans ht.symm)
  have e1 : (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = (Scheme.stalkClosedPointTo y).hom.comp s := by
    rw [Scheme.stalkClosedPointTo_comp]
    rfl
  rw [e1, est]
  ext a
  exact val_cst y (pullback.snd _ _) c₀ hy a

end GlobalTheory.CompanionTheory.Ar.LocFn.Coef
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivOfSectionOfLocallyTriv
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem triv_of_section_of_locally_triv : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X), e ≫ p = 𝟙 S → (∀ U : S.Opens, IsIso (p.app U)) → ∀ M : LB X, M.IsLB → GlobalTheory.AbLaw.Triv (M.pull e) → (∀ x : S, ∃ U : S.Opens, x ∈ U ∧ GlobalTheory.AbLaw.Triv (M.pull (p ⁻¹ᵁ U).ι)) → GlobalTheory.AbLaw.Triv M :=
  fun _ _ p e he hp _ hM h₀ loc =>
    GlobalTheory.CubeGlue.triv_of_locally_triv hM p e he (GlobalTheory.CubeGlue.surjective_restrict p hp) h₀ loc

end GlobalTheory.CompanionTheory.Ar.Approx
end

