import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0906
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCentralIdempotentOfGoodSeriesIdempotent
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0059
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0203
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugacyClassPartEqWeightMulKottwitzPointSum
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0177
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefInjective
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftScalarCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Places

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem primeToHost (h : R.toLevCh.Is A.μ0) : AdelicScalarSectionLift.PrimeToHost R := by
  intro PP hP
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  refine GlobalTheory.CoverHalf.not_mem_of_coprime PP.isPrime.ne_top (a := D.host.g k) ?_ (R.C.P.overP hk)
  have hc := D.ntypes.g_cond k
  have h1 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc, Nat.gcd_one_left]
  refine Nat.Coprime.mul_right h1 ?_
  refine (D.host.ccK_coprime _ ?_).symm
  simp [D.host.g_level k]

end Places

section Coord

variable {V : HSp D} (c : CoefA V) {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

def cx (ℓ : c.W →ₗ[ℂ] ℂ) : (Bridge.Gf V → c.W) →ₗ[ℂ] (GA D V → ℂ) := ℓ.compLeft (GA D V) ∘ₗ c.ext

theorem cx_apply (ℓ : c.W →ₗ[ℂ] ℂ) (f : Bridge.Gf V → c.W) (h : GA D V) : cx c ℓ f h = ℓ (c.ρ h⁻¹ (f (fin V h))) := rfl

variable {c}

end Coord

theorem adjoint_idem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ρ : Representation ℂ G H) (hu : ∀ g x, ‖ρ g x‖ = ‖x‖) {a : G → ℂ} (ha : GoodBasisCentralIdempotents.IsCentralIdem a) {x : H}
    (hx : (∑ g, a g • ρ g) x = x) (y : H) : ⟪x, (∑ g, a g • ρ g) y⟫_ℂ = ⟪x, y⟫_ℂ := by
  set E : H →ₗ[ℂ] H := ∑ g, a g • ρ g with hE
  have hin : ∀ g u w, ⟪ρ g u, ρ g w⟫_ℂ = ⟪u, w⟫_ℂ := fun g => LinearIsometry.inner_map_map ⟨ρ g, hu g⟩
  have hcomm : ∀ g u, E (ρ g u) = ρ g (E u) := fun g u => by
    simp only [hE, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, ← Module.End.mul_apply, ← map_mul]
    refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun h => ?_).symm
    show _ = a (g * h * g⁻¹) • ρ (g * h * g⁻¹ * g) u
    rw [ha.1, inv_mul_cancel_right]
  have hidem : ∀ u, E (E u) = E u := fun u => by
    have h1 : E u = ∑ g, ∑ h, (a h * a (h⁻¹ * g)) • ρ g u := by
      simp only [← Finset.sum_smul, ha.2, hE, LinearMap.sum_apply, LinearMap.smul_apply]
    have h2 : E (E u) = ∑ h, ∑ g, (a h * a g) • ρ h (ρ g u) := by
      simp only [hE, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    rw [h2, h1, Finset.sum_comm (f := fun g h => (a h * a (h⁻¹ * g)) • ρ g u)]
    refine Finset.sum_congr rfl fun h _ => Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

  have hadj : ∀ u, LinearMap.adjoint E u = ∑ g, star (a g) • ρ g⁻¹ u := fun u => by
    refine ext_inner_right ℂ fun w => ?_
    rw [LinearMap.adjoint_inner_left, sum_inner, hE, LinearMap.sum_apply, inner_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, inner_smul_right, inner_smul_left, ← hin g (ρ g⁻¹ u), ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
    simp
  have hfix : E (LinearMap.adjoint E x) = LinearMap.adjoint E x := by
    rw [hadj, map_sum]
    simp only [map_smul, hcomm, hx]

  have hz : LinearMap.adjoint E x - x = 0 := by
    rw [← inner_self_eq_zero (𝕜 := ℂ)]
    have h1 : E (LinearMap.adjoint E x - x) = LinearMap.adjoint E x - x := by rw [map_sub, hfix, hx]
    rw [inner_sub_left, LinearMap.adjoint_inner_left, h1, sub_self]
  rw [← LinearMap.adjoint_inner_left, sub_eq_zero.1 hz]

end GlobalTheory.LiftScalarCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothProjVarietyCompactManifold
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory

theorem cxPts_var_compact_manifold : ∀ Y : Var ℂ, CompactSpace (CxPts Y.str (RingHom.id ℂ)) ∧ T2Space (CxPts Y.str (RingHom.id ℂ)) ∧ SecondCountableTopology (CxPts Y.str (RingHom.id ℂ)) ∧ ∃ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A := fun Y =>
  haveI : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace _ Y.isProjOver
  ⟨this, t2Space_cxPts_of_isProjOver _ Y.isProjOver, secondCountableTopology_of_isProjOver _ Y.isProjOver,
    (AnRead.all Y.str (RingHom.id ℂ) Y.dim).finAtlas, AnRead.isAlgAtlas_finAtlas _⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugacyClassPartEqWeightMulKottwitzPointSumStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugacyClassPart_eq_weight_mul_kottwitzPointSum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y₀ : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0 → ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re → FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z) → ∀ y₀ : grp G β, ∑ᶠ o : MulAction.orbitRel.Quotient (Subgroup.centralizer {y₀}) (GlobalTheory.CxUnfold.Ys G v β x t hx Kf K'), ((Nat.card (MulAction.stabilizer (grp G β) (Quotient.out o) ⊓ Subgroup.centralizer {y₀} : Subgroup (grp G β)) : ℕ) : ℂ)⁻¹ * GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (Quotient.out o) y₀ = if (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y₀ z) then wt (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * pointSum ((toAfF G β x t hx).comp (Subgroup.centralizer {y₀}).subtype) ((toP1 G β).comp (Subgroup.centralizer {y₀}).subtype) (MonoidHom.id (Gr G 1)) Kf K' (toAfF G β x t hx y₀) (toP1 G β y₀) f f' else 0 := by
  first | (exact @GlobalTheory.CxUnfoldGen.cls_eq_of_uniq) | (exact GlobalTheory.CxUnfoldGen.cls_eq_of_uniq) | (intros; apply GlobalTheory.CxUnfoldGen.cls_eq_of_uniq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateCurvePointAdditionCompat
section
noncomputable section

namespace GlobalTheory.UnrEuler.ConjVal

open NumberField IsDedekindDomain GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UnrEuler Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors TensorProduct
open Formalism.L2.Host (aboveF)
open GlobalTheory.CuspRep (conjSrc conjLoc conjFin conjLoc_spec conjPl_conjSrc conjSrc_injective)
open GlobalTheory.Mem.Chr (ConjPl)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem count_map {σ : E →ₐ[F] E} {c : E ≃+* E} (hc : ∀ x, σ x = c x) {v v' : HeightOneSpectrum (𝓞 E)}
    (h : ConjPl c v v') {J : Ideal (𝓞 E)} (hJ : J ≠ 0) :
    FractionalIdeal.count E v' (conjI σ (J : FractionalIdeal (𝓞 E)⁰ E)) =
      FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E) := by
  classical
  have e : conjI σ (J : FractionalIdeal (𝓞 E)⁰ E) = (J.map (conjO σ) : Ideal (𝓞 E)) :=
    FractionalIdeal.extended_coeIdeal_eq_map _ _ _
  have hJ' : J.map (conjO σ) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.1 (e ▸ conjI_ne_zero σ (FractionalIdeal.coeIdeal_ne_zero.2 hJ))
  rw [e, FractionalIdeal.count_coe E _ hJ', FractionalIdeal.count_coe E _ hJ]
  congr 1
  have hm : Associates.mk J ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  have hm' : Associates.mk (J.map (conjO σ)) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  have key : ∀ k : ℕ, k ≤ (Associates.mk v'.asIdeal).count (Associates.mk (J.map (conjO σ))).factors ↔
      k ≤ (Associates.mk v.asIdeal).count (Associates.mk J).factors := by
    intro k
    rw [← Associates.prime_pow_dvd_iff_le hm' v'.associates_irreducible,
      ← Associates.prime_pow_dvd_iff_le hm v.associates_irreducible,
      ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
      Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
    have : (v'.asIdeal ^ k).comap (conjO σ) = v.asIdeal ^ k := by
      ext x
      rw [Ideal.mem_comap, ← HeightOneSpectrum.intValuation_le_pow_iff_mem,
        ← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E),
        ← HeightOneSpectrum.valuation_of_algebraMap (K := E), ← h, ← hc]
      rfl
    rw [this]
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

theorem count_conjI {σ : E →ₐ[F] E} {c : E ≃+* E} (hc : ∀ x, σ x = c x) {v v' : HeightOneSpectrum (𝓞 E)}
    (h : ConjPl c v v') {𝔠 : FractionalIdeal (𝓞 E)⁰ E} (h0 : 𝔠 ≠ 0) :
    FractionalIdeal.count E v' (conjI σ 𝔠) = FractionalIdeal.count E v 𝔠 := by
  obtain ⟨a, J, ha, hJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul 𝔠
  have ha' : Ideal.span {a} ≠ 0 := by rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hA := (FractionalIdeal.coeIdeal_ne_zero (K := E)).2 ha'
  have e : ((Ideal.span {a} : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * 𝔠 = J := by
    rw [hJ, FractionalIdeal.coeIdeal_span_singleton, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton,
      mul_inv_cancel₀ (by simpa using ha), FractionalIdeal.spanSingleton_one, one_mul]
  have hJ0 : J ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.1 (e ▸ mul_ne_zero hA h0)
  have h1 := count_map hc h hJ0
  rw [← e, conjI, FractionalIdeal.extended_mul, FractionalIdeal.count_mul E _ hA h0] at h1
  erw [FractionalIdeal.count_mul E _ (conjI_ne_zero σ hA) (conjI_ne_zero σ h0), count_map hc h ha'] at h1
  exact add_left_cancel h1

theorem sigR_locIdele {σ : E →ₐ[F] E} {c : E ≃+* E} (hc : ∀ x, σ x = c x) (w : HeightOneSpectrum (𝓞 E))
    (x : ((conjSrc c w).adicCompletion E)ˣ) :
    sigR (AF F) σ (locIdele F (conjSrc c w) x : AF F ⊗[F] E) =
      locIdele F w (Units.map (conjLoc c w).toMonoidHom x) := by
  classical
  rw [coe_locIdele, coe_locIdele, RingHom.map_add, RingHom.map_sub, RingHom.map_one, SplitVal.sigR_extZero,
    SplitVal.sigR_extZero, RingHom.map_one]
  congr 2
  rw [RingEquiv.eq_symm_apply, GlobalTheory.DefU.ClassFin.finAdEquiv_sigR σ c hc, RingEquiv.apply_symm_apply]
  refine FiniteAdeleRing.ext _ fun u => ?_
  change conjLoc c u (Neutral.B1.finiteSingle E (conjSrc c w) x (conjSrc c u)) = _
  by_cases e : u = w
  · subst e
    rw [finSingle_self, finSingle_self]
    rfl
  · rw [finSingle_ne e, finSingle_ne ((conjSrc_injective c).ne e), map_one]

theorem locChar_conjLoc {σ : E →ₐ[F] E} (hE : IsCMExt F E σ) {c : E ≃+* E} (hc : ∀ x, σ x = c x) {ν : Chr F E}
    (hν : ∀ x : (AF F)ˣ, ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) x) = 1)
    (w : HeightOneSpectrum (𝓞 E)) (x : ((conjSrc c w).adicCompletion E)ˣ) :
    locChar ν w (Units.map (conjLoc c w).toMonoidHom x) = (locChar ν (conjSrc c w) x)⁻¹ := by
  have e : Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E)
      (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (locIdele F (conjSrc c w) x)) =
      locIdele F (conjSrc c w) x * locIdele F w (Units.map (conjLoc c w).toMonoidHom x) :=
    Units.ext (by
      rw [Units.val_mul, ← sigR_locIdele hc]
      exact GlobalTheory.Doubling.algebraMap_norm_eq hE _)
  have k := hν (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (locIdele F (conjSrc c w) x))
  rw [e, map_mul] at k
  refine eq_inv_of_mul_eq_one_right ?_
  exact (map_mul Circle.toUnits _ _).symm.trans ((congrArg Circle.toUnits k).trans (map_one _))

theorem val_eq_inv {σ : E →ₐ[F] E} (hE : IsCMExt F E σ) {c : E ≃+* E} (hc : ∀ x, σ x = c x) {ν : Chr F E}
    (hν : ∀ x : (AF F)ˣ, ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) x) = 1)
    {w : HeightOneSpectrum (𝓞 E)} (hw : UnrAt ν w) : val ν w = (val ν (conjSrc c w))⁻¹ := by
  have h1 := Formalism.L2.Host.unif_spec (conjSrc c w)
  have h3 : val ν (conjSrc c w) = locChar ν (conjSrc c w) (Formalism.L2.Host.atFin _ (Formalism.L2.Host.unif (conjSrc c w))) := rfl
  rw [h3]
  generalize Formalism.L2.Host.atFin _ (Formalism.L2.Host.unif (conjSrc c w)) = x at h1
  have h4 : Formalism.L2.Host.IsUnifAt w (Units.map (conjLoc c w).toMonoidHom x) :=
    ((conjLoc_spec c w).2.2 x).trans h1
  rw [← hw.locChar_eq_val h4, locChar_conjLoc hE hc hν]

theorem idealVal_conjI : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ν : Chr F E, (∀ x : (AF F)ˣ, ν (Units.map (algebraMap (AF F) (AE F E) : AF F →* AE F E) x) = 1) → ∀ 𝔠 : FractionalIdeal (𝓞 E)⁰ E, 𝔠 ≠ 0 → (∀ w : HeightOneSpectrum (𝓞 E), FractionalIdeal.count E w 𝔠 ≠ 0 → UnrAt ν w) → idealVal ν (conjI σ 𝔠) = (idealVal ν 𝔠)⁻¹ := by
  intro F E _ _ _ _ _ σ hE ν hν 𝔠 h0 hu
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hE.2.2.2, hE.2.2.2, star_star]
  let c : E ≃+* E := RingEquiv.ofBijective (σ : E →+* E) (Function.Involutive.bijective hσ)
  have hc : ∀ x, σ x = c x := fun _ => rfl
  have hinv : Function.Involutive (conjSrc c) := fun w => by
    refine (GlobalTheory.CuspRep.eq_conjSrc fun x => ?_).symm
    rw [← conjPl_conjSrc c w, ← hc, ← hc, hσ]
  unfold idealVal
  rw [← finprod_inv_distrib, ← finprod_comp_equiv (hinv.toPerm _)]
  refine finprod_congr fun w => ?_
  change val ν (conjSrc c w) ^ FractionalIdeal.count E (conjSrc c w) (conjI σ 𝔠) = _
  have h1 := conjPl_conjSrc c (conjSrc c w)
  rw [hinv w] at h1
  rw [count_conjI hc h1 h0]
  by_cases hw : FractionalIdeal.count E w 𝔠 = 0
  · simp [hw]
  rw [val_eq_inv hE hc hν (hu w hw), inv_zpow, inv_inv]

end GlobalTheory.UnrEuler.ConjVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAt
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem contDiffAt_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ {f : CxPts X.str σ → ℝ} {y : CxPts X.str σ}, y ∈ e.source → CInfAt f y → ContDiffAt ℝ ∞ (fun v => f (e.symm v)) (e y) := by
  intro F _ σ X e he f y hy hf
  obtain ⟨W, ι, hι, g, Φ, O, hyW, hO, hgO, hΦ, hfeq⟩ := hf

  have hU : IsOpen (e.target ∩ e.symm ⁻¹' ptsIn X.str σ W) :=
    e.isOpen_inter_preimage_symm (GlobalTheory.CxPts.isOpen_ptsIn W)
  have hyU : e y ∈ e.target ∩ e.symm ⁻¹' ptsIn X.str σ W :=
    ⟨e.map_source hy, by rw [Set.mem_preimage, e.left_inv hy]; exact hyW⟩

  have hGc : ContDiffAt ℂ ∞ (fun v a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm v)) (e y) := by
    rw [contDiffAt_pi]
    intro a
    exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ hU (he W (g a))).contDiffAt
      (hU.mem_nhds hyU)

  have hΦc : ContDiffAt ℝ ∞ Φ (fun a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm (e y))) := by
    rw [e.left_inv hy]
    exact hΦ.contDiffAt (hO.mem_nhds hgO)
  have hcomp : ContDiffAt ℝ ∞ (fun v => Φ fun a => GlobalTheory.CxPts.ev X.str σ W (g a) (e.symm v)) (e y) :=
    hΦc.comp (e y) (hGc.restrict_scalars ℝ)
  refine hcomp.congr_of_eventuallyEq ?_

  have ht : Filter.Tendsto e.symm (𝓝 (e y)) (𝓝 y) := by
    have h := e.continuousAt_symm (e.map_source hy)
    rw [ContinuousAt, e.left_inv hy] at h
    exact h
  exact ht.eventually hfeq

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPolarisedTopChernCoeff
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in

theorem _root_.GlobalTheory.GoodTop.continuousAt_mixTop :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]
      {K : _root_.ReciprocityTheory.L2DbarEstimates.V n → Fin n → _root_.GlobalTheory.GoodTop.EndValuedForm11Coeffs n r} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n},
      (∀ i a b p q, ContinuousAt (fun x => K x i a b p q) v) →
        ContinuousAt (fun x => _root_.GlobalTheory.GoodTop.mixTop (K x)) v := by
  intro n r _ _ K v hK
  unfold _root_.GlobalTheory.GoodTop.mixTop
  simp only [Matrix.det_apply, Matrix.of_apply]
  fun_prop

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.core_clauses_of_weak_characterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → Core R.toRealDat F.lv2 ∧ IsSF R.toRealDat R.SF ∧ (∀ c, R.EEc c = EEc R.toRealDat R.SF c) ∧ ∀ i c, R.Wc' i c = Wcc R.toRealDat R.SF i c := by
  first | exact @GlobalTheory.CoreOfWeak.core_of_weak | exact GlobalTheory.CoreOfWeak.core_of_weak | (intros; apply GlobalTheory.CoreOfWeak.core_of_weak <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseInvertibleAntidiagonalCornerDoubledUnitaryStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_invertible_antidiagonal_corner_doubledUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (ε : ℤˣ), (∀ i j, σ (J j i) = ((ε : ℤ) : E) * J i j) → J.det ≠ 0 → ∀ g : UG (cA σ) (dbl (incM F J)), g ∈ closure {h : UG (cA σ) (dbl (incM F J)) | ∃ (p : UG (cA σ) (dbl (incM F J))) (t : GL (Fin n) (AE F E)), (p.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * diagCols (Fin n) = diagCols (Fin n) * t.1 ∧ IsUnit (Matrix.fromCols (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E)) * ((h * p).1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) (AE F E)) (-1 : Matrix (Fin n) (Fin n) (AE F E))).det} := by
  first | exact @GlobalTheory.SiegelDense.dense | exact GlobalTheory.SiegelDense.dense | (intros; apply GlobalTheory.SiegelDense.dense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedBirigidifiedBundleSymmetricStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_birigidified_bundle_symmetric : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ) (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left) := by
  first | exact @GlobalTheory.HeckeSym.descended_symm | exact GlobalTheory.HeckeSym.descended_symm | (intros; apply GlobalTheory.HeckeSym.descended_symm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryCharEqOneOnPrincipalLevel
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.PrincLevChar

theorem castDict_apply {D : D7} {Y : Type} {V W : HSp D} (hV : V = W) (μ : GA D V → Y) (k : GA D W) :
    castDict hV μ k = μ (cast (congrArg (GA D) hV.symm) k) := by
  subst hV
  rfl

set_option maxHeartbeats 1000000 in

theorem char_eq_one : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), castDict hV (T.mu ((i : ℕ) + 1) (res T σ)) k = 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hM ht hpb i σ hσ hV k hk
  rw [castDict_apply]
  exact GlobalTheory.T.dictionary_character_trivial_on_principal_level T R κ v₀ hL ht hpb i (res T σ) hσ hV _
    (((GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open D G Pl0 T0 A T R κ v₀ hL hM ht hpb i σ hσ hV).1 k).1 hk)

end GlobalTheory.HolDict.PrincLevChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChart
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem holoChart_trans_algChart {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F}
    {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} (he : IsHoloChart e)
    (c : AlgChart X.str σ X.dim) :
    DifferentiableOn ℂ (c.e ∘ e.symm) (e.target ∩ e.symm ⁻¹' c.e.source) :=
  differentiableOn_euclidean.2 fun a => ((he _ (c.x a)).mono fun _ hv =>
    ⟨hv.1, c.source_subset hv.2⟩).congr fun _ hv => c.apply_eq _ hv.2 a

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotConjTransposeMulMul
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem dot_conjTranspose_mul_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (y z : Fin n → ℂ) :
    star y ⬝ᵥ (Mᴴ * N * M) *ᵥ z = star (M *ᵥ y) ⬝ᵥ N *ᵥ (M *ᵥ z) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem mark_unique : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ μ' : ℂ), G.a = 1 →
    P.Mark μ → P.Mark μ' → μ = μ' := by
  intro p _ G P μ μ' ha hm hm'
  obtain ⟨v, hv, x, hx, hxp⟩ := hm
  obtain ⟨v', hv', x', hx', hxp'⟩ := hm'
  have hvv : v = v' := by
    have hc : Fintype.card {w : InfinitePlace G.F // sigPosH (G.gram_herm w) = 1} = 1 := ha
    rw [Fintype.card_eq_one_iff] at hc
    obtain ⟨w, hw⟩ := hc
    exact congrArg Subtype.val ((hw ⟨v, hv⟩).trans (hw ⟨v', hv'⟩).symm)
  subst hvv
  by_contra hne
  have hn := GlobalTheory.T.mark_norm_sq_eq_similitudeFactor p G P μ ⟨v, hv, x, hx, hxp⟩
  obtain ⟨-, -, hlaw⟩ := GlobalTheory.T.similitudePair_hermitianForm_invertible_similitude p G P v

  have e := dot_conjTranspose_mul_mul (G.psi v P.γ) (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) x x'
  rw [hlaw, hx, hx', Matrix.mulVec_smul, Matrix.smul_mulVec, star_smul, smul_dotProduct,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul] at e
  have hc0 : ((P.c : ℚ) : ℝ) ≠ 0 := by exact_mod_cast P.c.ne_zero
  have hμ : star μ * μ = (((P.c : ℚ) : ℂ)) := by
    rw [show star μ = (starRingEnd ℂ) μ from rfl, Complex.conj_mul', ← Complex.ofReal_pow, hn, Complex.ofReal_ratCast]
  have hμ0 : star μ ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hμ
    exact hc0 (by exact_mod_cast hμ.symm)
  have horth : star x ⬝ᵥ (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *ᵥ x' = 0 := by
    by_contra hne0
    have h1 : (((P.c : ℚ) : ℂ)) = star μ * μ' := by
      rw [← mul_assoc] at e; exact mul_right_cancel₀ hne0 e
    exact hne (mul_left_cancel₀ hμ0 (hμ.trans h1))

  obtain ⟨Z, hZ⟩ := GlobalTheory.T.similitudePair_gram_inv_congruent p G P v
  rw [hZ, dot_conjTranspose_mul_mul] at horth hxp hxp'
  have hx'0 : x' ≠ 0 := by
    rintro rfl; simp at hxp'
  have hY : (Z : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ x' ≠ 0 := by
    intro h0
    apply hx'0
    have := congrArg (fun w => ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ w) h0
    simpa [Matrix.mulVec_mulVec] using this
  have hneg := GlobalTheory.T.hermitianForm_neg_on_orthogonal_of_positiveIndex_one (G.gram v) (G.gram_herm v) (G.gram_det v) hv _ _ hxp horth hY
  exact absurd hxp' (not_lt.mpr hneg.le)

end GlobalTheory.LKMid.Pair
end

