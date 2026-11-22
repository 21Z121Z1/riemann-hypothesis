import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0219
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0382
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0359
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0380
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosets
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionWeilCharacterRationalEqOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTestVanishing
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.TypesFactor

section Split

variable {ι : Type} [DecidableEq ι] (i : ι) (G : ι → Type) [∀ j, Group (G j)] [∀ j, TopologicalSpace (G j)]

def splitEquiv : (∀ j, G j) ≃ₜ* G i × ∀ j : {j // j ≠ i}, G j :=
  { Homeomorph.piSplitAt i G with map_mul' := fun _ _ => rfl }

variable {i G}

theorem splitEquiv_apply (x : ∀ j, G j) : splitEquiv i G x = (x i, fun j : {j // j ≠ i} => x j) := rfl

theorem splitEquiv_symm_self (a : G i) (b : ∀ j : {j // j ≠ i}, G j) : (splitEquiv i G).symm (a, b) i = a :=
  congrArg Prod.fst ((splitEquiv i G).apply_symm_apply (a, b))

theorem splitEquiv_symm_ne (a : G i) (b : ∀ j : {j // j ≠ i}, G j) (j : {j // j ≠ i}) :
    (splitEquiv i G).symm (a, b) j = b j :=
  congrFun (congrArg Prod.snd ((splitEquiv i G).apply_symm_apply (a, b))) j

theorem splitEquiv_symm_one (a : G i) : (splitEquiv i G).symm (a, 1) = Pi.mulSingle i a := by
  apply (splitEquiv i G).injective
  rw [ContinuousMulEquiv.apply_symm_apply, splitEquiv_apply]
  exact Prod.ext (Pi.mulSingle_eq_same i a).symm (funext fun j => (Pi.mulSingle_eq_of_ne j.2 a).symm)

theorem splitEquiv_symm_mem_cent (g : ∀ j, G j) (a : G i) (b : ∀ j : {j // j ≠ i}, G j) :
    (splitEquiv i G).symm (a, b) ∈ cent g ↔ a ∈ cent (g i) ∧ b ∈ cent (fun j : {j // j ≠ i} => g j) := by
  simp only [mem_cent]
  rw [← (splitEquiv i G).injective.eq_iff, map_mul, map_mul, ContinuousMulEquiv.apply_symm_apply, splitEquiv_apply]
  exact Prod.ext_iff

end Split

theorem mem_cent_pi {ι : Type} {G : ι → Type} [∀ j, Group (G j)] {g x : ∀ j, G j} :
    x ∈ cent g ↔ ∀ j, x j ∈ cent (g j) :=
  ⟨fun h j => mem_cent.2 (congrFun (mem_cent.1 h) j), fun h => mem_cent.2 (funext fun j => mem_cent.1 (h j))⟩

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

theorem embAt_mem_cent {S : Finset (HeightOneSpectrum (𝓞 F))} {g : GAd σ J} {x : ∀ v : S, GLoc σ J v}
    (hx : x ∈ cent (projAt σ J S g)) : embAt σ J S x ∈ cent g := by
  have hm := mem_atPts.1 (embAt_mem σ J S x)
  refine mem_cent.2 (GAd_ext σ J (fun w => ?_) fun v => ?_)
  · simp only [map_mul, mem_finPts_iff_forall.1 hm.1 w, one_mul, mul_one]
  · by_cases hv : v ∈ S
    · have h := congrFun (mem_cent.1 hx) ⟨v, hv⟩
      rw [map_mul, map_mul, show proj σ J v (embAt σ J S x) = x ⟨v, hv⟩ from proj_embAt σ J S x ⟨v, hv⟩]
      exact h
    · simp only [map_mul, hm.2 v hv, one_mul, mul_one]

theorem isMulCommutative_cent_projAt (S : Finset (HeightOneSpectrum (𝓞 F))) {γ : GRat σ J} (hγ : IsRegSS γ.1.1) :
    IsMulCommutative (cent (projAt σ J S (ratEmb σ J γ))) :=
  ⟨⟨fun a b => Subtype.ext (funext fun v => by
    have hc := isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)
    exact congrArg Subtype.val (hc.1.1 ⟨a.1 v, mem_cent_pi.1 a.2 v⟩ ⟨b.1 v, mem_cent_pi.1 b.2 v⟩))⟩⟩

theorem leftInv_integrand (S : Finset (HeightOneSpectrum (𝓞 F))) {g : GAd σ J} (ff : ∀ v, GLoc σ J v → ℂ)
    {C : GAd σ J → ℂ} (hCi : LeftInv (cent g) C) :
    LeftInv (cent (projAt σ J S g)) fun x => C (embAt σ J S x) * ∏ v : S, ff v ((x v)⁻¹ * proj σ J v g * x v) := by
  intro t ht x
  simp only [map_mul, Pi.mul_apply]
  rw [hCi _ (embAt_mem_cent σ J ht)]
  congr 1
  refine Finset.prod_congr rfl fun v _ => congrArg (ff v) ?_
  have hc : t v * proj σ J v g = proj σ J v g * t v := mem_cent.1 (mem_cent_pi.1 ht v)
  have e : (t v * x v)⁻¹ * proj σ J v g * (t v * x v) = (x v)⁻¹ * ((t v)⁻¹ * (proj σ J v g * t v)) * x v := by group
  rw [e, ← hc, inv_mul_cancel_left]

theorem integrable_integrand (h : IsCMExt F E σ) (hJ : IsHermND σ J) (S : Finset (HeightOneSpectrum (𝓞 F)))
    {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (ff : ∀ v, GLoc σ J v → ℂ) (hc : ∀ v : S, Continuous (ff v))
    (hs : ∀ v : S, HasCompactSupport (ff v)) {C : GAd σ J → ℂ} (hC : Continuous C)
    (hCi : LeftInv (cent (ratEmb σ J γ)) C) (dg : Measure (∀ v : S, GLoc σ J v)) [dg.IsHaarMeasure]
    (dt : Measure (cent (projAt σ J S (ratEmb σ J γ)))) [dt.IsHaarMeasure] :
    Integrable (descend (cent (projAt σ J S (ratEmb σ J γ)))
      fun x => C (embAt σ J S x) * ∏ v : S, ff v ((x v)⁻¹ * proj σ J v (ratEmb σ J γ) * x v))
      (quotMeas _ dt dg) := by
  haveI : LocallyCompactSpace (∀ v : S, GLoc σ J v) := Pi.locallyCompactSpace_of_finite
  haveI := isMulRightInvariant_cent (isMulCommutative_cent_projAt σ J S hγ) dt
  have hp : ∀ v : S, IsProperOrbit (cent (proj σ J v (ratEmb σ J γ))) (proj σ J v (ratEmb σ J γ)) :=
    fun v => isProperOrbit_GLoc h hJ (isRegSS_proj_ratEmb hγ v)
  choose K hK hK' using fun v : S => hp v _ (hs v).isCompact
  refine integrable_descend (isClosed_cent _) (leftInv_integrand σ J S ff hCi)
    ((hC.comp (continuous_embAt σ J S)).mul (continuous_finset_prod _ fun v _ =>
      (hc v).comp ((((continuous_apply v).inv).mul continuous_const).mul (continuous_apply v))))
    (isCompact_univ_pi hK) fun x hx => ?_
  have h1 : ∀ v : S, (x v)⁻¹ * proj σ J v (ratEmb σ J γ) * x v ∈ tsupport (ff v) := fun v =>
    subset_tsupport _ (Finset.prod_ne_zero_iff.1 (right_ne_zero_of_mul hx) v (Finset.mem_univ _))
  choose t ht ht' using fun v => hK' v (x v) (h1 v)
  exact ⟨t, mem_cent_pi.2 ht, fun v _ => ht' v⟩

end Gen

end GlobalTheory.TypesFactor

namespace GlobalTheory.TypesFactor
section Gen2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
  (J : Matrix (Fin n) (Fin n) E)

def splitAt (S : Finset (HeightOneSpectrum (𝓞 F))) [DecidableEq S] (v₀ : S) :
    GLoc σ J v₀ × (∀ j : {j : S // j ≠ v₀}, GLoc σ J j) ≃ₜ* ∀ v : S, GLoc σ J v :=
  (splitEquiv v₀ fun v : S => GLoc σ J v).symm

variable {σ J}

theorem splitAt_self {S : Finset (HeightOneSpectrum (𝓞 F))} [DecidableEq S] {v₀ : S} (a : GLoc σ J v₀)
    (b : ∀ j : {j : S // j ≠ v₀}, GLoc σ J j) : splitAt σ J S v₀ (a, b) v₀ = a :=
  splitEquiv_symm_self (G := fun v : S => GLoc σ J v) a b

theorem splitAt_ne {S : Finset (HeightOneSpectrum (𝓞 F))} [DecidableEq S] {v₀ : S} (a : GLoc σ J v₀)
    (b : ∀ j : {j : S // j ≠ v₀}, GLoc σ J j) (j : {j : S // j ≠ v₀}) : splitAt σ J S v₀ (a, b) j = b j :=
  splitEquiv_symm_ne (G := fun v : S => GLoc σ J v) a b j

theorem splitAt_one {S : Finset (HeightOneSpectrum (𝓞 F))} [DecidableEq S] {v₀ : S} (a : GLoc σ J v₀) :
    splitAt σ J S v₀ (a, 1) = Pi.mulSingle v₀ a :=
  splitEquiv_symm_one (G := fun v : S => GLoc σ J v) a

theorem splitAt_mem_cent {S : Finset (HeightOneSpectrum (𝓞 F))} [DecidableEq S] {v₀ : S} (g : ∀ v : S, GLoc σ J v)
    (a : GLoc σ J v₀) (b : ∀ j : {j : S // j ≠ v₀}, GLoc σ J j) :
    splitAt σ J S v₀ (a, b) ∈ cent g ↔ a ∈ cent (g v₀) ∧ b ∈ cent (fun j : {j : S // j ≠ v₀} => g j) :=
  splitEquiv_symm_mem_cent (G := fun v : S => GLoc σ J v) g a b

end Gen2
end GlobalTheory.TypesFactor

namespace GlobalTheory.TypesFactor
section Gen3
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem quotInt_const_mul {H : Type} [Group H] [MeasurableSpace H] (T : Subgroup H) (dt : Measure T) (dh : Measure H)
    (c : ℂ) (f : H → ℂ) : quotInt T dt dh (fun x => c * f x) = c * quotInt T dt dh f := by
  simp only [quotInt, GlobalTheory.AutomorphicL2Unitary.descend]
  exact integral_const_mul _ _

theorem hasQuotInt_integrand_zero (h : IsCMExt F E σ) (hJ : IsHermND σ J) (S : Finset (HeightOneSpectrum (𝓞 F)))
    [DecidableEq S] (v₀ : S) {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (ff : ∀ v, GLoc σ J v → ℂ)
    (hc : ∀ v : S, Continuous (ff v)) (hs : ∀ v : S, HasCompactSupport (ff v)) (μ : Measure (GLoc σ J v₀))
    [μ.IsHaarMeasure] {C : GAd σ J → ℂ} (hC : Continuous C) (hCi : LeftInv (cent (ratEmb σ J γ)) C)
    (P : GLoc σ J v₀ → Prop) (hCP : ∀ g, P g → ∀ y, C (emb σ J v₀ g * y) = C y)
    (hloc : ∀ bf : GLoc σ J v₀ → ℂ, Continuous bf → LeftInv (cent (proj σ J v₀ (ratEmb σ J γ))) bf →
      (∀ g, P g → ∀ x, bf (g * x) = bf x) → ∀ (ds : Measure (cent (proj σ J v₀ (ratEmb σ J γ)))) [ds.IsHaarMeasure],
      quotInt (cent (proj σ J v₀ (ratEmb σ J γ))) ds μ
        (fun a => bf a * ff v₀ (a⁻¹ * proj σ J v₀ (ratEmb σ J γ) * a)) = 0)
    (dg : Measure (∀ v : S, GLoc σ J v)) [dg.IsHaarMeasure]
    (dt : Measure (cent (projAt σ J S (ratEmb σ J γ)))) [dt.IsHaarMeasure] :
    HasQuotInt (cent (projAt σ J S (ratEmb σ J γ))) dt dg
      (fun x => C (embAt σ J S x) * ∏ v : S, ff v ((x v)⁻¹ * proj σ J v (ratEmb σ J γ) * x v)) 0 := by
  have hint := integrable_integrand σ J h hJ S hγ ff hc hs hC hCi dg dt
  refine ⟨hint, ?_⟩
  haveI : LocallyCompactSpace (∀ v : S, GLoc σ J v) := Pi.locallyCompactSpace_of_finite
  haveI : LocallyCompactSpace (∀ j : {j : S // j ≠ v₀}, GLoc σ J j) := Pi.locallyCompactSpace_of_finite
  haveI : LocallyCompactSpace (cent (proj σ J v₀ (ratEmb σ J γ))) := (isClosed_cent _).locallyCompactSpace
  refine GlobalTheory.T.quotient_measure_fibration (GLoc σ J v₀) (∀ j : {j : S // j ≠ v₀}, GLoc σ J j) (∀ v : S, GLoc σ J v) (splitAt σ J S v₀)
    (cent (proj σ J v₀ (ratEmb σ J γ))) (cent (fun j : {j : S // j ≠ v₀} => proj σ J j (ratEmb σ J γ))) (cent (projAt σ J S (ratEmb σ J γ)))
    (fun a b => splitAt_mem_cent (projAt σ J S (ratEmb σ J γ)) a b) (isClosed_cent _) (isMulCommutative_cent_projAt σ J S hγ)
    dg dt μ Measure.haar _ (leftInv_integrand σ J S ff hCi) hint fun b => ?_
  set e := splitAt σ J S v₀
  have hsplit : (fun a => C (embAt σ J S (e (a, b))) *
      ∏ v : S, ff v ((e (a, b) v)⁻¹ * proj σ J v (ratEmb σ J γ) * e (a, b) v)) =
      fun a => (∏ j : {j : S // j ≠ v₀}, ff j ((b j)⁻¹ * proj σ J j (ratEmb σ J γ) * b j)) *
        (C (embAt σ J S (e (a, b))) * ff v₀ (a⁻¹ * proj σ J v₀ (ratEmb σ J γ) * a)) := by
    funext a
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ v₀]
    simp only [e, splitAt_self, splitAt_ne]
    ring
  have hmul : ∀ a a' : GLoc σ J v₀, e (a * a', b) = e (a, 1) * e (a', b) := fun a a' => by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  refine (congrArg _ hsplit).trans ((quotInt_const_mul _ _ _ _ _).trans ?_)
  rw [hloc (fun a => C (embAt σ J S (e (a, b))))
    (hC.comp ((continuous_embAt σ J S).comp (e.continuous.comp (continuous_id.prodMk continuous_const))))
    (fun t ht a => by
      change C (embAt σ J S (e (t * a, b))) = C (embAt σ J S (e (a, b)))
      rw [hmul, map_mul, hCi _ (embAt_mem_cent σ J ((splitAt_mem_cent (projAt σ J S (ratEmb σ J γ)) t 1).2 ⟨ht, one_mem _⟩))])
    (fun g hg x => by
      change C (embAt σ J S (e (g * x, b))) = C (embAt σ J S (e (x, b)))
      rw [hmul, map_mul, show e (g, 1) = Pi.mulSingle v₀ g from splitAt_one g, embAt_mulSingle]
      exact hCP g hg _) Measure.haar, mul_zero]

end Gen3
end GlobalTheory.TypesFactor

namespace GlobalTheory.TypesFactor

theorem typesFactor_vanish : GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic.TypeConstTermVanish → ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestFin T U μf ff → (∀ v, (μf v).IsHaarMeasure) → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ → ∀ (Φ : WittFrame V) (u : SV (wittIndex V)) (γ : GF V), u ≠ 0 → IsRegSS γ.1.1 → rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) {u} → ∀ C : GA D V → ℂ, Continuous C → LeftInv (cent (rat V γ)) C → (∀ hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u), LeftInv (NA (IsoFlag.single hW)) C) → ∀ (dg : Measure (∀ v : T.S, GLoc D.sp.cm.sig V.gram v)) [dg.IsHaarMeasure] (dt : Measure (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ)))) [dt.IsHaarMeasure], HasQuotInt (cent (projAt D.sp.cm.sig V.gram T.S (rat V γ))) dt dg (fun x => C (embAt D.sp.cm.sig V.gram T.S x) * ∏ v : T.S, ff v ((x v)⁻¹ * proj D.sp.cm.sig V.gram v (rat V γ) * x v)) 0 := by
  intro hTC D V T U μf ff hff hHaar hH Φ u γ hu hγ hlevi C hC hCi hCN dg _ dt _
  classical
  obtain ⟨ε, hW, hε2, hεpos, hεlt, hεγ, hεN⟩ := GlobalTheory.T.levi_idempotent_splitting D V Φ u hu
  obtain ⟨v₀, hv₀⟩ := hH ε.rank hεpos hεlt
  have hfin := hff.isFinFamily.1
  exact hasQuotInt_integrand_zero (isCMExt_host D) (isHermND_gram V) T.S v₀ hγ ff
    (fun v => (hfin v).1.continuous) (fun v => (hfin v).2) (μf v₀) hC hCi
    (fun g => ε.map (T.frame v₀).emb * ((splitHom D.sp.cm.sig V.gram (T.frame v₀).emb g).1 - 1) *
      (1 - ε.map (T.frame v₀).emb) = (splitHom D.sp.cm.sig V.gram (T.frame v₀).emb g).1 - 1)
    (fun g hg y => hCN hW _ (hεN v₀ (T.frame v₀).emb g hg) y)
    (fun bf hbc hbi hbn ds _ => (GlobalTheory.T.weightedOrbitalIntegral_typeTest_vanish hTC D V T U μf ff hff v₀ (hHaar v₀) γ ε hγ hε2 (hεγ γ hlevi) hεpos hεlt
      hv₀ bf hbc hbi hbn ds).2) dg dt

end GlobalTheory.TypesFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzOneParameterGroupFormula
section
open scoped Matrix

noncomputable section

namespace GlobalTheory.MetaplecticScalarDeriv

open MeasureTheory Filter Topology GlobalTheory.RealWeil

theorem exists_schwartz_one (l : Type) [Fintype l] : ∃ f : Sch l, f 0 = 1 := by
  let b : ContDiffBump (0 : EuclideanSpace ℝ l) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

theorem lintegral_sq_eq (l : Type) [Fintype l] (f : Sch l) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 = eLpNorm (⇑(f.toLp 2 : L2 l)) 2 volume ^ 2 := by
  rw [eLpNorm_congr_ae (f.coeFn_toLp 2 volume), eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
  have := lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := ⇑f) (μ := volume) (q := 2) two_pos
  simpa [ENNReal.toReal_ofNat] using this

theorem continuous_eval (l : Type) [Fintype l] (x : EuclideanSpace ℝ l) : Continuous fun f : Sch l => f x :=
  ((BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)).continuous

theorem continuous_rhoFun (l : Type) [Fintype l] (w : l ⊕ l → ℝ) {f : EuclideanSpace ℝ l → ℂ} (hf : Continuous f) :
    Continuous (rhoFun w f) :=
  (continuous_phase w).mul (hf.comp (continuous_add_right _))

theorem intertwine_fun (l : Type) [Fintype l] (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) (U : L2 l ≃ₗᵢ[ℂ] L2 l)
    (S : Sch l →L[ℂ] Sch l) (h3 : ∀ (w : l ⊕ l → ℝ) (f : L2 l), U (rho w f) = rho (M *ᵥ w) (U f))
    (h4 : ∀ f : Sch l, U (f.toLp 2) = (S f).toLp 2) (w : l ⊕ l → ℝ) (h h₁ : Sch l) (hh : ⇑h₁ = rhoFun w ⇑h) :
    ⇑(S h₁) = rhoFun (M *ᵥ w) ⇑(S h) := by
  have e1 : (h₁.toLp 2 : L2 l) = rho w (h.toLp 2) := by
    refine Lp.ext ((h₁.coeFn_toLp 2 volume).trans ?_)
    rw [hh]
    exact (rhoFun_congr w (h.coeFn_toLp 2 volume).symm).trans (coeFn_rho w _).symm
  have e2 : ((S h₁).toLp 2 : L2 l) = rho (M *ᵥ w) ((S h).toLp 2) := by
    rw [← h4, e1, h3, h4]
  have e3 : ⇑(S h₁) =ᵐ[volume] rhoFun (M *ᵥ w) ⇑(S h) := by
    refine ((S h₁).coeFn_toLp 2 volume).symm.trans ?_
    rw [e2]
    exact (coeFn_rho _ _).trans (rhoFun_congr _ ((S h).coeFn_toLp 2 volume))
  exact (Continuous.ae_eq_iff_eq volume (S h₁).continuous (continuous_rhoFun l _ (S h).continuous)).1 e3

theorem lintegral_iso (l : Type) [Fintype l] (U : L2 l ≃ₗᵢ[ℂ] L2 l) (S : Sch l →L[ℂ] Sch l)
    (h4 : ∀ f : Sch l, U (f.toLp 2) = (S f).toLp 2) (h : Sch l) :
    ∫⁻ x, ‖S h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 := by
  rw [lintegral_sq_eq, lintegral_sq_eq]
  congr 1
  have hn : ‖((S h).toLp 2 : L2 l)‖ = ‖(h.toLp 2 : L2 l)‖ := by rw [← h4, U.norm_map]
  rw [Lp.norm_def, Lp.norm_def] at hn
  exact (ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)).1 hn

theorem main_nonempty (hP : GlobalTheory.FunPr.Hypotheses₂) (l : Type) [Fintype l] [DecidableEq l] [Nonempty l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ) (hZ : Z ∈ LieAlgebra.Symplectic.sp l ℝ)
    (T : ℝ → Sch l →ₗ[ℂ] Sch l) (hT0 : T 0 = LinearMap.id) (hTadd : ∀ s t, T (s + t) = T s ∘ₗ T t)
    (hTrho : ∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : Sch l), ⇑h₁ = rhoFun w ⇑h →
      ⇑(T t h₁) = rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h))
    (hTiso : ∀ (t : ℝ) (h : Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2)
    (hTcont : ∀ (h : Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) :
    ∃ a : ℂ, ∀ f : Sch l,
      Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 (a • f + quad Z f)) := by
  obtain ⟨G, _, _, _, pr, om, omS, -, -, h3, h4, -, h6⟩ := hP.realMetaplecticRepresentation l
  obtain ⟨γ, -, hγ0, hγadd, hγpr, hγd⟩ := h6 Z hZ
  have hmul : ∀ s t (f : Sch l), omS (γ s) (omS (γ t) f) = omS (γ (s + t)) f := by
    intro s t f
    rw [hγadd, map_mul]
    rfl
  have hS1 : ∀ t (f : Sch l), omS (γ (-t)) (omS (γ t) f) = f := by
    intro t f
    rw [hmul, neg_add_cancel, hγ0, map_one]
    rfl
  have hS2 : ∀ t (f : Sch l), omS (γ t) (omS (γ (-t)) f) = f := by
    intro t f
    rw [hmul, add_neg_cancel, hγ0, map_one]
    rfl
  have hmat : ∀ t (w : l ⊕ l → ℝ), NormedSpace.exp (t • Z) *ᵥ ((pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) = w := by
    intro t w
    have e : pr (γ t) * pr (γ (-t)) = 1 := by rw [← map_mul, ← hγadd, add_neg_cancel, hγ0, map_one]
    have e' : (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) * (pr (γ (-t)) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 1 :=
      congrArg (fun g : Matrix.symplecticGroup l ℝ => (g : Matrix (l ⊕ l) (l ⊕ l) ℝ)) e
    rw [← hγpr t, Matrix.mulVec_mulVec, e', Matrix.one_mulVec]
  have hU : ∀ t, ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, (T t ∘ₗ (omS (γ (-t)) : Sch l →ₗ[ℂ] Sch l)) h = a • h := by
    intro t
    refine GlobalTheory.T.schwartz_unitary_intertwiner_scalar hP l _ (fun w h h₁ hh => ?_) (fun h => ?_)
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hTrho t _ _ _ (intertwine_fun l _ (om (γ (-t))) (omS (γ (-t))) (h3 _) (h4 _) w h h₁ hh), hmat]
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [hTiso, lintegral_iso l (om (γ (-t))) (omS (γ (-t))) (h4 _)]
  choose ν _hνn hν using hU
  have hTν : ∀ t (f : Sch l), T t f = ν t • omS (γ t) f := by
    intro t f
    have := hν t (omS (γ t) f)
    simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hS1] using this
  obtain ⟨f0, hf0⟩ := exists_schwartz_one l
  have hν0 : ν 0 = 1 := by
    have e := congrArg (fun g : Sch l => g 0) (hTν 0 f0)
    simp only [hT0, LinearMap.id_apply, hγ0, map_one, SchwartzMap.smul_apply, smul_eq_mul, hf0] at e
    change 1 = ν 0 * (1 : Sch l →L[ℂ] Sch l) f0 0 at e
    rw [ContinuousLinearMap.one_apply, hf0, mul_one] at e
    exact e.symm
  have hνmul : ∀ s t, ν (s + t) = ν s * ν t := by
    intro s t
    set f := omS (γ (-(s + t))) f0
    have e1 : T (s + t) f = ν (s + t) • f0 := by rw [hTν, hS2]
    have e2 : T (s + t) f = (ν s * ν t) • f0 := by
      rw [hTadd, LinearMap.comp_apply, hTν t, map_smul, hTν s, hmul, hS2, smul_smul, mul_comm]
    have e := congrArg (fun g : Sch l => g 0) (e1.symm.trans e2)
    simpa [hf0] using e
  have hcontS : ContinuousAt (fun t => omS (γ t) f0) 0 := by
    have hd := GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f0
    have h1 : Tendsto (fun t : ℝ => t • (t⁻¹ • (omS (γ t) f0 - f0))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • quad Z f0)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul hd
    rw [zero_smul] at h1
    have h2 : Tendsto (fun t : ℝ => omS (γ t) f0) (𝓝[≠] 0) (𝓝 f0) := by
      have h1' := h1.add_const f0
      rw [zero_add] at h1'
      refine h1'.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul, sub_add_cancel]
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hγ0, map_one]
    exact h2
  have hcontS0 : ContinuousAt (fun t => omS (γ t) f0 0) 0 := (continuous_eval l 0).continuousAt.comp hcontS
  have hS00 : omS (γ 0) f0 0 ≠ 0 := by
    rw [hγ0, map_one, ContinuousLinearMap.one_apply, hf0]
    exact one_ne_zero
  have hνc : ContinuousAt ν 0 := by
    have hq : ContinuousAt (fun t => T t f0 0 / omS (γ t) f0 0) 0 :=
      (hTcont f0 0).continuousAt.div hcontS0 hS00
    refine hq.congr ?_
    filter_upwards [hcontS0.eventually_ne hS00] with t ht
    rw [hTν, SchwartzMap.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ ht]
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_hasDerivAt_zero_of_map_add_mul' ν hν0 hνmul hνc
  refine ⟨a, fun f => ?_⟩
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 ha
  simp only [zero_add, hν0] at hslope
  have hd := GlobalTheory.T.tendsto_slope_metaplecticLift_schwartz l G pr om omS h3 h4 Z hZ γ hγ0 hγpr hγd f
  have hν1 : Tendsto ν (𝓝[≠] 0) (𝓝 1) := by
    rw [← hν0]
    exact hνc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (hν1.smul hd).add (hslope.smul_const f)
  rw [one_smul, add_comm] at hlim
  refine hlim.congr fun t => ?_
  rw [hTν]
  ext x
  simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem main_empty (l : Type) [Fintype l] [DecidableEq l] [IsEmpty l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (T : ℝ → Sch l →ₗ[ℂ] Sch l) (hT0 : T 0 = LinearMap.id) (hTadd : ∀ s t, T (s + t) = T s ∘ₗ T t)
    (hTcont : ∀ (h : Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) :
    ∃ a : ℂ, ∀ f : Sch l,
      Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 (a • f + quad Z f)) := by
  obtain ⟨f0, hf0⟩ := exists_schwartz_one l
  have hsub : ∀ x : EuclideanSpace ℝ l, x = 0 := fun x => by
    ext i
    exact isEmptyElim i
  have hdec : ∀ f : Sch l, f = f 0 • f0 := by
    intro f
    ext x
    rw [hsub x, SchwartzMap.smul_apply, hf0, smul_eq_mul, mul_one]
  set ν : ℝ → ℂ := fun t => T t f0 0 with hνdef
  have hTν : ∀ t (f : Sch l), T t f = ν t • f := by
    intro t f
    have e : T t f = f 0 • T t f0 := by
      conv_lhs => rw [hdec f]
      exact map_smul _ _ _
    rw [e]
    ext x
    rw [hsub x]
    simp only [SchwartzMap.smul_apply, smul_eq_mul, hνdef]
    ring
  have hν0 : ν 0 = 1 := by
    simp only [hνdef, hT0, LinearMap.id_apply, hf0]
  have hνmul : ∀ s t, ν (s + t) = ν s * ν t := by
    intro s t
    have e : T (s + t) f0 = (ν s * ν t) • f0 := by
      rw [hTadd, LinearMap.comp_apply, hTν t, map_smul, hTν s, smul_smul, mul_comm]
    have e' := congrArg (fun g : Sch l => g 0) e
    simpa [hf0, hνdef] using e'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_hasDerivAt_zero_of_map_add_mul' ν hν0 hνmul (hTcont f0 0).continuousAt
  refine ⟨a, fun f => ?_⟩
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 ha
  simp only [zero_add, hν0] at hslope
  have hq : quad Z f = 0 := by simp [quad]
  rw [hq, add_zero]
  refine (hslope.smul_const f).congr fun t => ?_
  rw [hTν]
  ext x
  simp only [SchwartzMap.smul_apply, SchwartzMap.sub_apply, smul_eq_mul, Complex.real_smul]
  ring

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (l : Type) [Fintype l] [DecidableEq l]
    (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ), Z ∈ LieAlgebra.Symplectic.sp l ℝ →
    ∀ T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l, T 0 = LinearMap.id → (∀ s t, T (s + t) = T s ∘ₗ T t) →
    (∀ (t : ℝ) (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(T t h₁) = GlobalTheory.RealWeil.rhoFun (NormedSpace.exp (t • Z) *ᵥ w) ⇑(T t h)) →
    (∀ (t : ℝ) (h : GlobalTheory.RealWeil.Sch l), ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    (∀ (h : GlobalTheory.RealWeil.Sch l) (x : EuclideanSpace ℝ l), Continuous fun t => T t h x) →
    ∃ a : ℂ, ∀ f : GlobalTheory.RealWeil.Sch l,
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds (a • f + GlobalTheory.RealWeil.quad Z f)) := by
  intro hP l _ _ Z hZ T hT0 hTadd hTrho hTiso hTcont
  rcases isEmpty_or_nonempty l with hl | hl
  · exact main_empty l Z T hT0 hTadd hTcont
  · exact main_nonempty hP l Z hZ T hT0 hTadd hTrho hTiso hTcont

end GlobalTheory.MetaplecticScalarDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTriplePolynomialFockStableMulTraceLinearStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTriple_polynomialFock_stable_mul_trace_linear : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' → ∀ (q : Fin a × Fin (a + a') → mixedEmbedding.mixedSpace F),
    ∀ f ∈ G.M.Pol B.ψ B.emb, ∃ f₁ ∈ G.M.Pol B.ψ B.emb,
      ∀ x, f₁ x = (GlobalTheory.GaussLine.pairInf F (Fin a × Fin (a + a')) x q : ℂ) * f x := by
  first | exact @GlobalTheory.PolMul.pol_mul_pairInf | exact GlobalTheory.PolMul.pol_mul_pairInf | (intros; apply GlobalTheory.PolMul.pol_mul_pairInf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosetsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_zeta_sum_GL_cosets : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w r => φ a.out * ℓ (ρ a.out x)) (eulerFac (B.map (z * ·)) (npow w (-((1 + (t : ℂ)) / 2))) * eulerFac (B.map fun β => (z * β)⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) * (∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) * ℓ x) := by
  first | exact @GlobalTheory.ZetaGL.zeta_sum_GL | exact GlobalTheory.ZetaGL.zeta_sum_GL | (intros; apply GlobalTheory.ZetaGL.zeta_sum_GL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionWeilCharacterRationalEqOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittTowerRestriction_weilCharacter_rational_eq_one : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χS' χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS' χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ c : GA D W →* Circle, (∀ h f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f)) → ∀ γ ∈ GQ W, c γ = 1 := by
  first | exact @GlobalTheory.TwistCharRat.char_eq_one_of_rat | exact GlobalTheory.TwistCharRat.char_eq_one_of_rat | (intros; apply GlobalTheory.TwistCharRat.char_eq_one_of_rat <;> assumption)
end

