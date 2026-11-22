import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0181
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0162
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0172
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0141
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import GroundTheory.AutomorphicForms.AdelicGLn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0183

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL
section
variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem comap_eq_of_placeOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← h x, ← h' (algebraMap (𝓞 K) (𝓞 L) x)]
  have : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
  rw [this, ← IsScalarTower.algebraMap_apply]

end

theorem normV_eq_pow {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L))
    (hc : v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal) :
    ∃ f : ℕ, normV v' = normV v ^ f := by
  classical
  haveI := v.isMaximal
  haveI := v'.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 L ⧸ v'.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI : Finite (𝓞 L ⧸ v'.asIdeal) := v'.asIdeal.finiteQuotientOfFreeOfNeBot v'.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  letI : Fintype (𝓞 L ⧸ v'.asIdeal) := Fintype.ofFinite _
  letI : Algebra (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ v'.asIdeal) :=
    (Ideal.quotientMap v'.asIdeal (algebraMap (𝓞 K) (𝓞 L)) hc.ge).toAlgebra
  refine ⟨Module.finrank (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ v'.asIdeal), ?_⟩
  simp only [normV, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank
end GlobalTheory.AboveL

namespace GlobalTheory.AboveL
section
variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem restrictScalars_mem_Dec {A : ValuationSubring Ω} {σ : G L Ω} (hσ : σ ∈ Dec (F := L) A) :
    (σ.restrictScalars K : G K Ω) ∈ Dec (F := K) A := hσ

theorem actsAs_restrictScalars {A : ValuationSubring Ω} {σ : G L Ω} {q f a b : ℕ} (hσ : ActsAs A (q ^ f) σ a b) :
    ActsAs A q (σ.restrictScalars K : G K Ω) (f * a) (f * b) := by
  refine ⟨restrictScalars_mem_Dec hσ.1, fun x hx => ?_⟩
  have := hσ.2 x hx
  rw [← pow_mul, ← pow_mul] at this
  exact this

theorem restrictScalars_mem_Ine_iff {A : ValuationSubring Ω} {σ : G L Ω} :
    (σ.restrictScalars K : G K Ω) ∈ Ine (F := K) A ↔ σ ∈ Ine (F := L) A := Iff.rfl

end

theorem exists_weil_restrict : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ' : Weil h'), ∃ σ : Weil h, (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) ∧ (deg σ = 0 ↔ deg σ' = 0) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' σ'
  obtain ⟨f, hf⟩ := normV_eq_pow v v' (comap_eq_of_placeOver h h')
  obtain ⟨a, b, hab⟩ := (mem_Weil h').mp σ'.2
  rw [hf] at hab
  refine ⟨⟨(σ' : G L Ω).restrictScalars K, (mem_Weil h).mpr ⟨_, _, actsAs_restrictScalars hab⟩⟩, fun z => rfl, ?_⟩
  rw [deg_eq_zero_iff, deg_eq_zero_iff]
  exact restrictScalars_mem_Ine_iff
end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentHeckeCharCompNormConjEmbeddingStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponent_heckeChar_compNorm_conjEmbedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (τ : E →+* ℂ), expo (compNorm E χ) (ComplexEmbedding.conjugate τ) = expo (compNorm E χ) τ := by
  first | exact @GlobalTheory.NormExpo.expo_compNorm_conjugate | exact GlobalTheory.NormExpo.expo_compNorm_conjugate | (intros; apply GlobalTheory.NormExpo.expo_compNorm_conjugate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHeckeLabel

theorem ext_mul {Gr Γ W K : Type} [Group Gr] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* Gr} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gr} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) (f : S.Forms) (g : Gr) (k : J) (hk : χ k = 1) : P.ext f.1 (g * k) = P.ext f.1 g := by
  have h2 := (GlobalTheory.classPres_basic ι S σ ρ J χ P).1 f 1 g k
  rwa [map_one, map_one, one_mul, Module.End.one_apply, hk, Units.val_one, one_smul] at h2

def rightTr {H Gr : Type} [Group H] [Group Gr] (φ : H →* Gr) (W : Type) [AddCommGroup W] [Module ℂ W] :
    H →* Module.End ℂ (Gr → W) where
  toFun g := LinearMap.funLeft ℂ W (fun h => h * φ g)
  map_one' := by ext F h; simp [LinearMap.funLeft]
  map_mul' g g' := by ext F h; simp [LinearMap.funLeft, mul_assoc]

theorem rightTr_sum {H Gr : Type} [Group H] [Group Gr] (φ : H →* Gr) {W : Type} [AddCommGroup W] [Module ℂ W] (s : Finset H)
    (F : Gr → W) (h : Gr) : (∑ γ ∈ s, rightTr φ W γ) F h = ∑ γ ∈ s, F (h * φ γ) := by
  rw [LinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem opOf_single {D : D7} {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) (d : List ℤ) : opOf π P (Finsupp.single d 1) = ∑ γ ∈ Hk3.rep V P d, π γ := by
  unfold opOf
  rw [Finsupp.sum_single_index (by exact zero_smul ℂ _), one_smul]

theorem hkF_single {D : D7} (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (d : List ℤ)
    (F : Bridge.Gf V → W) :
    hkF V P (Finsupp.single d 1) F = opOf (rightTr (finHom V).rangeRestrict W) P (Finsupp.single d 1) F := by
  funext h
  have e1 : hkF V P (Finsupp.single d 1) F h = (1 : ℂ) • ∑ γ ∈ Hk3.rep V P d, F (h * (finHom V).rangeRestrict γ) :=
    Finsupp.sum_single_index (h := fun d (z : ℂ) => z • ∑ γ ∈ Hk3.rep V P d, F (h * (finHom V).rangeRestrict γ))
      (zero_smul ℂ _)
  exact e1.trans ((one_smul ℂ _).trans ((rightTr_sum (finHom V).rangeRestrict _ F h).symm.trans
    (congrArg (fun u : Module.End ℂ (Bridge.Gf V → W) => u F h) (opOf_single _ P d).symm)))

theorem side_label {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsSDFrame V β Λ 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : GQ V →* Module.End ℂ W} {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} {S : CSD K}
    (Pr : Bridge.ClassPres (Bridge.ratF V) S σ ρ (levEnv V β L).J (levEnv V β L).χ) {Pl0 : Type} (pl : Pl0 → Pl D.host.E)
    (ok : Set Pl0) (op : ok × ℕ → Module.End K S.Forms)
    (Comparison₂ : Bridge.HeckeTie (Bridge.ratF V) Pr op (fun i => 1 ≤ i.2 ∧ i.2 ≤ V.rank) (isTEnv V pl ok) (isLocEnv V pl ok))
    (P : ok) (h0 : op (P, 0) = 1) (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ pl P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl P))
    (k : ℕ) (hk : k ≤ V.rank) (f : S.Forms) :
    Pr.ext (op (P, k) f).1 = hkF V (pl P) (Finsupp.single (splitLab V.rank k) 1) (Pr.ext f.1) := by
  refine hβ.elim fun c hc => ?_
  have hc' : IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl P).asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 (pl P).isPrime.ne_top
  have hl := fun e f' he => (GlobalTheory.LevSplit.lev_split V β Λ 1 (flag1L L) hc').2 (pl P) e f' he h1 hoff
  have hinv : ∀ g (x : (levEnv V β L).J), IsLocElt V (pl P) x → Pr.ext f.1 (g * x) = Pr.ext f.1 g := by
    rintro g ⟨x, hx⟩ ⟨e, f', a, he, ha, hxa, hs⟩
    obtain rfl : x = (finHom V).rangeRestrict a := Subtype.ext hxa
    exact ext_mul Pr f g _ (Units.ext ((hl e f' he).2.1 a ⟨ha, hx⟩ hs))
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · have e0 : splitLab V.rank 0 = List.replicate V.rank 0 := by simp [splitLab]
    rw [h0, e0, hkF_single]
    refine ((GlobalTheory.T.spherical_label_operators_on_hyperspecial_fixed_vectors V (pl P)).2.2.1.2 _ _ _ fun a ha => ?_).symm
    obtain ⟨ha, e, f', he, hs⟩ := ha
    funext g
    exact hinv g ⟨(finHom V).rangeRestrict a, (((hl e f' he).1 a hs).2 ha).2⟩ ⟨e, f', a, he, ha.1, rfl, hs⟩
  · have hi : 1 ≤ ((P, k) : ok × ℕ).2 ∧ ((P, k) : ok × ℕ).2 ≤ V.rank := ⟨hpos, hk⟩
    have hs := fun x => GlobalTheory.T.split_hecke_element_label_zeros_then_neg_ones V pl ok (P, k) x
    have hd := GlobalTheory.T.doubleCosetOperator_eq_labelOperator_localReps V β Λ 1 L hc' (pl P) h1 hoff (splitLab V.rank k) (Comparison₂.hx (P, k)) (Comparison₂.hA (P, k)) (hs 1).2.2
      ((hs _).1 hk (Comparison₂.hx_ok _ hi)) (fun a ha => (hs a).2.1 (Comparison₂.hA_loc _ hi a ha)) (Comparison₂.hDC _ hi)
    exact (Comparison₂.op_eq _ hi f).trans (hd.2 W _ hinv)

theorem split_ops : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t h, IsOpsX R t h → ∀ (P : A.ok t) k, k ≤ D.sp.X'.rank → ∀ f, R.jX t (A.heckeR t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (R.jX t f)) ∧ ∀ j t h, IsOpsV R j t h → ∀ (P : A.ok t) k, k ≤ (Vc D j).rank → ∀ f, R.jV j t (A.heckeL j t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1) (R.jV j t f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hM
  have hgood : ∀ t (P : A.ok t), Good R t (R.pl P) := fun t P => ((GlobalTheory.T.theta_lift_levels_good_primes_properties R F hL).2.2.2 hF t P P.2).1
  refine ⟨fun t h hh P k hk f => ?_, fun j t h hh P k hk f => ?_⟩
  · have hd := side_label D.sp.X' R.βX R.ΛX (R.datXt t) hL.βX (R.B.R t).pres R.pl (A.ok t) (A.heckeR t) (R.B.R t).hecke
      P (hF.degR t P).1 (hgood t P) k hk f
    refine (hM.HX t).1 ?_
    refine (hM.jX t _).trans (Eq.trans ?_ (hh _ (hgood t P) _ _).symm)
    exact hd.trans (congrArg (hkF D.sp.X' (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1)) (hM.jX t f).symm)
  · have hd := side_label (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) (hL.βV j) (R.B.L j t).pres R.pl (A.ok t) (A.heckeL j t)
      (R.B.L j t).hecke P (hF.degL j t P).1 (hgood t P) k hk f
    refine (hM.HV j t).1 ?_
    refine (hM.jV j t _).trans (Eq.trans ?_ (hh _ (hgood t P) _ _).symm)
    exact hd.trans (congrArg (hkF (Vc D j) (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1)) (hM.jV j t f).symm)

end GlobalTheory.SplitHeckeLabel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FockVectorsChainIsVacuumOffThetaLevels
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacGood

variable {D : D7}

theorem infPart_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {u : WO S T}
    (hu : u ∈ latO S T LS LT fun _ => True) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold latO at hu
  refine AddSubgroup.closure_induction (p := fun u _ => infPart D (u i j) = 0) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    rw [Matrix.of_apply]
    exact (show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) from rfl).trans (TensorProduct.zero_tmul _ _)
  · simp
  · intro x y _ _ hx hy; rw [Matrix.add_apply, RingHom.map_add, hx, hy, add_zero]
  · intro x _ hx; rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem prime_idem_absorb (S : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    f * e = e := by
  have hff := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents S).2.2.1 P e f h).1
  rcases h with ⟨he, hf⟩ | ⟨hf, -, -⟩
  · rw [hf, add_mul, he.1.1, mul_comm (cA D e) e, he.1.2.1, add_zero]
  · subst hf; exact hff

theorem prime_idem_absorb_conj (S : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    f * cA D e = cA D e := by
  have hcf := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents S).2.2.1 P e f h).2.1
  have := congrArg (cA D) (prime_idem_absorb S h)
  rwa [map_mul, hcf] at this

theorem half_absorb (S : HSp D) {T : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f)
    {u : WO S T} (hu : IsHalf e u ∨ IsHalf (cA D e) u) (i : Fin T.rank) (j : Fin S.rank) : f * u i j = u i j := by
  rcases hu with hu | hu
  · rw [← hu i j, ← mul_assoc, prime_idem_absorb S h]
  · rw [← hu i j, ← mul_assoc, prime_idem_absorb_conj S h]

theorem idemSum_mul_zero (S : HSp D) {E0 : AE D} {Q : Finset (Pl D.host.E)} (hE : IsIdemSum E0 Q)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hQ : ∀ PP ∈ Q, PP ≠ P ∧ ¬ IsConjPl PP P)
    {e f : AE D} (hP : IsPrimeIdem P e f) (x : AE D) (hx : f * x = x) : E0 * x = 0 ∧ cA D E0 * x = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
  have hI := GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents S
  have key : ∀ PP ∈ Q, es PP * x = 0 ∧ cA D (es PP) * x = 0 := by
    intro PP hPP
    have hPPi : IsPrimeIdem PP (es PP) (es PP + cA D (es PP)) := Or.inl ⟨hes PP hPP, rfl⟩
    have h4 := (hI.2.2.1 PP _ _ hPPi).2.2.2.2 P e f hP
    have hff : (es PP + cA D (es PP)) * f = 0 := by
      rcases h4 with h | ⟨-, h | h⟩
      · exact h
      · exact absurd h.symm (hQ PP hPP).1
      · exact absurd h (hQ PP hPP).2
    have ha := prime_idem_absorb S hPPi
    have hb := prime_idem_absorb_conj S hPPi
    constructor
    · calc es PP * x = ((es PP + cA D (es PP)) * es PP) * (f * x) := by rw [ha, hx]
        _ = es PP * (((es PP + cA D (es PP)) * f) * x) := by ring
        _ = 0 := by rw [hff]; ring
    · calc cA D (es PP) * x = ((es PP + cA D (es PP)) * cA D (es PP)) * (f * x) := by rw [hb, hx]
        _ = cA D (es PP) * (((es PP + cA D (es PP)) * f) * x) := by ring
        _ = 0 := by rw [hff]; ring
  constructor
  · rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun PP h => (key PP h).1
  · rw [map_sum, Finset.sum_mul]; exact Finset.sum_eq_zero fun PP h => (key PP h).2

theorem vac_of_frames {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} {NS NT : ℕ}
    (hS : IsSDFrame S βS ΛS NS) (hT : IsSDFrame T βT ΛT NT) {P : Pl D.host.E}
    (hNS : ((NS : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (hNT : ((NT : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    {f₀ : WO S T → ℂ} (hv : IsVacO ψ θ S T sS sT ΛS ΛT f₀) : IsVacAt ψ S T P f₀ := by
  obtain ⟨cS, hS⟩ := hS
  obtain ⟨cT, hT⟩ := hT
  refine GlobalTheory.T.isLocalVacuum_of_isLatticeVacuum_coprime_level ψ S T βS βT ΛS ΛT (NS ^ cS) (NT ^ cT) hS hT P ?_ f₀ hv.2.theta hv.2.lat
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  intro h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact hNS (P.isPrime.mem_of_pow_mem _ h)
  · exact hNT (P.isPrime.mem_of_pow_mem _ h)

theorem vac_pt {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {P : Pl D.host.E}
    {f₀ Φ f : WO S T → ℂ} {E1 : AE D} {Λ : AddSubgroup (WO S T)}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hv : IsVacAt ψ S T P f₀) (ht : IsThetaAt ψ (symplO S T) (heisO ψ S T) E1 Λ 1 f₀ Φ f)
    (hE : ∀ e' f', IsPrimeIdem P e' f' → ∀ x : AE D, f' * x = x → E1 * x = 0 ∧ cA D E1 * x = 0)
    (hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f φ)) :
    ∀ φ, IsVacAt ψ S T P (pureTensorO ψ θ S T sS sT BS BT f φ) := by
  intro φ
  refine ⟨hth φ, fun e' f' hP u hu hh => ?_⟩
  refine GlobalTheory.T.heisenbergOriented_finite_fixes_fockPolynomialVectors ψ θ S T hθ sS sT BS BT f hth u (infPart_latO hu) ?_ φ
  exact GlobalTheory.T.heisenbergOperator_fix_thetaDatum_away_splitPlaces ψ S T E1 Λ 1 f₀ Φ f ht u (fun i j => hE e' f' hP _ (half_absorb S hP hh i j))
    (hv.2 e' f' hP u hu hh)

theorem fock_vacua_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F →
    ∀ t P, Good R t P → (∀ k, k + 1 < D.R.m → ∀ φ, IsVacAt R.ψ _ _ P (R.ptY t k φ)) ∧ (∀ φ, IsVacAt R.ψ _ _ P (R.ptX t φ)) ∧
      ∀ i φ, IsVacAt R.ψ _ _ P (R.ptP i t φ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t P hG
  classical
  have hN := ((GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev).2.1 t P hG).1
  have hθ : IsInfFam R.θ := hC.models.inf
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hm := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · obtain ⟨hvac, e, he, ht⟩ := hC.chain.vY t k hk
    have hv := vac_of_frames (hC.lev.βY k (by omega)) (hC.lev.βY (k + 1) hk) hN hN hvac
    exact vac_pt hθ hv ht (fun e' f' hP x hx => idemSum_mul_zero (Yc D k) he (fun PP h => hG PP (Finset.mem_union.1 h)) hP x hx) (hC.chain.ptY t k hk)
  · obtain ⟨hvac, e, he, ht⟩ := hC.chain.vX t
    have hv := vac_of_frames (hC.lev.βY (D.R.m - 1) (by omega)) hC.lev.βX hN h1 hvac
    exact vac_pt hθ hv ht (fun e' f' hP x hx => idemSum_mul_zero (Yc D (D.R.m - 1)) he (fun PP h => hG PP (Finset.mem_union.1 h)) hP x hx) (hC.chain.ptX t)
  · obtain ⟨hvac, e, he, ht⟩ := hC.thP.vP i t
    have hv := vac_of_frames (hC.lev.βV i) (hC.lev.βW i) h1 h1 hvac
    refine vac_pt hθ hv ht (fun e' f' hP x hx => ?_) (hC.thP.pt_theta i t)
    obtain ⟨a, b⟩ := idemSum_mul_zero (Vc D i) he (fun PP h => hG PP (Finset.mem_union.1 h)) hP x hx
    exact ⟨b, by rw [cA_cA]; exact a⟩

end GlobalTheory.VacGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianDualSubsetOfIntegralGramStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDual_subset_of_integral_gram : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L),
    (∀ z, σ (σ z) = z) → (∀ z, Valued.v (σ z) = Valued.v z) →
    JS ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → JT ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) →
    (∀ i j, σ ((JS : Matrix (Fin n) (Fin n) L) i j) = (JS : Matrix (Fin n) (Fin n) L) j i) →
    (∀ i j, σ ((JT : Matrix (Fin n') (Fin n') L) i j) = (JT : Matrix (Fin n') (Fin n') L) j i) →
    ∀ x : Matrix (Fin n') (Fin n) L, (∀ i j, (x * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Matrix.transpose (x.map σ)) i j ∈ Formalism.UG.intL L) →
    ∀ v : Fin n → L,
      (∀ u : Fin n → L, (∀ i, u i ∈ Formalism.UG.intL L) → (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) u v ∈ Formalism.UG.intL L) →
      (∀ w : Fin n' → L, (∀ i, w i ∈ Formalism.UG.intL L) →
        Formalism.UG.hform σ (JS : Matrix (Fin n) (Fin n) L) (GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w) v ∈ Formalism.UG.intL L) →
      ∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧
        (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + GlobalTheory.Hk3.HoweG.adj σ JS JT x *ᵥ w := by
  first | exact @GlobalTheory.Hk3.HoweG.hermDual_subset_of_gram_int | exact GlobalTheory.Hk3.HoweG.hermDual_subset_of_gram_int | (intros; apply GlobalTheory.Hk3.HoweG.hermDual_subset_of_gram_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapInfDiagMaxRealSubfieldCmStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleMap_infDiag_maxRealSubfield_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (x : (maximalRealSubfield E)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infDiag x) = infDiag (Units.map (algebraMap (maximalRealSubfield E) E).toMonoidHom x) := by
  first | exact @GlobalTheory.InfDiagExt.ideleMap_infDiag | exact GlobalTheory.InfDiagExt.ideleMap_infDiag | (intros; apply GlobalTheory.InfDiagExt.ideleMap_infDiag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapNormToMaxRealInfiniteIdeleStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleMap_normToMaxReal_infiniteIdele : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (u : (Cinf E)ˣ), GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (ideleNorm E (infId E u)) = infId E (u * Units.map (starRingEnd (Cinf E)).toMonoidHom u) := by
  first | exact @GlobalTheory.GalReal.ideleMap_ideleNorm_infId | exact GlobalTheory.GalReal.ideleMap_ideleNorm_infId | (intros; apply GlobalTheory.GalReal.ideleMap_ideleNorm_infId <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfCharConjEmbeddingNegOfInvariantPairingStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.TheRec GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infChar_conjEmbedding_neg_of_invariant_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π π' : CuspSub E a), Paired π π' conjOp → ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), π.HasInfChar τ m → π'.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m' → m' = m.map Neg.neg := by
  first | exact @GlobalTheory.CapPair.infChar_conj_of_paired | exact GlobalTheory.CapPair.infChar_conj_of_paired | (intros; apply GlobalTheory.CapPair.infChar_conj_of_paired <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaTranslatesAwayDiscStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralJets_normalisedTheta_translates_away_disc : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam h Λ θ p ι → p ≠ D.host.d → (p = 3 → D.host.d % 3 = 2) → ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (M : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < M → ¬ p ∣ M → (∀ k, (M : ℂ) • t k ∈ Λ) → ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ D.host.d ha hd lam hlam) Λ (v j)) → ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) → JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) := by
  first | exact @GlobalTheory.ThLoc.jetsIntegral_away_disc | exact GlobalTheory.ThLoc.jetsIntegral_away_disc | (intros; apply GlobalTheory.ThLoc.jetsIntegral_away_disc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOfFinOrderOfCompactConjMemUnitaryRationalPoint
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory

theorem isOfFinOrder_of_conj_mem_ratU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Subgroup (UA E n)),
    IsCompact (D : Set (UA E n)) → ∀ (g : UA E n), ∀ c ∈ D, g * c * g⁻¹ ∈ ratU E n → IsOfFinOrder c := by
  intro E _ _ _ n D hD g c hc hgc
  haveI : DiscreteTopology (ratGL E n).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E n
  have hcl : IsClosed (((ratGL E n).range : Subgroup (GA E n)) : Set (GA E n)) := Subgroup.isClosed_of_discrete
  let K : Set (GA E n) := (fun x : UA E n => ((g * x * g⁻¹ : UA E n) : GA E n)) '' (D : Set (UA E n))
  have hK : IsCompact K := hD.image (continuous_subtype_val.comp ((continuous_const.mul continuous_id).mul continuous_const))
  have hKG : IsCompact (K ∩ ((ratGL E n).range : Set (GA E n))) := hK.inter_right hcl
  let t : Set (ratGL E n).range := {x | (x : GA E n) ∈ K}
  have himg : Subtype.val '' t = K ∩ ((ratGL E n).range : Set (GA E n)) := by
    ext y; constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨hx, x.2⟩
    · rintro ⟨hy, hy'⟩; exact ⟨⟨y, hy'⟩, hy, rfl⟩
  have ht : IsCompact t := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]; exact hKG
  have hfin : (K ∩ ((ratGL E n).range : Set (GA E n))).Finite := by
    rw [← himg]; exact (ht.finite_of_discrete).image _
  by_contra hno
  have hinj := (injective_pow_iff_not_isOfFinOrder).2 hno
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((g * c ^ k * g⁻¹ : UA E n) : GA E n)) ?_ ?_ hfin
  · intro i j hij
    apply hinj
    have h1 : g * c ^ i * g⁻¹ = g * c ^ j * g⁻¹ := Subtype.ext hij
    simpa using h1
  · intro k
    refine ⟨⟨c ^ k, D.pow_mem hc k, rfl⟩, ?_⟩
    have hk : g * c ^ k * g⁻¹ ∈ ratU E n := by
      have := (ratU E n).pow_mem hgc k
      simpa [conj_pow] using this
    exact (Subgroup.mem_subgroupOf).1 hk

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalDoubleCosetLabelIffDecreasingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ d : List ℤ, IsLab V P d ↔ d.length = V.rank ∧ d.Pairwise (fun a b => b ≤ a) ∧ (conjPl P = P → dualLab d = d) := by
  first | exact @GlobalTheory.LabChar.labels_char | exact GlobalTheory.LabChar.labels_char | (intros; apply GlobalTheory.LabChar.labels_char <;> assumption)
end

