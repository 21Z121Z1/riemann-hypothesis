import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0030
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqSelfDualLatticesSameHermitianSpace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CnormMapConjMulVec
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp.GramFrame

open Matrix Module
open scoped ComplexOrder InnerProductSpace

variable {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

def gramOf {n : ℕ} (w : Fin n → Hs) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => ⟪w i, w j⟫_ℂ

theorem norm_sum_sq {n : ℕ} (w : Fin n → Hs) (c : Fin n → ℂ) :
    ((‖∑ i, c i • w i‖ ^ 2 : ℝ) : ℂ) = star c ⬝ᵥ (gramOf w *ᵥ c) := by
  have h1 : ((‖∑ i, c i • w i‖ ^ 2 : ℝ) : ℂ) = ⟪∑ i, c i • w i, ∑ i, c i • w i⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h1]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, dotProduct, mulVec, gramOf, of_apply,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring

theorem gramOf_posDef {n : ℕ} {w : Fin n → Hs} (hw : LinearIndependent ℂ w) : (gramOf w).PosDef := by
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun c hc => ?_⟩
  · ext i j
    simp [gramOf, conjTranspose_apply]
  · rw [← norm_sum_sq]
    have h0 : ∑ i, c i • w i ≠ 0 := fun h => hc (funext fun i => Fintype.linearIndependent_iff.1 hw c h i)
    exact Complex.zero_lt_real.2 (by positivity)

theorem exists_frame {n : ℕ} {w : Fin n → Hs} (hw : LinearIndependent ℂ w) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ ∀ c, Formalism.HermitianLatticesTheory.cnorm (B *ᵥ c) = ‖∑ i, c i • w i‖ := by
  obtain ⟨B, hB, hG⟩ := exists_unit_factor (gramOf_posDef hw)
  refine ⟨B, hB, fun c => ?_⟩
  have key : star (B *ᵥ c) ⬝ᵥ (B *ᵥ c) = star c ⬝ᵥ ((Bᴴ * B) *ᵥ c) := by
    have e0 : star c ⬝ᵥ (Bᴴ *ᵥ (B *ᵥ c)) = (star c ᵥ* Bᴴ) ⬝ᵥ (B *ᵥ c) := dotProduct_mulVec _ _ _
    rw [← mulVec_mulVec, e0, star_mulVec]
  have e : ((∑ i, ‖(B *ᵥ c) i‖ ^ 2 : ℝ) : ℂ) = ((‖∑ i, c i • w i‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum_norm_sq_eq, norm_sum_sq, hG, key]
  simp only [Formalism.HermitianLatticesTheory.cnorm, Complex.ofReal_injective e, Real.sqrt_sq (norm_nonneg _)]

theorem cnorm_map_conj_mulVec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (B.map (starRingEnd ℂ) *ᵥ u) = Formalism.HermitianLatticesTheory.cnorm (B *ᵥ star u) := by
  have e : B.map (starRingEnd ℂ) *ᵥ u = star (B *ᵥ star u) := by
    funext i
    simp [mulVec, dotProduct, star_sum, mul_comm]
  rw [e]
  simp [Formalism.HermitianLatticesTheory.cnorm]

end GlobalTheory.HSApp.GramFrame

open GlobalTheory.HSApp.GramFrame Matrix Module in

theorem GlobalTheory.HSApp.hasGram_of_inner : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ), (∀ v : InfinitePlace K, ∃ (Hs : Type) (_ : NormedAddCommGroup Hs) (_ : InnerProductSpace ℂ Hs) (Φ : V →+ Hs), ((∀ (a : K) (x : V), Φ (a • x) = v.embedding a • Φ x) ∨ (∀ (a : K) (x : V), Φ (a • x) = starRingEnd ℂ (v.embedding a) • Φ x)) ∧ (∀ x, N v.embedding x = ‖Φ x‖) ∧ ∀ (n : ℕ) (e : Fin n → V), LinearIndependent K e → LinearIndependent ℂ (fun i => Φ (e i))) → GlobalTheory.AllWt.HasGram N := by
  intro K V _ _ _ _ _ N h
  classical
  let b := Module.finBasis K V
  have key : ∀ v : InfinitePlace K, ∃ Y : Matrix (Fin (finrank K V)) (Fin (finrank K V)) ℂ, IsUnit Y.det ∧
      ∀ x, Formalism.HermitianLatticesTheory.cnorm (Y *ᵥ Formalism.HermitianLatticesTheory.vecAt b v x) = N v.embedding x := by
    intro v
    obtain ⟨Hs, i1, i2, Φ, hlin, hN, hli⟩ := h v
    obtain ⟨B, hB, hBn⟩ := exists_frame (hli _ b b.linearIndependent)
    have hsum : ∀ x, Φ x = ∑ i, Φ (b.repr x i • b i) := fun x => by
      conv_lhs => rw [← b.sum_repr x]
      exact map_sum Φ _ _
    rcases hlin with hl | hl
    · refine ⟨B, hB, fun x => ?_⟩
      rw [hN, hBn, hsum]
      simp only [hl]
      rfl
    · refine ⟨B.map (starRingEnd ℂ), ?_, fun x => ?_⟩
      · have e := RingHom.map_det (starRingEnd ℂ) B
        change IsUnit ((starRingEnd ℂ).mapMatrix B).det
        rw [← e]
        exact hB.map _
      · rw [cnorm_map_conj_mulVec, hN, hBn, hsum]
        simp only [hl]
        rfl
  choose Y hY hYn using key
  refine GlobalTheory.AllWt.IsGram.hasGram (b := b) (X := fun v => (Y v)⁻¹) fun v => ⟨isUnit_nonsing_inv_det _ (hY v), fun x => ?_⟩
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord]
  rw [nonsing_inv_nonsing_inv _ (hY v)]
  exact hYn v x
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory.SecJet

section Alg

variable (R : Type) [CommRing R]

def sqIdeal (k : ℕ) : Ideal (MvPolynomial (Fin k) R) :=
  Ideal.span (Set.range fun a : Fin k => (MvPolynomial.X a : MvPolynomial (Fin k) R) ^ 2)

abbrev EpsAlg (k : ℕ) : Type := MvPolynomial (Fin k) R ⧸ sqIdeal R k

def topMon (k : ℕ) : Fin k →₀ ℕ := ∑ a, Finsupp.single a 1

theorem coeff_topMon_eq_zero {k : ℕ} {p : MvPolynomial (Fin k) R} (hp : p ∈ sqIdeal R k) :
    MvPolynomial.coeff (topMon k) p = 0 := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hp
  rw [MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_mul_monomial', if_neg]
  intro h
  have := h a
  simp [topMon, Finsupp.finsetSum_apply, Finsupp.single_apply] at this

def topCoeff (k : ℕ) : EpsAlg R k →ₗ[R] R :=
  (Submodule.liftQ ((sqIdeal R k).restrictScalars R) (MvPolynomial.lcoeff R (topMon k))
    (fun _ hp => LinearMap.mem_ker.2 (coeff_topMon_eq_zero R hp))) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R (sqIdeal R k)).symm.toLinearMap

def eps {k : ℕ} (a : Fin k) : EpsAlg R k := Ideal.Quotient.mk _ (MvPolynomial.X a)

theorem eps_mul_self {k : ℕ} (a : Fin k) : eps R a * eps R a = 0 := by
  rw [eps, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  exact Ideal.subset_span ⟨a, rfl⟩

def epsIncl {k : ℕ} (a : Fin k) : DualNumber R →ₐ[R] EpsAlg R k :=
  DualNumber.lift ⟨(Algebra.ofId R (EpsAlg R k), eps R a), eps_mul_self R a,
    fun _ => Commute.all _ _⟩

end Alg

end GlobalTheory.SecJet

namespace GlobalTheory.SecJet

section Geo

variable (R : Type) [CommRing R]

abbrev epsT (k : ℕ) : Over (Sp R) := Over.mk (spMap (algebraMap R (EpsAlg R k)))

theorem spMap_comp_eq {A B : Type} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    spMap (f : A →+* B) ≫ spMap (algebraMap R A) = spMap (algebraMap R B) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact f.comp_algebraMap

def epsIn {k : ℕ} (a : Fin k) : epsT R k ⟶ epsR R :=
  Over.homMk (spMap ((epsIncl R a : DualNumber R →ₐ[R] EpsAlg R k) : DualNumber R →+* EpsAlg R k))
    (spMap_comp_eq R (epsIncl R a))

def epsScaleA (c : R) : DualNumber R →ₐ[R] DualNumber R :=
  { epsScaleR c with commutes' := fun r => by simp [epsScaleR] }

def epsScale (c : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR c)) (spMap_comp_eq R (epsScaleA R c))

variable {R}

def epsPt {G : Over (Sp R)} [GrpObj G] (y : epsR R ⟶ G) (k : ℕ) : epsT R k ⟶ G :=
  (List.ofFn fun a : Fin k => epsIn R a ≫ y).prod

def jetVal {G : Over (Sp R)} [GrpObj G] (y : epsR R ⟶ G) (k : ℕ) (U : G.left.Opens) (f : Γ(G.left, U)) : R :=
  topCoeff R k (valR (epsPt y k).left U f)

def tanComb {G : Over (Sp R)} [GrpObj G] {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G)) : epsR R ⟶ G :=
  (List.ofFn fun i => epsScale R (c i) ≫ v i).prod

theorem isLieComb_tanComb {G : Over (Sp R)} [GrpObj G] {m : ℕ} (c : Fin m → R) (v : Fin m → (epsR R ⟶ G)) :
    IsLieComb c v (tanComb c v) :=
  ⟨_, fun _ => rfl, rfl⟩

end Geo

def jetFun {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (y : epsR K ⟶ G) {L : LB G.left} (i₀ : L.ι) (c₀ : K)
    {r : ℕ} (b : Fin r → L.Sec) (i : ℕ) : (Fin r → K) →ₗ[K] K :=
  ∑ a, (c₀⁻¹ * jetVal y i (L.U i₀) ((b a).f i₀)) • LinearMap.proj a

theorem jetFun_apply {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (y : epsR K ⟶ G) {L : LB G.left} (i₀ : L.ι)
    (c₀ : K) {r : ℕ} (b : Fin r → L.Sec) (i : ℕ) (c : Fin r → K) :
    jetFun y i₀ c₀ b i c = ∑ a, c₀⁻¹ * jetVal y i (L.U i₀) ((b a).f i₀) * c a := by
  simp [jetFun]

def filt {K V : Type} [Field K] [AddCommGroup V] [Module K V] (j : ℕ → V →ₗ[K] K) (i : ℕ) : Submodule K V :=
  Nat.rec ⊤ (fun k F => F ⊓ LinearMap.ker (j k)) i

theorem filt_succ {K V : Type} [Field K] [AddCommGroup V] [Module K V] (j : ℕ → V →ₗ[K] K) (i : ℕ) :
    filt j (i + 1) = filt j i ⊓ LinearMap.ker (j i) := rfl

open Classical in

def rigVal {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp K)} {AA : Over (Sp (𝓞 K))} [GrpObj AA]
    {φ : P.A.left ⟶ AA.left} {MM : RigLB AA} {N : ℕ} (w : LB.Iso (MM.L.pull φ) (lbPow P.L N))
    (i₀ : (lbPow P.L N).ι) : K :=
  if h : ∃ p : PUnit → MM.L.ι,
      ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p) then
    valR (X := P.A.left) (eSec P.A) _ (w.s (i₀, h.choose)).val *
      valR (X := Sp (𝓞 K)) (spMap (algebraMap (𝓞 K) K)) _ (MM.rig.s h.choose).val
  else 0

end GlobalTheory.SecJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundTuple
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Datum
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.ConjTwist (BaseOf)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceFlatLevel

open GlobalTheory.TraceLevelPf

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem traceLevel_flat (R : RealDat D A Ks) (i : Fin D.R.m) (B : Base (Vc D i) (Wc D i)) (hB : B.Good) (hBo : BaseOf R i B)
    (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (e : G ≃* G0 B.G.Pg (Wc D i).rank)
    (hent : ∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c))
    (hU : ∀ g, e g ∈ B.G.P.H ↔ g ∈ U)
    (hchi : ∀ (u : U) (hu : e u ∈ B.G.P.H), ((B.G.P.chi ⟨e u, hu⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((ψ u : D.what₂.LLˣ) : D.what₂.LL))
    (τ : Twist D Circle) (hτ : τ.Good) (hQ : B.admitted τ.Q) (ω : PairRep (Vc D i) (Wc D i)) (hω : B.IsWeil τ.chi ω)
    (hh : GA D (Vc D i)) (P : PolF D (Wc D i).rank (Vc D i).rank) :
    levelTrace R i U ψ (series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P) = series B.F ω (B.vecFlat τ) hh P := by
  classical
  have hW : IsWeilDatumO B.F.ψ (Vc D i) (Wc D i) _ _ ω := hω
  have hlift := fun g => exists_lift_datWp hB hBo e hent g
  haveI : Fintype B.G.P.H := Fintype.ofFinite _
  have hQ' : (GlobalTheory.FlatVecSum.princ B).admitted τ.Q := hQ
  have hfθ : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) :=
    GlobalTheory.GalLift.Vec.theta_of_thetaAt hB.frame.vac.1 hB.frame.vac.2.inf
      (Base.isThetaAt_vecAt (GlobalTheory.FlatVecSum.princ_good hB) hQ' _) hB.frame.vac.2.theta
  have hsum : B.vecFlat τ = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) •
      ω (1, (hlift (e.symm p)).choose) ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) :=
    GlobalTheory.FlatVecSum.vecFlat_eq_sum_princ hB (D.sp.V_sig _) hτ hQ hω (fun p => (hlift (e.symm p)).choose) (fun p => by
      have := lifts_of_datWp hBo e hent (hlift (e.symm p)).choose_spec
      rwa [MulEquiv.apply_symm_apply] at this)
  funext x
  have hL : levelTrace R i U ψ (series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P) x =
      ∑ g, (if hg : g ∈ U then D.what₂.embLL (((ψ ⟨g, hg⟩)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) else 0) *
        series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P (x * (hlift g).choose) := by
    unfold levelTrace gaL
    rw [LinearMap.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    show Lev.actG0 _ _ _ _ _ x = _
    rw [Lev.actG0]
    split_ifs with hk
    · rw [GlobalTheory.CuspMult.EqCut.levChi_flag rfl rfl, inv_one]
      exact one_mul _
    · exact absurd (hlift g) hk
  have hR : series B.F ω (B.vecFlat τ) hh P x = ∑ p : B.G.P.H, (((B.G.P.chi p)⁻¹ : ℂˣ) : ℂ) *
      series B.F ω ((GlobalTheory.FlatVecSum.princ B).vecFlat τ) hh P (x * (hlift (e.symm p)).choose) := by
    rw [hsum, GlobalTheory.SpecFac.series_sum hB ω _ _ _ (fun p _ => hW.om_pres _ _ hfθ)]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [series_om_fin hB hW hfθ hh P x (hlift (e.symm p)).choose_spec.1]
  rw [hL, hR]
  symm
  refine Fintype.sum_of_injective (fun p : B.G.P.H => e.symm p) (fun p q hpq => Subtype.ext (e.symm.injective hpq)) _ _
    (fun g hg => ?_) (fun p => ?_)
  · rw [dif_neg, zero_mul]
    intro hgU
    exact hg ⟨⟨e g, (hU g).2 hgU⟩, e.symm_apply_apply g⟩
  · have hp : e.symm p ∈ U := (hU _).1 (by rw [MulEquiv.apply_symm_apply]; exact p.2)
    have key : ((B.G.P.chi p : ℂˣ) : ℂ) = D.what₂.embLL ((ψ ⟨e.symm p, hp⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
      have hp' : e (e.symm p) ∈ B.G.P.H := by rw [MulEquiv.apply_symm_apply]; exact p.2
      have := hchi ⟨e.symm p, hp⟩ hp'
      have hpe : (⟨e (e.symm p), hp'⟩ : B.G.P.H) = p := Subtype.ext (e.apply_symm_apply p)
      rw [hpe] at this
      exact this
    rw [dif_pos hp, Units.val_inv_eq_inv_val, key, Units.val_inv_eq_inv_val, map_inv₀]

end GlobalTheory.TraceFlatLevel

namespace GlobalTheory.BigOn.Exp.TupLe

theorem traceSt : TraceSt := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j hr hm ρ hρ hpin hlev i b ψ ω hψ hQ hω h P
  have hL := GlobalTheory.BigOn.links2_of_rows _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B i j b) := { baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin i j b with }
  refine GlobalTheory.TraceFlatLevel.traceLevel_flat (R2 p) j (ρ.B i j b) (hρ.base i j b) hBo (F2 p).P0 (F2 p).ψ0⁻¹
    ((p.R.eG.trans p.cG).trans (ρ.eG i j b)) (fun g P h h' a c => ?_) (fun g => mem_level_iff hm.2.2 hlev i j b g)
    (fun u hu => ?_) ψ hψ hQ ω hω h P
  · have e1 := hpin.grp i j b (p.cG (p.R.eG g)) P h h' a c
    rw [MulEquiv.symm_apply_apply] at e1
    exact e1
  · refine (level_chi hm.2.2 hρ hlev i j b u hu).1.trans ?_
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, map_inv₀]
    rfl

end GlobalTheory.BigOn.Exp.TupLe
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.CovTop

namespace GlobalTheory.LawsDeep

theorem goodAt_of_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (l l₂ : Level H) (b : ℕ) (hM : l₂.M = l.M * b) (hl : ∀ p : ℕ, p.Prime → l.GoodAt p) (p : ℕ) (hp : p.Prime) :
    l₂.GoodAt p := by
  rw [GlobalTheory.HostProbe.goodAt_iff l₂ hp]
  intro k hk
  have hdvd : l.M ∣ p ^ k := ⟨b, by rw [← hk]; exact hM⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  exact (GlobalTheory.HostProbe.goodAt_iff l hp).1 (hl p hp) i hi

theorem levLaws (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (hT : LawsJ T) (hj : InR D j)
    (hG : Y.Good e o) : GlobalTheory.LevGeo.Laws D j Y.d.Xo₂ Y.d.c₂ Y.U Y.dict where
  inR := hj
  host := (GlobalTheory.LevGeo.laws_core D T j hT hj).host
  dat := (GlobalTheory.LevGeo.laws_core D T j hT hj).dat
  levA := hG.lev.2
  unf := hG.unf
  chiTriv := hG.chiTriv
  dictU := by
    intro σ hσ
    obtain ⟨th, hr, hth, hd⟩ := hG.dictU σ hσ
    refine ⟨Y.Kf, th, hr, ?_, hth, hd, hG.unit σ hσ⟩
    have h₁ := hG.lev.1
    unfold DeltaDat.IsLev at h₁
    have h₂ := hT.toLawsM.pins.2.1
    unfold Par.PinLevel at h₂
    rw [h₁.2.1, h₂.1]
    exact hG.levelK
  modelW := hG.modelW

theorem laws_deep : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ),
    LawsJ T → InR D j → Y.Good e o → Laws Y.U (xiR D) := by
  intro D T j Y e o hT hj hG
  have hM : Y.d.l₂.M = T.Q.l.M * Y.d.pd := by
    have h₁ := hG.lev.1
    unfold DeltaDat.IsLev at h₁
    exact h₁.2.1
  have hgood : ∀ p : ℕ, p.Prime → Y.d.l₂.GoodAt p := fun p hp =>
    goodAt_of_mul T.Q.l Y.d.l₂ Y.d.pd hM (GlobalTheory.RecDict.level_good_and_sign D T.Q hT.toLawsM.pins).1 p hp
  exact (GlobalTheory.T.moduliLaws_of_principalLevel_fieldOfDefinition D j T.Q.H (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ Y.U Y.dict
    (levLaws D T j Y e o hT hj hG) hG.geo hgood).1

end GlobalTheory.LawsDeep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthArchSectionEqSmulOfSameWeight
section
noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem archSec_exists_eq_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → FnAlgClosed Xo c →
    ∀ (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (s t : ArchSec U x Z la), ∃ a : c.F, a ≠ 0 ∧ t.sig = a • s.sig := by
  intro E _ _ _ H Dw l Xo c r U x hU hF Z la s t
  obtain σ : c.F →+* ℂ := c.F.val.toRingHom
  have hσ₀ : GoodEmb c (goodOf c σ) := goodEmb_goodOf c σ
  set V := U (goodOf c σ) with hV

  have hinv : s.inv ∈ suppOn Z := by
    have h := mul_mem_suppOn s.inv (idem_mem_suppOn Z)
    rwa [mul_comm, s.idem_inv] at h
  have hg0 : t.sig * s.inv ∈ secZ Xo c 0 := by
    have h := mul_mem_secZ t.sig_mem s.inv_mem
    rwa [add_neg_cancel] at h
  have hgs : t.sig * s.inv ∈ suppOn Z := mul_mem_suppOn t.sig hinv

  have hb : ∀ z ∈ framesOn V Z, ‖rdU V (t.sig * s.inv) z.1 z.2‖ = t.cInf σ / s.cInf σ := by
    intro z hz
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ f : Rul Xo c, homN V x (wtOf Dw la 0) f z = ‖rdU V f z.1 z.2‖ * K := by
      refine ⟨lieFacZ Dw x (wtOf Dw la 0) *
        (V.X z.1).pnorm (modelWt V (wtOf Dw la 0) z.1) (fun _ => 1) z.2, fun f => ?_⟩
      simp only [homN, ptN, ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm, norm_one, one_mul]
      ring
    have ht : ‖rdU V t.sig z.1 z.2‖ * K = t.cInf σ := by
      rw [← hK]
      have h := t.norm_inf σ ▸ Set.mem_image_of_mem (homN V x (wtOf Dw la 0) t.sig) hz
      exact h
    have hs : ‖rdU V s.sig z.1 z.2‖ * K = s.cInf σ := by
      rw [← hK]
      have h := s.norm_inf σ ▸ Set.mem_image_of_mem (homN V x (wtOf Dw la 0) s.sig) hz
      exact h
    have hspos := s.cInf_pos σ
    have hs0 : rdU V s.sig z.1 z.2 ≠ 0 := by
      intro h0
      rw [h0, norm_zero, zero_mul] at hs
      linarith
    have hread : ∀ f g : Rul Xo c, rdU V (f * g) z.1 z.2 = rdU V f z.1 z.2 * rdU V g z.1 z.2 := by
      intro f g
      rw [AllWt.rdU_mul]
      rfl
    have hidem : rdU V (idem Z) z.1 z.2 = 1 := by
      have h := congrArg (fun f => rdU V f z.1 z.2) s.idem_sig
      simp only [hread] at h
      exact (mul_eq_right₀ hs0).mp h
    have hone : rdU V s.sig z.1 z.2 * rdU V s.inv z.1 z.2 = 1 := by
      rw [← hread, s.mul_inv, hidem]
    rw [eq_div_iff hspos.ne', ← hs, hread, norm_mul]
    calc ‖rdU V t.sig z.1 z.2‖ * ‖rdU V s.inv z.1 z.2‖ * (‖rdU V s.sig z.1 z.2‖ * K)
        = ‖rdU V t.sig z.1 z.2‖ * K * ‖rdU V s.sig z.1 z.2 * rdU V s.inv z.1 z.2‖ := by
          rw [norm_mul]; ring
      _ = t.cInf σ := by rw [ht, hone, norm_one, mul_one]
  obtain ⟨a, ha⟩ := exists_eq_smul_idem V hσ₀ (hU _ hσ₀) hF hg0 hgs hb
  have hts : t.sig = s.sig * (t.sig * s.inv) := by
    calc t.sig = idem Z * t.sig := t.idem_sig.symm
      _ = s.sig * s.inv * t.sig := by rw [s.mul_inv]
      _ = s.sig * (t.sig * s.inv) := by ring
  have hsi : s.sig * idem Z = s.sig := by rw [mul_comm]; exact s.idem_sig
  have hta : t.sig = a • s.sig := by
    rw [hts, ha, mul_smul_comm, hsi]
  by_cases ha0 : a = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    have ht0 : t.sig = 0 := by rw [hta, ha0, zero_smul]
    have hi0 : idem Z = 0 := by rw [← t.mul_inv, ht0, zero_mul]
    have hs0 : s.sig = 0 := by rw [← s.idem_sig, hi0, zero_mul]
    rw [ht0, hs0, smul_zero]
  · exact ⟨a, ha0, hta⟩

end GlobalTheory.FlatCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqSelfDualLatticesSameHermitianSpaceStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_eq_selfDual_lattices_same_hermitian_space : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (r : ℕ) (Y Y' : ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ p : ℕ, p.Prime → l.GoodAt p) → (∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0) → Y'.Ψ = Y.Ψ → Y'.Gm = Y.Gm → Y'.ξ0 = Y.ξ0 → Y'.p0 = Y.p0 → 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsLevGrp l Y' → GlobalTheory.EqCovol.IsSelfDualTr Y → GlobalTheory.EqCovol.IsSelfDualTr Y' → GlobalTheory.TrueCx.covol Y = GlobalTheory.TrueCx.covol Y' := by
  first | exact @GlobalTheory.EqCovol.SameSpace.covol_eq_of_same_space | exact GlobalTheory.EqCovol.SameSpace.covol_eq_of_same_space | (intros; apply GlobalTheory.EqCovol.SameSpace.covol_eq_of_same_space <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGrowthOnComponentNsmulStatement
section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormGrowthOnComponent_nsmul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → ∀ (Z : Comp Xo c) (G : WTZ E), Even G.2 → ∀ a : ℕ, 1 ≤ a → growthOn U Z (a • G) = (a : ℝ≥0∞) ^ dimFlag Dw * growthOn U Z G := by
  first | exact @GlobalTheory.GrowthMul.growthOn_nsmul | exact GlobalTheory.GrowthMul.growthOn_nsmul | (intros; apply GlobalTheory.GrowthMul.growthOn_nsmul <;> assumption)
end

