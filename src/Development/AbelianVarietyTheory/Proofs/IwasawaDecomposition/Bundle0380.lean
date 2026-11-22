import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0277
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1343
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorDualRepDualHighestWeightAtEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0376
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0377
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsDetRoot
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Mem.Th GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WeilTwist

variable {D : D7}

theorem exists_isDetRoot (V : HSp D) (g : GA D V) : ∃ x, IsDetRoot V g x := by
  obtain ⟨a, aval, -⟩ := GlobalTheory.Member.exists_muVal D V 1 (isHC_one D).1 (fun _ => rfl)
  exact aval.1 g

theorem twist_both {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {χ χ' ν ν' : IdC D}
    (ha : AdmE V W χ χ') (hν : IsHC D ν) (rν : ResEta D ν 0) (hν' : IsHC D ν') (rν' : ResEta D ν' 0)
    {om om' : GA D V × GA D W →* Module.End ℂ (ThS ψ V W)} (ho : IsWeilOn ψ V W χ χ' om)
    (ho' : IsWeilOn ψ V W (χ * ν) (χ' * ν') om') {g : GA D V} {h : GA D W} {x y : (AE D)ˣ}
    (hx : IsDetRoot V g x) (hy : IsDetRoot W h y) :
    om' (g, h) = (((ν' x)⁻¹ * ν y : Circle) : ℂ) • om (g, h) := by
  obtain ⟨⟨C, hC⟩, -⟩ := GlobalTheory.Mem.HeckeExp.hecke_exp_laws D
  have hmul : ∀ a b : IdC D, IsHC D a → IsHC D b → IsHC D (a * b) := fun a b k l =>
    (hC _).1 (C.mul_mem ((hC _).2 k) ((hC _).2 l))
  have ha' : AdmE V W (χ * ν) (χ' * ν') :=
    ⟨ha.1, hmul _ _ ha.2.1 hν, hmul _ _ ha.2.2.1 hν', resEta_mul ha.2.2.2.1 rν, resEta_mul ha.2.2.2.2 rν'⟩
  obtain ⟨o, hd, ht⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W χ χ' om ha ho
  obtain ⟨o', hd', ht'⟩ := GlobalTheory.Mem.WeilOriented.exists_isWeilDatumO_of_rank_eq D ψ hψ V W _ _ om' ha' ho'
  obtain ⟨o'', hd'', hv⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D ψ hψ V W χ χ' ν ν' o hd hν.1 hν'.1 rν rν'
  obtain ⟨e, -, -, he, -, -, -, hth, -⟩ := GlobalTheory.OrientedCoord.exists_coord D V W ha.1.le
  refine LinearMap.ext fun Φ => Subtype.ext (funext fun w => ?_)
  have hΦ : IsThetaFunO ψ V W fun x => Φ.1 (toTWsmall V W x) := by
    simp only [← he]
    exact (hth ψ _).2 (mem_ThS.1 Φ.2)
  have k := GlobalTheory.T.weilDatum_unique_on_thetaFunctions D ψ hψ V W _ _ o' o'' hd' hd'' (g, h) _ hΦ
  rw [ht', hv g h x y hx hy, LinearMap.smul_apply, ht] at k
  have k2 := congrFun k (e.symm w)
  simp only [← he, e.apply_symm_apply, Pi.smul_apply] at k2
  exact k2

theorem weilTwEq : ∀ D : D7, WeilTwEq D := by
  intro D ψ hψ V W χ χ' ν ha hν rν om ho
  have r1 : ResEta D 1 0 := ⟨rν.1, fun _ _ _ => by simp⟩
  refine ⟨fun om' ho' g h x hx => ?_, fun om' ho' g h x hx => ?_⟩
  · obtain ⟨y, hy⟩ := exists_isDetRoot W h
    have := twist_both hψ ha (isHC_one D) r1 hν rν ho (om' := om') (by rwa [mul_one]) hx hy
    rwa [MonoidHom.one_apply, mul_one] at this
  · obtain ⟨y, hy⟩ := exists_isDetRoot V g
    have := twist_both hψ ha hν rν (isHC_one D) r1 ho (om' := om') (by rwa [mul_one]) hy hx
    rwa [MonoidHom.one_apply, inv_one, one_mul] at this

end GlobalTheory.Mem.WeilTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenLevelFixingThetaFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_level_fixing_theta_function : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ f, IsThetaFunO ψ S T f → ∃ (U : Subgroup (GA D S)) (U' : Subgroup (GA D T)), IsOpen (U : Set (GA D S)) ∧ IsOpen (U' : Set (GA D T)) ∧ ∀ k ∈ U, k ∈ GfC S → ∀ k' ∈ U', k' ∈ GfC T → om (k, k') f = f := by
  first | exact @GlobalTheory.Mem.ThetaLevel.exists_level | exact GlobalTheory.Mem.ThetaLevel.exists_level | (intros; apply GlobalTheory.Mem.ThetaLevel.exists_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyTraceFrobeniusStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_trace_frobenius : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (ptV : ι → Option (X.nd.X i)), (∀ P x, ptV P = some x ↔ (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)) → ∀ P x, ptV P = some x → ∀ w, SplitOut X.nd i w → (heckePol X.nd i x w).map (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) = ((D.naut.frobEig (D.naut.lpTw (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) ((1 - (D.R.nV : ℝ)) / 2))).map fun α => Polynomial.X - Polynomial.C α).prod := by
  first | exact @GlobalTheory.AutPart.heckePol_map_eq_frobPol | exact GlobalTheory.AutPart.heckePol_map_eq_frobPol | (intros; apply GlobalTheory.AutPart.heckePol_map_eq_frobPol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDataAtLevelPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_data_carT_of_std : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∃ A, CarT H F A ∧ Formalism.L2.Herm.SymmetricAdelicCompatibility (I.rec7 l Z) H A ∧ Formalism.L2.Herm.SymmetricStabilizerMapCompatibility (I.rec7 l Z) H A := by
  first | exact @GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime | exact GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime | (intros; apply GlobalTheory.Mem.Col2.TC.hermitian_data_at_level_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualUpperTriangularEigenvecto
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.AlgWtF.DDHwT

section Fam

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {K : Type} [Field K]

open Classical in

def fam (τ : L →+* K) (B : GL (Fin n) K) : (L →+* K) → GL (Fin n) K := fun σ =>
  if σ = τ then B else if σ = τ.comp (IsCMField.complexConj L : L →+* L) then inside₂ K n B else 1

theorem fam_conj (τ : L →+* K) (B : GL (Fin n) K) (h : τ.comp (IsCMField.complexConj L : L →+* L) ≠ τ)
    (σ : L →+* K) : ((fam τ B (σ.comp (IsCMField.complexConj L : L →+* L)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.transpose (((fam τ B σ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hcc : ∀ σ' : L →+* K, (σ'.comp (IsCMField.complexConj L : L →+* L)).comp (IsCMField.complexConj L : L →+* L) = σ' := by
    intro σ'
    ext x
    simp [IsCMField.complexConj_apply_apply]
  have hinj : ∀ σ₁ σ₂ : L →+* K, σ₁.comp (IsCMField.complexConj L : L →+* L) = σ₂.comp (IsCMField.complexConj L : L →+* L) → σ₁ = σ₂ := by
    intro σ₁ σ₂ e
    rw [← hcc σ₁, e, hcc]
  by_cases h1 : σ = τ
  · subst h1
    simp only [fam, h, if_false, if_true]
    rfl
  · by_cases h2 : σ = τ.comp (IsCMField.complexConj L : L →+* L)
    · subst h2
      simp only [fam, hcc, if_true, h]
      simp [inside₂]
    · have h3 : σ.comp (IsCMField.complexConj L : L →+* L) ≠ τ := by
        intro e; apply h2; rw [← e, hcc]
      have h4 : σ.comp (IsCMField.complexConj L : L →+* L) ≠ τ.comp (IsCMField.complexConj L : L →+* L) :=
        fun e => h1 (hinj _ _ e)
      simp [fam, h1, h2, h3, h4]

theorem fam_eval (τ : L →+* K) (B : GL (Fin n) K) :
    (fun p : (L →+* K) × Fin n × Fin n => ((fam τ B p.1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) p.2.1 p.2.2) =
      Formalism.L2.NX.evPtF (IsCMField.complexConj L : L →+* L) τ B := by
  funext p
  simp only [fam, Formalism.L2.NX.evPtF]
  split_ifs <;> simp_all [inside₂, Matrix.one_apply]

end Fam

section Eig

open Formalism.L2.DIV

variable {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K]

theorem bVVfun_mem (lam : ι → DomWeight n) (j : VVIdx lam) : bVVfun K lam j ∈ VV K lam := by
  rw [← (bVVfun_spec K lam).2]
  exact Submodule.subset_span ⟨j, rfl⟩

def wOf (lam : ι → DomWeight n) (u : VVIdx lam → K) : Pol K ι n := ∑ j, u j • bVVfun K lam j

theorem wOf_mem (lam : ι → DomWeight n) (u : VVIdx lam → K) : wOf lam u ∈ VV K lam :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bVVfun_mem lam j)

theorem wOf_ne (lam : ι → DomWeight n) (u : VVIdx lam → K) (hu : u ≠ 0) : wOf lam u ≠ 0 := by
  intro h0
  apply hu
  funext j
  exact Fintype.linearIndependent_iff.mp (bVVfun_spec K lam).1 u h0 j

theorem wOf_eig (lam : ι → DomWeight n) (M : ι → Matrix (Fin n) (Fin n) K)
    (hMV : ∀ F ∈ VV K lam, Formalism.GradedWeylDivisibility.blockAct K M F ∈ VV K lam) (c χ : K) (hc : c ≠ 0) (u : VVIdx lam → K)
    (h : ∀ i, ∑ j, c * DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M (bVVfun K lam j)) * u j = χ * u i) :
    Formalism.GradedWeylDivisibility.blockAct K M (wOf lam u) = (c⁻¹ * χ) • wOf lam u := by
  classical
  set w := wOf lam u with hw
  set F : VV K lam := ⟨_, hMV w (wOf_mem lam u)⟩ with hF
  have hco : ∀ i, (bVV K lam).repr F i = c⁻¹ * χ * u i := by
    intro i
    have e1 : c * DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M w) = χ * u i := by
      rw [← h i, hw, wOf, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, map_smul, smul_eq_mul]
      ring
    have e2 : DDHw.coord lam i (Formalism.GradedWeylDivisibility.blockAct K M w) = (bVV K lam).repr F i := DDHw.coord_spec lam i F
    rw [← e2, mul_assoc, ← e1, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hsum := congrArg Subtype.val ((bVV K lam).sum_repr F)
  rw [Submodule.coe_sum] at hsum
  simp only [Submodule.coe_smul, bVV_coe, hco] at hsum
  show (F : Pol K ι n) = _
  rw [← hsum, hw, wOf, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]

theorem blockAct_mem [DecidableEq ι] (lam : ι → DomWeight n) (τ₀ : ι) (B : GL (Fin n) K) (F : Pol K ι n)
    (hF : F ∈ VV K lam) :
    Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) F ∈ VV K lam := by
  set g : ι → GL (Fin n) K := fun τ => if τ = τ₀ then B else 1 with hg
  have hgM : (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose) =
      fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1 := by
    funext τ
    by_cases h : τ = τ₀ <;> simp [hg, h]
  have hdet : detTwK lam g ≠ 0 := by
    unfold detTwK
    exact Finset.prod_ne_zero_iff.2 fun τ _ => Units.ne_zero _
  have e : actP lam g F = detTwK lam g •
      Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) F := by
    rw [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, trAct, hgM]
  have h1 := polyAction_mem_VV lam g hF
  rw [e] at h1
  exact (Submodule.smul_mem_iff _ hdet).1 h1

end Eig

section Main

open Formalism.L2.DIV
open scoped Matrix

theorem hw_eigvec_transport : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (K : Type) [Field K] [CharZero K] (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb →
    ∀ (τ₀ : ι) (mu : Fin n → ℤ),
      NX.HWAtF (IsCMField.complexConj L : L →+* L) (GlobalTheory.AlgWtF.wtRepF emb lam).dual (emb τ₀) mu →
      ∃ w : Formalism.L2.DIV.Pol K ι n, w ∈ Formalism.L2.DIV.VV K lam ∧ w ≠ 0 ∧
        ∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
          Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) w =
            ((detPow K n B (lam τ₀).detShift)⁻¹ * ∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • w := by
  intro L _ _ _ n ι _ _ K _ _ emb lam hd τ₀ mu hH
  classical
  obtain ⟨ι', _, _, b', P', hP', v, hv, hB⟩ := hH
  have hinj := hd.1
  have hcm := hd.2
  set bD := DDHw.bDD (K := K) lam with hbD
  set Q : Matrix ι' (VVIdx lam) K := b'.toMatrix bD with hQ
  set Q' : Matrix (VVIdx lam) ι' K := bD.toMatrix b' with hQ'
  have hQQ : Q * Q' = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hQQ' : Q' * Q = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hrat : ∀ a a', ∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n →
      MvPolynomial.eval (fun p : (L →+* K) × Fin n × Fin n => p.1 ((γ₀ : Matrix (Fin n) (Fin n) L) p.2.1 p.2.2))
        (P' a a' - ∑ i, ∑ j, MvPolynomial.C (Q a i * Q' j a') * DDHw.tenPF emb lam i j) = 0 := by
    intro a a' γ₀ hγ
    obtain ⟨γ, rfl⟩ := ratHom_surjective L n γ₀ hγ
    have hm : (((γ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        ((ratHom γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
      rw [show ratHom γ = ratFun γ from rfl, ← incGL_ratFun γ]
      rfl
    have h1 := congrFun (congrFun (hP' γ _ hm) a) a'
    have h2 : LinearMap.toMatrix b' b' ((wtRepF emb lam).dual γ) =
        Q * LinearMap.toMatrix bD bD ((wtRepF emb lam).dual γ) * Q' :=
      (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b' bD b' bD _).symm
    rw [hbD, DDHw.dd_toMatrix, DDHw.tenRepF_toMatrix emb lam γ _ hm] at h2
    rw [map_sub, ← h1, h2, map_sum]
    simp only [map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C, Matrix.mul_apply, Finset.sum_mul]
    rw [sub_eq_zero, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    erw [Matrix.mul_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set u : VVIdx lam → K := Q' *ᵥ v with hu
  have hu0 : u ≠ 0 := by
    intro h0
    apply hv
    have e : Q *ᵥ u = v := by rw [hu, Matrix.mulVec_mulVec, hQQ, Matrix.one_mulVec]
    rw [← e, h0, Matrix.mulVec_zero]
  refine ⟨wOf lam u, wOf_mem lam u, wOf_ne lam u hu0, fun B hBt => ?_⟩
  have hne : (emb τ₀).comp (IsCMField.complexConj L : L →+* L) ≠ emb τ₀ := fun h' => hcm τ₀ τ₀ h'.symm
  set T : Matrix (VVIdx lam) (VVIdx lam) K := Matrix.of fun i j =>
    MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (DDHw.tenPF emb lam i j) with hT
  have hev : ∀ a a', MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (P' a a') =
      ∑ i, ∑ j, Q a i * Q' j a' * T i j := by
    intro a a'
    have h0 := GlobalTheory.T.zariskiDense_rationalPoints_definiteUnitary_charZero L n K _ (hrat a a') (fam (emb τ₀) B) (fam_conj _ B hne)
    rw [fam_eval, map_sub, sub_eq_zero] at h0
    rw [h0, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, hT, Matrix.of_apply]
  have hmat : (Matrix.of fun a a' => MvPolynomial.eval (NX.evPtF (IsCMField.complexConj L : L →+* L) (emb τ₀) B) (P' a a')) =
      Q * T * Q' := by
    ext a a'
    rw [Matrix.of_apply, hev, Matrix.mul_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  set χ : K := ∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a with hχ
  have hTu : T *ᵥ u = χ • u := by
    have h1 := hB B hBt
    rw [hmat] at h1
    have e : Q' *ᵥ ((Q * T * Q') *ᵥ v) = T *ᵥ u := by
      rw [hu, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQQ', Matrix.one_mul]
    rw [← e, h1, Matrix.mulVec_smul]
  set c : K := detPow K n B (lam τ₀).detShift with hc
  have hc0 : c ≠ 0 := by
    rw [hc, detPow]
    exact Units.ne_zero _
  have hM : (fun τ => (Matrix.of fun a b => NX.evPtF (DDHw.cL L) (emb τ₀) B (emb τ, a, b)).transpose) =
      fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1 := by
    funext τ
    split_ifs with hτ
    · rw [hτ, DDHw.evPtF_self]
    · rw [DDHw.evPtF_other _ _ _ _ (fun h' => hτ (hinj h')) (hcm τ τ₀), Matrix.transpose_one]
  have hTe : ∀ i j, T i j = c * DDHw.coord lam i
      (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then (B : Matrix (Fin n) (Fin n) K).transpose else 1) (bVVfun K lam j)) := by
    intro i j
    rw [hT, Matrix.of_apply, DDHw.tenPF_eval]
    erw [DDHw.detTwistPolynomial_eval_embeddingPoint emb hd lam τ₀ B]
    rw [← hM]
  refine wOf_eig lam _ (blockAct_mem lam τ₀ B) c χ hc0 u fun i => ?_
  have := congrFun hTu i
  simp only [Matrix.mulVec, dotProduct, hTe, Pi.smul_apply, smul_eq_mul] at this
  exact this

end Main

end GlobalTheory.AlgWtF.DDHwT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelLiftGelfandInvariantFiniteOfFiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelLift_gelfandInvariantFinite_of_finite : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∃ Z : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ Z ∧ F ∈ Z ∧ ∀ τ k, ∀ f ∈ Z, gelf θ V τ k f ∈ Z) → ∀ f, ∃ Z : Submodule ℂ (GA D W → ℂ), FiniteDimensional ℂ Z ∧ (fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∈ Z ∧ ∀ τ k, ∀ φ ∈ Z, gelf θ W τ k φ ∈ Z := by
  first | exact @GlobalTheory.Mem.LiftFin.lift_zfin | exact GlobalTheory.Mem.LiftFin.lift_zfin | (intros; apply GlobalTheory.Mem.LiftFin.lift_zfin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeInIsotypicSup
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeightCounting.FormsStep

theorem descend_exists (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    ∃ Φ : S.WL j →+ FmT D T S i j b, (∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x) ∧
      (∀ (f : Module.End D.what₂.LL (S.WL j)) (fr : Module.End S.Ks ↥(WKr D S j)),
        (∀ w : ↥(WKr D S j), (fr w : S.WL j) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange (KT D T i b) fr (Φ x)) ∧
      ∀ w : ↥(WKr D S j), Φ (w : S.WL j) = (1 : KT D T i b) ⊗ₜ[S.Ks] w := by
  obtain ⟨n, bs, hb, -, hKs, hLi, hLs⟩ := In.ks j h1 h2
  have hW : WKr D S j = (S.A j).WK := WKr_of D S h1 h2
  exact GlobalTheory.T.exists_semilinear_descent_to_baseChange_of_form D.LL0 S.kKs S.kKs_spec (WKr D S j) bs (fun k => hW ▸ hb k) (hW ▸ hKs) hLi hLs
    (KT := KT D T i b) (readK D T i b) (fun s => rfl)

theorem descend_actL (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (hf : ∀ (f : Module.End D.what₂.LL (S.WL j)) (fr : Module.End S.Ks ↥(WKr D S j)),
        (∀ w : ↥(WKr D S j), (fr w : S.WL j) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange (KT D T i b) fr (Φ x))
    (g : G0g D.nd) (x : S.WL j) :
    Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x) := by
  have hcR : cR D S In.chi j (S.eG.symm g) = chiL S j (In.chi j h1 h2) (S.eG.symm g) := by
    unfold cR; rw [dif_pos ⟨h1, h2⟩]
  change _ = ((readK D T i b (cR D S In.chi j (S.eG.symm g)))⁻¹ •
    Module.End.baseChangeHom S.Ks (KT D T i b) ↥(WKr D S j) (rhoR D S In.rho j (S.eG.symm g))) (Φ x)
  rw [hcR]
  have e1 : actL D S j g x = (((chiL S j (In.chi j h1 h2) (S.eG.symm g))⁻¹ : ↥D.LL0) : D.what₂.LL) •
      (S.A j).ρ (S.eG.symm g) x := by
    simp only [actL, chiL, IntermediateField.coe_inv, LinearMap.smul_apply]
  rw [e1, hc, hf ((S.A j).ρ (S.eG.symm g)) (rhoR D S In.rho j (S.eG.symm g)) (fun w => rfl), map_inv₀]
  rfl

theorem descend_eSum (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (x : S.WL j) :
    Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x) := by
  haveI : Fintype (G0g D.nd) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum]
  unfold eGT
  rw [MonoidAlgebra.lift_apply]
  simp only [eAlgT, MonoidAlgebra.coeff_ofCoeff]
  rw [Finsupp.sum_fintype _ _ (by intro; simp), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, hc, ha]
  simp

theorem descend_mem_V0T (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (ha : ∀ (g : G0g D.nd) (x : S.WL j), Φ (actL D S j g x) = actGT D T S In.rho In.chi i j b g (Φ x))
    (he : ∀ x : S.WL j, Φ ((∑ᶠ g : G0g D.nd, ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) • actL D S j g) x) =
      eGT D T S In.rho In.chi i j b (Φ x))
    (x : S.WL j) (hx : x ∈ goodL D S In.θ j) : Φ x ∈ V0T D T S In.rho In.chi In.θ i j b := by
  rw [goodL, Submodule.mem_inf, Submodule.mem_iInf] at hx
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨Φ x, ?_, ?_⟩
  · rw [SetLike.mem_coe, Fm0T, Submodule.mem_iInf]
    intro u
    rw [LinearMap.mem_ker, LinearMap.sub_apply]
    have h := hx2 u
    rw [Module.End.mem_eigenspace_iff] at h
    rw [LinearEquiv.coe_coe, ← ha, h, hc]
    simp [psiUT]
  · rw [Module.End.mem_eigenspace_iff, one_smul] at hx1
    rw [← he, hx1]

theorem descend_mem_eigenspace (D : D7) (T : TwR D.LL0 D.nd) (S : RatDat D.ntw) (In : RatIn D S) (i : T.Tw) (j : ℕ) (b : Bool)
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Φ : S.WL j →+ FmT D T S i j b)
    (hc : ∀ (c : ↥D.LL0) (x : S.WL j), Φ ((c : D.what₂.LL) • x) = readT D T i b c • Φ x)
    (hf : ∀ (f : Module.End D.what₂.LL (S.WL j)) (fr : Module.End S.Ks ↥(WKr D S j)),
        (∀ w : ↥(WKr D S j), (fr w : S.WL j) = f w) →
        ∀ x, Φ (f x) = LinearMap.baseChange (KT D T i b) fr (Φ x))
    (k : ℕ) (P : PlE D.host) (μ : ↥D.LL0) (x : S.WL j)
    (hx : x ∈ Module.End.eigenspace (In.hL j k P) (μ : D.what₂.LL)) :
    Φ x ∈ Module.End.eigenspace (hkT D T S In i j b k P)
      (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b μ) := by
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  have hw : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    split_ifs with h
    · rfl
    · exact absurd ⟨h1, h2⟩ h
  change ((show KT D T i b from algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i)) ^ k •
    LinearMap.baseChange (KT D T i b) (hLr D S In j k P) (Φ x) : KT D T i b ⊗[S.Ks] ↥(WKr D S j)) = _
  rw [← hf _ _ hw, hx, hc]
  exact smul_smul _ _ _

theorem goodPart_le_iSup_eigen : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool), 1 ≤ j → j ≤ D.R.m →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          V0T D T S In.rho In.chi In.θ i j b ⊓
            ⨅ (k : ℕ) (P : PlE D.host) (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ T.S0 i),
              Module.End.eigenspace (hkT D T S In i j b k P)
                (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  intro D cf jE A S In b0 b1 Sx T Sp hSb hstar i j b hj1 hj2
  obtain ⟨Φ, hc, hf, hw⟩ := descend_exists D T S In i j b hj1 hj2
  have ha := descend_actL D T S In i j b hj1 hj2 Φ hc hf
  have he := descend_eSum D T S In i j b Φ hc ha
  refine (GlobalTheory.T.V0T_le_span_image_goodL D S In T i j b hj1 hj2 (eIdem_all D) Φ hc ha he hw).trans (Submodule.span_le.mpr ?_)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [SetLike.mem_coe]
  refine Submodule.iSup_induction (motive := fun y => Φ y ∈ _) _ (In.span j hj1 hj2 hx) ?_ ?_ ?_
  · intro σ y hy
    refine Submodule.iSup_induction (motive := fun y => Φ y ∈ _) _ hy ?_ ?_ ?_
    · intro hσ z hz
      refine Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem hσ ?_)
      rw [Submodule.mem_inf] at hz ⊢
      refine ⟨descend_mem_V0T D T S In i j b Φ hc ha he z hz.1, ?_⟩
      have hz2 := hz.2
      simp only [Submodule.mem_iInf] at hz2 ⊢
      intro k P hkP
      have hPb : P ∉ In.Sb := fun hP => hkP.2.2.2 (by
        rw [← Finset.mem_coe, Sp.ringSpec_excludedPlaces_eq i]
        exact Or.inr (Finset.mem_coe.mpr (hSb hP)))
      exact descend_mem_eigenspace D T S In i j b hj1 hj2 Φ hc hf k P _ z (hz2 k P ⟨hkP.1, hkP.2.1, hkP.2.2.1, hPb⟩)
    · rw [map_zero]; exact zero_mem _
    · intro y z hy hz; rw [map_add]; exact add_mem hy hz
  · rw [map_zero]; exact zero_mem _
  · intro y z hy hz; rw [map_add]; exact add_mem hy hz

end GlobalTheory.HeightCounting.FormsStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalEmbeddingWeilActionFiniteExtensionStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_embedding_weil_action_finite_extension : ∀ (E K Ω : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra E K] [IsScalarTower E K Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι → ∀ L : IntermediateField (w.adicCompletion E) (Kbar w), FiniteDimensional (w.adicCompletion E) L → (∀ (σ : Weil h) (g : GalLoc w), Lifts ι g σ → ((∀ z ∈ L, g z = z) ↔ ∀ x : K, (σ : G E Ω) (algebraMap K Ω x) = algebraMap K Ω x)) → L = IntermediateField.adjoin (w.adicCompletion E) (Set.range fun x : K => ι (algebraMap K Ω x)) := by
  first | exact @GlobalTheory.LocDec.eq_adjoin_of_fixing_iff_weil | exact GlobalTheory.LocDec.eq_adjoin_of_fixing_iff_weil | (intros; apply GlobalTheory.LocDec.eq_adjoin_of_fixing_iff_weil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothModelsOnThetaTargetsStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_kType_smooth_models_on_theta_targets : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i σ, LowSm (R.MW i σ) := by
  first | exact @GlobalTheory.LowSmooth.lowSm_MW | exact GlobalTheory.LowSmooth.lowSm_MW | (intros; apply GlobalTheory.LowSmooth.lowSm_MW <;> assumption)
end

