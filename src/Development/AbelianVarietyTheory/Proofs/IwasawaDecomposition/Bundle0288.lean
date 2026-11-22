import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TilLatticesOfLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyLiftObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0231
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0034
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0222
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0268
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0269
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinors
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.MinorHarmonic

theorem pderiv_comm {σ R : Type*} [CommRing R] (i j : σ) (f : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j f) = MvPolynomial.pderiv j (MvPolynomial.pderiv i f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    have h : ∀ a b : σ, MvPolynomial.pderiv a (MvPolynomial.pderiv b (MvPolynomial.X k : MvPolynomial σ R)) = 0 := by
      intro a b
      rw [MvPolynomial.pderiv_X]
      by_cases hk : k = b
      · subst hk; simp
      · simp [Pi.single_eq_of_ne hk]
    simp only [Derivation.leibniz, map_add, smul_eq_mul, hp, h]
    ring

def ker {σ : Type*} (v : σ) : Subring (MvPolynomial σ ℂ) where
  carrier := {f | MvPolynomial.pderiv v f = 0}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [Derivation.leibniz, ha, hb]
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    simp [ha, hb]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [ha]

theorem det_mem {R : Type*} [CommRing R] (S : Subring R) {k : ℕ} (M : Matrix (Fin k) (Fin k) R)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

variable {D : D7} {m n : ℕ}

theorem varF_mem (τ τ' : D.what₂.Tau) (a : Fin m) (c : Fin n) (i j : ℕ)
    (h : τ' = τ → i = a → j = c → False) :
    (varF τ' i j : MvPolynomial (FVar D m n) ℂ) ∈ ker ((τ, a, c) : FVar D m n) := by
  classical
  unfold varF
  split_ifs with h1
  · show MvPolynomial.pderiv _ _ = 0
    apply MvPolynomial.pderiv_X_of_ne
    intro he
    simp only [Prod.mk.injEq] at he
    exact h he.1 (congrArg Fin.val he.2.1) (congrArg Fin.val he.2.2)
  · exact Subring.zero_mem _

theorem delta_mem (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (hpq : ∀ τ, p τ + q τ ≤ n)
    (τ : D.what₂.Tau) (a : Fin m) (c : Fin n)
    (h : ((a : ℕ) < p τ ∧ p τ ≤ c) ∨ (p τ ≤ (a : ℕ) ∧ (c : ℕ) < p τ)) :
    (delta p q ap am : MvPolynomial (FVar D m n) ℂ) ∈ ker ((τ, a, c) : FVar D m n) := by
  unfold delta deltaAt
  refine Subring.prod_mem _ fun τ' _ => Subring.mul_mem _ ?_ ?_
  · refine Subring.prod_mem _ fun i hi => Subring.pow_mem _ ?_ _
    refine det_mem _ _ fun α β => varF_mem τ τ' a c _ _ ?_
    rintro rfl h1 h2
    have := Finset.mem_range.1 hi
    have := α.2
    have := β.2
    omega
  · refine Subring.prod_mem _ fun i hi => Subring.pow_mem _ ?_ _
    refine det_mem _ _ fun α β => varF_mem τ τ' a c _ _ ?_
    rintro rfl h1 h2
    have := Finset.mem_range.1 hi
    have := hpq τ'
    omega

theorem laplacian_delta : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ), (∀ τ, p τ + q τ ≤ n) → ∀ τ (a b : Fin m), p τ ≤ (a : ℕ) → (b : ℕ) < p τ → ∑ c : Fin n, MvPolynomial.pderiv (τ, a, c) (MvPolynomial.pderiv (τ, b, c) (delta p q ap am : PolF D m n)) = 0 := by
  intro D m n p q ap am hpq τ a b ha hb
  refine Finset.sum_eq_zero fun c _ => ?_
  rcases lt_or_ge (c : ℕ) (p τ) with hc | hc
  · rw [pderiv_comm]
    have : MvPolynomial.pderiv (τ, a, c) (delta p q ap am : PolF D m n) = 0 :=
      delta_mem p q ap am hpq τ a c (Or.inr ⟨ha, hc⟩)
    rw [this, map_zero]
  · have : MvPolynomial.pderiv (τ, b, c) (delta p q ap am : PolF D m n) = 0 :=
      delta_mem p q ap am hpq τ b c (Or.inl ⟨hb, hc⟩)
    rw [this, map_zero]

end GlobalTheory.MinorHarmonic

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtOfFactors
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Mem.Col2.TC

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def latSD (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) : (letI := B.host.cmStar; SDLat B.host.E (B.R.N i)) :=
  letI := B.host.cmStar
  ⟨((I.stp u a i).rep c).1.1.deco.1.N, GlobalTheory.SeamSelfDual.isSDLat_of_isSdLat _
    ⟨((I.stp u a i).rep c).1.1.deco.2.lat, ((I.stp u a i).rep c).1.1.deco.2.uni⟩⟩

def mtOf (a : I.ι) (j : ℕ) : (I.rec7 l Z).Dt →* ℂˣ :=
  if 1 ≤ j ∧ j ≤ B.R.m then
    (I.rec7 l Z).muTil j * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) else (I.rec7 l Z).muTil j

theorem mtOf_factors (u : B.Word) (a : I.ι) : GL3Theta.CarriesTupleCharacters (I.rec7 l Z) ((I.rec7 l Z).chTw u a) (I.mtOf l Z a)
    (fun i c => detPt B.host I.SQ ((I.stp u a i).rep c).1.1) := by
  intro i hi
  have hm : 1 ≤ i + 1 ∧ i + 1 ≤ B.R.m := ⟨by omega, hi⟩
  refine ⟨fun c => ?_, fun c => ?_⟩
  · show ((rhoAt I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ) = _
    rw [rhoAt_eq]
    simp only [GL3Theta.rhoOf, mtOf, if_pos hm]
    rfl
  · show ((rhoAt' I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ) = _
    rw [rhoAt'_eq]
    simp only [GL3Theta.rhoOf', mtOf, if_pos hm]
    rfl

def objOf (hok : I.Ok) (Qp : I.ι → Finset ℕ) (u : B.Word) (a : I.ι) : GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a) :=
  letI := B.host.cmStar
  { mt := I.mtOf l Z a
    L0 := fun i => ⟨GlobalTheory.Glob.IntegralWittCoefficients.Model.stdLat _ _, GlobalTheory.Glob.IntegralWittCoefficients.Model.isSDLat_std _ _⟩
    lattice_integral_coordinates := fun i x => GlobalTheory.Glob.IntegralWittCoefficients.Model.mem_stdLat x
    lat := fun i c => I.latSD u a i c
    dt := fun i c => detPt B.host I.SQ ((I.stp u a i).rep c).1.1
    dt_lat := fun i c => GlobalTheory.Mem.Col2.mk_detPt_eq_relDetQ B.R B.host _ _ _ _ I.SQ _ (GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).1
    c13 := I.mtOf_factors l Z u a
    frm := fun i y => y.1
    frm_inj := fun i _ => Subtype.val_injective
    frm_range := fun i _ f => ⟨by
        rintro ⟨y, rfl⟩ τ
        exact (y.2 τ).ne_zero, fun h => ⟨⟨f, fun τ => isUnit_iff_ne_zero.2 (h τ)⟩, rfl⟩⟩
    frm_de := fun _ _ _ _ => rfl
    dgen := I.J.cD
    dgen_gen := hok.amb_ok.dgen
    S := insert (B.T u) ({B.host.g 0, B.host.g 1} ∪ Qp a)
    Th := fun i c c' => I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c') }

theorem objOf_unf (hok : I.Ok) (Qp : I.ι → Finset ℕ) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) :
    UnfIsAll (I.objOf l Z hok Qp u a) i := by
  intro c c' Q
  have e0 : ∀ (n : ℕ) (P : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N n)) ℂ),
      frPoly (I.objOf l Z hok Qp u a) n P = fnOf (Gr B.fields.emb B.embLL (B.R.N n)) 0 1 P := by
    intro n P
    funext y
    simp [frPoly, GL3Theta.evFr, fnOf, objOf]
    rfl
  have e1 : frInv (I.objOf l Z hok Qp u a) i (frPoly (I.objOf l Z hok Qp u a) i Q) = Q :=
    LinearMap.congr_fun (frInv_spec (I.objOf l Z hok Qp u a) hi) Q
  show fnOf _ 0 1 (jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 _ _)) 0 (polOf _ 0 (fr0 _ _ _) (frPoly (I.objOf l Z hok Qp u a) i Q))) =
    frPoly (I.objOf l Z hok Qp u a) (i + 1) (jetMap _ _ (frInv (I.objOf l Z hok Qp u a) i (frPoly (I.objOf l Z hok Qp u a) i Q)))
  have e2 : polOf (Gr B.fields.emb B.embLL (B.R.N i)) 0 (fr0 B.fields.emb B.embLL (B.R.N i))
      (frPoly (I.objOf l Z hok Qp u a) i Q) = Q :=
    (congrArg _ (e0 i Q)).trans (GlobalTheory.TilClass.polOf_fnOf_one B.fields.emb B.embLL 0 Q)
  refine (congrArg (fun P => fnOf (Gr B.fields.emb B.embLL (B.R.N (i + 1))) 0 1
    (jetMap (jetC I.J.cD (I.th u a i c.1 c'.1 ((I.stp u a i).rep c) ((I.stp u a (i + 1)).rep c'))) 0 P)) e2).trans ?_
  rw [e1, e0 (i + 1)]
  rfl

theorem lift_objects : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ Qp : I.ι → Finset ℕ, ∃ O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a), I.StdO l Z Qp O ∧ ∀ u a i, i < B.R.m → UnfIsAll (O u a) i := by
  intro B X I hok _ l Z Qp
  refine ⟨I.objOf l Z hok Qp, ⟨fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩, fun u a i hi => I.objOf_unf l Z hok Qp u a i hi.le⟩

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

theorem nefFib_of_primeField : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (L : HermLB p),
    (∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (q : ℕ) [Fact q.Prime]
      [Algebra (ZMod q) Γ(Z, ⊤)], topologicalKrullDim Z = 1 → 0 ≤ topSelfIntersection (ZMod q) (L.B.pull i) 1) →
    ArInt.NefFib L := by
  intro k _ X p L h Z i _ _ κ _ _ _ hdim
  haveI : Fintype κ := Fintype.ofFinite κ
  haveI hq : Fact (ringChar κ).Prime := ⟨CharP.char_is_prime κ (ringChar κ)⟩
  letI : Algebra (ZMod (ringChar κ)) κ := ZMod.algebra κ (ringChar κ)
  letI : Algebra (ZMod (ringChar κ)) Γ(Z, ⊤) :=
    ((algebraMap κ Γ(Z, ⊤)).comp (algebraMap (ZMod (ringChar κ)) κ)).toAlgebra
  haveI : IsScalarTower (ZMod (ringChar κ)) κ Γ(Z, ⊤) := IsScalarTower.of_algebraMap_eq' rfl
  have h1 := h Z i (ringChar κ) hdim
  have e := GlobalTheory.T.lineBundleIntersectionNumber_groundFieldChange (ZMod (ringChar κ)) κ Z (structureModule Z) (fun _ : Fin 1 => L.B.pull i)
  rw [topSelf_def] at h1 ⊢
  rw [e] at h1
  haveI : Module.Finite (ZMod (ringChar κ)) κ := Module.Finite.of_finite
  have hpos : (0 : ℤ) < (Module.finrank (ZMod (ringChar κ)) κ : ℤ) := by
    exact_mod_cast Module.finrank_pos
  exact (mul_nonneg_iff_of_pos_left hpos).mp h1

end GlobalTheory.ArInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotTwistPlaceReferenceTuple
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem not_underQ_mu0 : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ v : HeightOneSpectrum (𝓞 B.host.F), ¬ I.UnderQ I.mu0 v := by
  intro B X I _ v ⟨P, hP, _⟩
  have e : P ∈ (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) := I.twistPrimes_reference_tuple_eq_empty ▸ hP
  simp at e

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormPeriodRelation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.ClassScalar

open GlobalTheory.Ker

variable {D : D7}

theorem fmt_mul_inv (V : HSp D) (g : GA D V) : fmt V g * fmt V g⁻¹ = 1 := by
  simp only [fmt, Formalism.L2.Theta.mt]
  rw [← Matrix.map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isMov_hLat (V : HSp D) (hL : Bridge.hLat V 1 = stdL D.host.E V.rank) (g : GA D V) :
    IsMov (fmt V g) (stdL D.host.E V.rank) (Bridge.hLat V (fin V g)) := by
  have hs : Submodule.span D.host.E (stdL D.host.E V.rank : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun D.host.E (Fin V.rank)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, (Pi.basisFun_apply _ _ i).symm⟩
  obtain ⟨⟨L, hL', hm⟩, h2⟩ := (isMov_laws D V.rank _ ⟨Submodule.fg_span (Set.finite_range _), hs⟩).2.2.2 _ _
    (fmt_mul_inv V g)
  have h3 := (isMov_laws D V.rank L hL').1
  have h4 : fmt V g⁻¹ * fmt V g = 1 := mul_eq_one_comm.1 (fmt_mul_inv V g)
  have key : Bridge.hLat V (fin V g) = L := by
    rw [Bridge.hLat, ← GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, hL, ← Submodule.span_eq L]
    congr 1
    ext x
    change fmt V g⁻¹ *ᵥ toAf x ∈ hatV (stdL D.host.E V.rank) ↔ x ∈ L
    rw [← h3, hm]
    constructor
    · intro hx
      exact ⟨_, hx, by rw [Matrix.mulVec_mulVec, fmt_mul_inv, Matrix.one_mulVec]⟩
    · rintro ⟨u, hu, e⟩
      rwa [e, Matrix.mulVec_mulVec, h4, Matrix.one_mulVec]
  rwa [key]

noncomputable abbrev cf (D : D7) : AfE D →+* AfE D := sigR (Af D.host.F) D.sp.cm.sig

theorem cf_cf (x : AfE D) : cf D (cf D x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun t => a ⊗ₜ[D.host.F] t) (star_star x)
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]

theorem finPart_cA (x : AE D) : finPart D (cA D x) = cf D (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, RingHom.map_add, hx, hy]

theorem conj_mem_hatV {k : ℕ} {L L' : Lt D.host.E k} (h : ∀ v ∈ L, (fun j => cc (v j)) ∈ L') {u : Fin k → AfE D}
    (hu : u ∈ hatV L) : cf D ∘ u ∈ hatV L' := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a, ha, _, h x hx, rfl⟩
  | zero => convert (hatV L').zero_mem; funext i; exact RingHom.map_zero _
  | add a b _ _ ha hb => convert add_mem ha hb; funext i; exact RingHom.map_add _ _ _
  | neg a _ ha => convert neg_mem ha; funext i; exact RingHom.map_neg _ _

theorem isMov_conj {V : HSp D} {g : GA D V} {L L' : Lt D.host.E V.rank} (h : IsMov (fmt V g) (stdL D.host.E V.rank) L)
    (hc : ∀ v, v ∈ L' ↔ (fun j => cc (v j)) ∈ L) : IsMov (fmtC V g) (stdL D.host.E V.rank) L' := by
  have c4 : fmtC V g = (fmt V g).map (cf D) := by ext i j; exact finPart_cA _
  have c5 : ∀ v ∈ stdL D.host.E V.rank, (fun j => cc (v j)) ∈ stdL D.host.E V.rank := fun v hv => by
    rw [← GenLatCmp.std_eq, GenLatCmp.mem_std] at hv ⊢
    exact fun i => Base.isIntegral_cc (hv i)
  have c6 (u : Fin V.rank → AfE D) : cf D ∘ cf D ∘ u = u := funext fun i => cf_cf _
  have c7 (u : Fin V.rank → AfE D) : fmtC V g *ᵥ (cf D ∘ u) = cf D ∘ (fmt V g *ᵥ u) := by
    rw [c4]; funext i; exact (RingHom.map_mulVec (cf D) _ _ i).symm
  intro u
  constructor
  · intro hu
    obtain ⟨u₀, h0, e⟩ := (h _).1 (conj_mem_hatV (fun v hv => (hc v).1 hv) hu)
    exact ⟨_, conj_mem_hatV c5 h0, by rw [c7, ← e, c6]⟩
  · rintro ⟨u₀, h0, rfl⟩
    rw [← c6 u₀, c7]
    refine conj_mem_hatV (fun v hv => (hc _).2 ?_) ((h _).2 ⟨_, conj_mem_hatV c5 h0, rfl⟩)
    simpa [cc] using hv

theorem exists_isDetAt {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) : ∃ y, IsDetAt e V g y :=
  ⟨Units.mkOfMulEqOne (e * (Formalism.L2.Theta.mt V g).det + (1 - e)) (e * cA D (Formalism.L2.Theta.mt V g).det + (1 - e)) (by
    linear_combination (e * e) * det_conj_mul V g +
      (2 - (Formalism.L2.Theta.mt V g).det - cA D (Formalism.L2.Theta.mt V g).det) * he), Units.val_mkOfMulEqOne _⟩

set_option maxHeartbeats 800000 in

theorem class_lattice_scalar : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (h : O.Cl' t → GA D (Vc D i)) (J' : Subgroup (Bridge.Gf (Vc D i))), RepsR R i (tup t) h (O.bad t) J' (O.Lh t) (O.gam t) (O.vol t) → ∀ k, (O.La t k).La ∈ Vset D.host.E (Vc D i).rank 1 ∧ GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmtC (Vc D i) (h k)) (stdL D.host.E (Vc D i).rank) (O.La t k).La ∧ ∃ (e : AE D) (P : Finset (Pl D.host.E)) (x : (AE D)ˣ), IsIdemSum e P ∧ SuppAt e (Vc D i) (h k) ∧ IsDetAt e (Vc D i) (h k) x ∧ inC O.c' (O.ep t k * (((O.La t k).mIdx (O.Nc t k) D.R.r : O.c'.F))⁻¹ * ((O.La t k).zCard (O.Nc t k) D.R.r : O.c'.F)) = ((((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 x)⁻¹ : Circle) : ℂ) * ((Real.sqrt ((((((O.La t k).La ⊓ stdL D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.La t k).La.toAddSubgroup).index ^ D.R.r : ℕ) : ℝ)) : ℝ) : ℂ) := by
  rintro D G _ _ Pl0 T0 A T _ R F κ v₀ hC ⟨tie⟩ i Tp tup O hO t h J' hR k
  obtain ⟨-, hbad, -, -, -, -, hk⟩ := hR
  obtain ⟨⟨-, e, P, he, hP, hs⟩, hLh, -⟩ := hk k
  obtain ⟨r1, -, -, r4, -, -⟩ := (hO.reps t).1 k
  obtain ⟨x, hx⟩ := exists_isDetAt (GlobalTheory.PlaceDatum.idemSum_mul_self he) (Vc D i) (h k)
  refine ⟨?_, ?_, e, P, x, he, hs, hx, ?_⟩
  · have hU := (GenLatCmp.unimod_iff (O.La t k).La).1 r1
    have h4 : ∀ u ∈ stdL D.host.E (Vc D i).rank, (O.Nc t k : D.host.E) • u ∈ (O.La t k).La := fun u hu =>
      ((GenLatCmp.span_smul_le _ _ _).1 r4.2.2 u (GenLatCmp.std_eq (E := D.host.E) ▸ hu)).1
    have h5 := GenLatCmp.smul_mem_std hU h4
    exact ⟨GenLatCmp.fg_of_smul_le r4.1.pos h5, hU, _, r4.1.pos, Nat.coprime_one_right _, h5, h4⟩
  · refine isMov_conj (isMov_hLat _ (hO.lift.std.2.trans GenLatCmp.std_eq) (h k)) fun v => ?_
    rw [← hLh]
    exact (hO.reps t).2 k v
  · rw [GlobalTheory.T.oscillator_model_values_third D G Pl0 T0 A T R F κ v₀ hC ⟨tie.laws, tie.alg_eq, tie.kap, tie.hv₀, tie.chiR, tie.x0⟩ i Tp tup O hO
      t k (h k) e P x he hP hs hx hLh hbad, Circle.coe_inv, Nat.cast_pow, GenLatCmp.std_eq]

end GlobalTheory.OneMapRef.ClassScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PetIntOfCuspRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem petInt_of_cuspRapidDecay (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) : PetInt D :=
  fun _ hθ _ μ 𝓕 hq _ _ hψ hφ =>
    GlobalTheory.CuspDecay.integrableOn_star_mul hP GlobalTheory.Mem.VolFin.finVol hθ μ 𝓕 hq.1 hq.2 hψ hφ.1 hφ.2

end GlobalTheory.Mem.Th
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsCarryCommonFlagSpectrumMapFieldExt
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

section Helpers

variable {F : Type} [Field F]

theorem spMap_comp_apply_field {Z : Scheme.{0}} {k K : Type} [Field k] [Field K] (σ : k →+* K) (p : Sp k ⟶ Z)
    (w : Sp K) (w' : Sp k) : (spMap σ ≫ p) w = p w' := by
  rw [Scheme.Hom.comp_apply]
  exact congrArg p (Subsingleton.elim (α := PrimeSpectrum k) _ _)

theorem val_spMap_comp_field {Ω : Type} [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {k K : Type} [Field k]
    [Field K] (σ : k →+* K) (p : Sp k ⟶ M.Z) (y : Ω) : M.val (spMap σ ≫ p) y = σ (M.val p y) := by
  by_cases hy : y ∈ M.O (p (IsLocalRing.closedPoint k))
  · have := RatModel.val_spMap_comp σ p specializes_rfl ⟨y, hy⟩
    rw [RatModel.valLoc_eq_val] at this
    exact this
  · rw [RatModel.val_of_notMem (y := p) (IsLocalRing.closedPoint k) hy, map_zero,
      RatModel.val_of_notMem (y := spMap σ ≫ p) (IsLocalRing.closedPoint K)
        (fun h' => hy (by convert h' using 2; exact (spMap_comp_apply_field σ p _ _).symm))]

theorem bears_spMap {ι : Type} {m : ι → ℕ} {X Y : Var F} (S : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn)
    (A : Mat m X.Fn) {k K : Type} [Field k] [Field K] (σ : k →+* K) (h : Mat m k) (p : Sp k ⟶ Y.X)
    (hb : Bears S φ A h p) : Bears S φ A (h.map σ) (spMap σ ≫ p) := by
  obtain ⟨A', hA', hP⟩ := hb
  refine ⟨A', ?_, ?_⟩
  · convert hA' using 2
    exact spMap_comp_apply_field σ p _ _
  have e : (A' * (A.map φ)⁻¹).map ((ratOf Y).val (spMap σ ≫ p)) =
      ((A' * (A.map φ)⁻¹).map ((ratOf Y).val p)).map σ := by
    funext τ
    ext i j
    exact val_spMap_comp_field (ratOf Y) σ p _
  rw [e, ← Mat.map_inv, ← Mat.map_mul]
  exact hP.map σ fun _ _ => trivial

end Helpers

theorem coBear_spMap : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (x : Sp k ⟶ X.X) (p₁ : Sp k ⟶ Y₁.X) (p₂ : Sp k ⟶ Y₂.X), CoBear Eb S₁ φ₁ S₂ φ₂ x p₁ p₂ → CoBear Eb S₁ φ₁ S₂ φ₂ (spMap σ ≫ x) (spMap σ ≫ p₁) (spMap σ ≫ p₂) := by
  intro F _ ι _ m X Y₁ Y₂ Eb S₁ φ₁ f₁ S₂ φ₂ f₂ _ _ k K _ _ σ x p₁ p₂ hc
  obtain ⟨A, hA, h, hh, h1, h2⟩ := hc
  refine ⟨A, ?_, h.map σ, hh.map σ fun _ _ => trivial, bears_spMap S₁ φ₁ A σ h p₁ h1,
    bears_spMap S₂ φ₂ A σ h p₂ h2⟩
  convert hA using 2
  exact congrArg Eb.S (spMap_comp_apply_field σ x _ _)

end GlobalTheory.FlagBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjectiveBundlePointsOfRationalModelStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_bundle_points_of_rational_model : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J] (EE : M.Lat J) (s : J → Ω'), ProjBundle M EE M' φ f s → ProjPoints M EE M' φ f s := by
  first | exact @GlobalTheory.FlagBundle.projPoints_of_projBundle | exact GlobalTheory.FlagBundle.projPoints_of_projBundle | (intros; apply GlobalTheory.FlagBundle.projPoints_of_projBundle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFacePrim
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.Mem.R3
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 4000000 in

theorem reFace_prim (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (e : type_of% R.err0) (h : PrimRows3 R F) :
    PrimRows3 (R.withErr e) (reFace F Dc Sp Zsc) := by
  obtain ⟨⟨hE, hR⟩, ⟨hW, hL⟩⟩ := h.hecke
  exact
  { heckeR := h.heckeR
    heckeL := h.heckeL
    hecke := ⟨⟨hE, ⟨hR.intw, hR.comm, hR.parts⟩⟩, ⟨hW, ⟨hL.intw, hL.comm, hL.parts⟩⟩⟩
    gUnit := h.gUnit
    gEquiv := h.gEquiv
    block := h.block
    rowTest := h.rowTest
    liftTest := h.liftTest
    liftTestB := h.liftTestB
    liftOnto := fun hW' hh => h.liftOnto hW' ⟨hh.intw, hh.comm, hh.parts⟩
    pos := h.pos
    posScal := h.posScal
    levE := h.levE
    h2P := h.h2P
    thmB := h.thmB
    sumE := h.sumE
    unif := h.unif
    mLat := h.mLat
    levW := h.levW
    thmA := h.thmA
    sumW := h.sumW
    scalConj := h.scalConj
    dimParts := h.dimParts }

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGLStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w → ∃ e : locU n w ≃ₜ* GL (Fin n) (w.adicCompletion E), ∀ x : locU n w, e x = cLoc w (x : UA E n) := by
  first | exact @GlobalTheory.locU_equiv_GL | exact GlobalTheory.locU_equiv_GL | (intros; apply GlobalTheory.locU_equiv_GL <;> assumption)
end

