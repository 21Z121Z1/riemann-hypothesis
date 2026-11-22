import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorOrthogonalTranslateFinitePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)

namespace GlobalTheory.FrameOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ring

variable {l : ℕ} [Fact l.Prime] (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))

abbrev intR : Type := integralClosure ℤ_[l] Lf

def intEmb : intR Lf →+* PadicAlgCl l := Lf.val.toRingHom.comp (algebraMap (integralClosure ℤ_[l] Lf) Lf)

end Ring

section Adeles

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {l : ℕ} [Fact l.Prime]

def EvOk (i : E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l) : Prop :=
  (∀ x, ev (1 ⊗ₜ[F] x) = i x) ∧
    (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → ‖ev (a ⊗ₜ[F] 1)‖ ≤ 1) ∧
    (∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → a v = 0) → ev (a ⊗ₜ[F] 1) = 0) ∧
    ∀ y, ev y ∈ IntermediateField.adjoin ℚ_[l] (Set.range i)

end Adeles

def incOf (D : D7) {l : ℕ} [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (τ : D.what₂.Tau) :
    D.host.E →+* PadicAlgCl l :=
  cond b (cj (e0.comp (labLL D τ))) (e0.comp (labLL D τ))

def HalfAt (D : D7) (l : ℕ) : Prop := ∀ [Fact l.Prime] (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool), IsHalf (incOf D e0 b)

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

def Ix (j : Fin D.R.m) (t : p.P.T) (l N : ℕ) : Type :=
  {i : (blk p j t).Pl × ℕ // 1 ≤ i.2 ∧ i.2 ≤ N ∧ ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t i.1).asIdeal}

def frameOf (j : Fin D.R.m) (t : p.P.T) (l : ℕ) [Fact l.Prime] (N : ℕ) (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))
    [FiniteDimensional ℚ_[l] Lf] (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j t →* (intR Lf)ˣ) :
    Frame l D.what₂.Tau N where
  O := intR Lf
  emb := intEmb Lf
  G := Bridge.Gf (Vc D j)
  Γ := (Bridge.ratF (Vc D j)).range
  K := levJ p j t
  kap := kap
  chi := chi
  I := Ix p j t l N
  tr i := hkA p j t i.1
  cst _ := 1

def kapMat (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) (κ : levJ p j t) (τ : D.what₂.Tau) :
    Matrix (Fin N) (Fin N) (PadicAlgCl l) :=
  ((bs τ)⁻¹).val * ((matOf j (κ : Bridge.Gf (Vc D j))).map (ev τ)).submatrix rk rk * (bs τ).val

def KapEq (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) {Lf : IntermediateField ℚ_[l] (PadicAlgCl l)}
    (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) : Prop :=
  ∀ κ τ, (Matrix.GeneralLinearGroup.map (intEmb Lf) (kap κ τ)).val = kapMat p j t ev bs rk κ τ

def ChiEq (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (io : PadicAlgCl l ≃+* ℂ) (sh : D.what₂.Tau → ℤ)
    {Lf : IntermediateField ℚ_[l] (PadicAlgCl l)} (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf)))
    (chi : levJ p j t →* (intR Lf)ˣ) : Prop :=
  ∀ κ, io (intEmb Lf (chi κ) * ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) * ((levChi p j t κ : ℂˣ) : ℂ) = 1

def KapAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (rk : Fin P.Nr ≃o Fin (Vc D j).rank), (∀ x : 𝓞 D.what₂.LL, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1) →
    (∀ τ, EvOk (incOf D e0 b τ) (ev τ)) →
    ∃ bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, bs τ = 1) ∧ ∀ κ τ a c,
      kapMat p j (p.R.mu w) ev bs rk κ τ a c ∈ IntermediateField.adjoin ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (Set.range e0) ∧
        ‖kapMat p j (p.R.mu w) ev bs rk κ τ a c‖ ≤ 1

def ChiAt (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∃ M : ℕ, 0 < M ∧ ∀ κ : levJ p j (p.R.mu w), ((levChi p j (p.R.mu w) κ : ℂˣ) : ℂ) ^ M = 1

def ClassesAt (j : Fin D.R.m) (t : p.P.T) : Prop :=
  ∃ S : Finset (Bridge.Gf (Vc D j)), ∀ g, ∃ γ ∈ (Bridge.ratF (Vc D j)).range, ∃ s ∈ S, ∃ κ ∈ levJ p j t, g = γ * s * κ

def TameAt (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ g : Bridge.Gf (Vc D j),
    Finite {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)} ∧
      ¬ Formalism.EigenvalueLevelCeiling.plc w ∣ Nat.card {γ : (Bridge.ratF (Vc D j)).range // g⁻¹ * (γ : Bridge.Gf (Vc D j)) * g ∈ levJ p j (p.R.mu w)}

def ChoiceOk (j : Fin D.R.m) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] {N : ℕ}
    (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    {Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))}
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ) : Prop :=
  (∀ x : 𝓞 D.what₂.LL, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1) ∧ (∀ x, e0 x ∈ Lf) ∧ (∀ x, io (e0 x) = D.what₂.embLL x) ∧
    (∀ τ, EvOk (incOf D e0 b τ) (ev τ)) ∧ KapEq p j (p.R.mu w) ev bs rk kap ∧ ChiEq p j (p.R.mu w) io sh kap chi

open Classical in

def PermAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi →
    let F := frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi
    ∀ i (κ : F.K), ∃ σ : Equiv.Perm (F.tr i), ∀ s : F.tr i, ∃ κ' : F.K,
      (κ : F.G) * s = σ s * κ' ∧ F.kap κ' = F.kap κ ∧ F.chi κ' = F.chi κ

open Classical in

def CommAt (j : Fin D.R.m) (P : Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (b : Bool) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi →
    let F := frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi
    ∀ i i', ∃ σ : F.tr i × F.tr i' ≃ F.tr i' × F.tr i, ∀ x, F.Triv ((((σ x).1 : F.G) * (σ x).2)⁻¹ * ((x.1 : F.G) * x.2))

def ReadsAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime], ∃ (b : Bool) (sh : D.what₂.Tau → ℤ),
    ∀ (e0 : D.what₂.LL →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (io : PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w) ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)))
    (bs : D.what₂.Tau → GL (Fin P.Nr) (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (rk : Fin P.Nr ≃o Fin (Vc D j).rank)
    (Lf : IntermediateField ℚ_[Formalism.EigenvalueLevelCeiling.plc w] (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) [FiniteDimensional ℚ_[Formalism.EigenvalueLevelCeiling.plc w] Lf]
    (kap : levJ p j (p.R.mu w) →* (D.what₂.Tau → GL (Fin P.Nr) (intR Lf))) (chi : levJ p j (p.R.mu w) →* (intR Lf)ˣ),
    ChoiceOk p j w e0 b io ev bs rk sh kap chi → (∀ τ, bs τ = 1) →
    ∃ R : Reads (frameOf p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) P.Nr Lf kap chi) W.lam (blk p j (p.R.mu w)) w,
      R.e0 = e0 ∧ R.ix = Subtype.val

end Point

end GlobalTheory.FrameOf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedPairLatticeDilationMemOfInteger
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.BaseCmp

theorem dil_mem_latP (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (ϖ : 𝓞 D.host.E) : ∀ y ∈ lattice₂ R i, dil i (ϖ : D.host.E) y ∈ lattice₂ R i := by
  intro y hy
  have hint : finPart D (incA D (ϖ : D.host.E)) ∈ intAE D := by
    have e : finPart D (incA D (ϖ : D.host.E)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (ϖ : D.host.E) := rfl
    rw [e]
    exact AddSubgroup.subset_closure ⟨1, fun v => by simpa using (one_mem (v.adicCompletionIntegers D.host.F)), ϖ, rfl⟩
  have h := GlobalTheory.LatticeStable.smul_mem_latO D (Vc D i) (Wc D i) _ _ _ (incA D (ϖ : D.host.E)) hint y hy
  exact h

end GlobalTheory.BaseCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstUpToCenter
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.OneMapAll

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.OnCmp.const_upTo_center : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ cc, GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → ∀ u : ℂ, GlobalTheory.AdTh.SerOf (O i) (κ i) (v₀ i (sg0 D A)) (u • cc) 1 → ∃ z ∈ Subgroup.center G, ∃ (ζ : D.what₂.LL) (n : ℕ), 0 < n ∧ ζ ^ n = 1 ∧ ∀ f ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ g, (O i).phi (u • cc) f g = D.what₂.embLL ζ * (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) (actLev T.J.toCore.Q.c (O i).lev2 z f) g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hpins hU hIo h0 hPh hSpan cc hcc u hser
  have hP := hpins.2
  obtain ⟨hE, ⟨hLL, -, -, hcU, -, z, hz, hrowT⟩, -⟩ := hPh h0
  obtain ⟨ζ, hζL, ⟨m, hm, hζm⟩, hT1⟩ := hrowT ()
  obtain ⟨ζ', rfl⟩ := (AlgHom.mem_fieldRange).1 hζL
  have hζ : D.what₂.embLL.toRatAlgHom ζ' = D.what₂.embLL ζ' := rfl
  rw [hζ] at hζm hT1
  clear hζL
  have hs0 : ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (lieFac_pos _ _ _).ne'
  have gen : ∀ x, (O i).Plc () x → ∀ Fr ∈ sec (T.J.Q.Xo ((i : ℕ) + 1)) (O i).c' (wtA (κ i)) (Vc D i).rank,
      IsSum (O i) () x Fr → ∀ q,
      ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) * geo (O i) (u • cc) 1 Fr q =
        (D.what₂.embLL ζ' * ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ)) *
          geo (O i) (T.J.cE ((i : ℕ) + 1) (O i).s0) z Fr q := by
    intro x hx Fr hF hsum q
    have h1 := (hT1 x hx).2 Fr hF hsum q
    obtain ⟨h, J', hR, -, hA, hPl⟩ := (hP.tuple ()).reps
    obtain ⟨y, hy⟩ := (hPl x).1 hx
    have h2 := hser.2.2 () h J' hR _ x hy Fr hF hsum q.out
    have h3 : actLev (O i).c' (O i).lev2 1 Fr = Fr := actL_one _ _ _ hP.act.2.total hP.act.2.func hP.act.2.one hF.1
    rw [hA _ x hy] at h1
    unfold geo
    rw [h3]
    simp only [jFn, onQ, adel, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul, one_mul] at h1 h2 ⊢
    linear_combination h1 - h2
  have span : ∀ q, ∀ Fr ∈ cuspOver (O i) (κ i),
      ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ) * geo (O i) (u • cc) 1 Fr q =
        (D.what₂.embLL ζ' * ((lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) : ℂ)) *
          geo (O i) (T.J.cE ((i : ℕ) + 1) (O i).s0) z Fr q := by
    intro q Fr hF
    have hF' := hSpan hF
    clear hF
    induction hF' using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨hgc, x, hx, hgx⟩ := hg
      exact gen x hx g ((mem_cusp _ _ _ _ _ _).1 hgc).1 hgx q
    | zero =>
      have e := geo_smul (O i) (u • cc) 1 0 0 q
      have e' := geo_smul (O i) (T.J.cE ((i : ℕ) + 1) (O i).s0) z 0 0 q
      rw [zero_smul] at e e'
      rw [e, e']
      simp
    | add f g _ _ hf hg => rw [geo_add, geo_add, mul_add, mul_add, hf, hg]
    | smul a f _ hf => rw [geo_smul, geo_smul, mul_left_comm, hf, mul_left_comm]
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have rep : ∀ f ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ q : AutQ (Wc D i),
      (O i).phi (u • cc) f q.out =
        D.what₂.embLL ζ' * (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) (actLev T.J.toCore.Q.c (O i).lev2 z f) q.out := by
    intro f hf q
    rw [hn] at hf
    have hfs : f ∈ sec _ _ (wtA (κ i)) (Vc D i).rank := ((mem_cusp _ _ _ _ _ _).1 hf).1
    have hF := ((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ (O i).hle _ (T.J.U ((i : ℕ) + 1)) _ _ _ hfs).2).2 hf
    have hBC := GlobalTheory.FieldBCModel.isBC_rulBC (O i).hle hfs.1
    have hs1 : ∀ k, ![f] k ∈ sec _ T.J.Q.c (wtA (κ i)) (Vc D i).rank := fun k => by
      rw [Subsingleton.elim k 0]; exact hfs
    have e := span q _ hF
    rw [geo_of_isBC (O i) hP.act.1 _ 1 (GlobalTheory.FieldBCModel.rulBC_mem_sec _ hfs) hs1 hBC q,
      geo_of_isBC (O i) hP.act.1 _ z (GlobalTheory.FieldBCModel.rulBC_mem_sec _ hfs) hs1 hBC q] at e
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero, map_one, OneMemClass.coe_one, one_mul] at e
    have h1 : actLev T.J.toCore.Q.c (O i).lev2 1 f = f :=
      actL_one _ _ _ hP.act.1.total hP.act.1.func hP.act.1.one hfs.1
    rw [h1] at e
    exact mul_left_cancel₀ hs0 (e.trans (by ring))
  have hcomp : ∀ γ ∈ GQ (Wc D i), ∀ g, ((O i).dict (γ * g)).1 = ((O i).dict g).1 := by
    obtain ⟨th, hr, -, hd⟩ := hT.j.dictU ((i : ℕ) + 1) (inR i) _ T.J.good_σ₀
    have key : ∀ (W : HSp D) (hV : T.J.V ((i : ℕ) + 1) T.J.σ₀ = W), ∀ γ ∈ GQ W, ∀ g,
        (castDict hV (T.J.dict ((i : ℕ) + 1) T.J.σ₀) (γ * g)).1 = (castDict hV (T.J.dict ((i : ℕ) + 1) T.J.σ₀) g).1 := by
      rintro W rfl γ hγ g
      obtain ⟨γ', -, he⟩ := hd.1 γ hγ g
      have e := congrArg Sigma.fst he
      exact e
    exact key _ (O i).hV
  have hsplit : ∀ (c' : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (f : T.J.R ((i : ℕ) + 1)) g,
      (O i).phi c' f g = c' ((O i).dict g).1 * (O i).phi (fun _ => 1) f g := by
    intro c' f g
    show c' _ * _ * _ = c' _ * (1 * _ * _)
    ring
  have hV : T.J.V ((i : ℕ) + 1) T.J.σ₀ = Wc D i := (O i).hV
  have hinv : ∀ f ∈ T.J.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∀ γ ∈ GQ (Wc D i), ∀ g,
      (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) f (γ * g) = (O i).phi (T.J.cE ((i : ℕ) + 1) (O i).s0) f g :=
    fun f hf => GlobalTheory.OneMapTuples.psi_inv T.J _ hV hT.j (inR i) (dom_wtA (κ i)) hf
  refine ⟨z, hz, ζ', m, hm, ?_, ?_⟩
  · apply D.what₂.embLL.injective
    rw [map_pow, map_one]
    exact hζm
  intro f hf g
  obtain ⟨k, hk, -⟩ := hP.lift.lev z
  have hzf := (hE z k hk f hf).1
  have hq : g * (⟦g⟧ : AutQ (Wc D i)).out⁻¹ ∈ GQ (Wc D i) :=
    QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel (GQ (Wc D i))) g)
  set γ := g * (⟦g⟧ : AutQ (Wc D i)).out⁻¹ with hγ
  have hg : g = γ * (⟦g⟧ : AutQ (Wc D i)).out := by rw [hγ, inv_mul_cancel_right]
  have hL : (O i).phi (u • cc) f g = (O i).phi (u • cc) f (⟦g⟧ : AutQ (Wc D i)).out := by
    have e := hinv f hf γ hq (⟦g⟧ : AutQ (Wc D i)).out
    rw [← hg] at e
    rw [hsplit (T.J.cE _ _) f g, hsplit (T.J.cE _ _) f, hg, hcomp γ hq] at e
    rw [← hg] at e
    have hne : T.J.cE ((i : ℕ) + 1) (O i).s0 ((O i).dict (⟦g⟧ : AutQ (Wc D i)).out).1 ≠ 0 :=
      norm_ne_zero_iff.1 ((hcU _).trans_ne one_ne_zero)
    have hc : ((O i).dict g).1 = ((O i).dict (⟦g⟧ : AutQ (Wc D i)).out).1 := by
      have := hcomp γ hq (⟦g⟧ : AutQ (Wc D i)).out
      rwa [← hg] at this
    rw [hsplit (u • cc) f g, hsplit (u • cc) f, hc, mul_left_cancel₀ hne e]
  rw [hL, rep f hf, ← hinv _ hzf γ hq, ← hg]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVectorOrthogonalTranslateFinitePointStatement
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetVector_orthogonal_translate_finite_point : ∀ {D : D7} {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (X : Data P) (r : D.host.E), IsExact P X r →
  ∀ (𝔪 : Ideal (𝓞 D.host.E)) (Sf : Finset (FinPl D)) (o : ℕ), GoodMod D 𝔪 Sf →
  ∀ LB : Lat X.B, IsSelfDualC X.B LB →
    (∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, z ∈ Formalism.MainNotions.TaylorLogMetric.YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D P.a) (Formalism.MainNotions.StandardLatticesGL3.stdL D P.d) ↔
      finPt X.rkA X.rkB r z ∈ latO X.A X.B (stdLat X.A) LB fun _ => True) →
  ∀ f₀ φ, Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r P.e0 f₀ → IsSphOff X.ψ X.A X.B (stdLat X.A) LB ∅ f₀ →
    Reads X.ψ X.θ X.rkA X.rkB ⊤ δ r (cosetVec P 𝔪 o) φ →
  o + P.a ≤ P.d → ∀ (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), IsCovolOne (ratL X.B X.A) ν 𝓕 →
  ∀ y, X.ιA y ∈ openOff X.A (stdLat X.A) Sf → ¬ (y ∈ intG D P.a ∧ CongOne D 𝔪 y) →
    ip X.A X.B ν 𝓕 (X.om (X.ιA y, 1) φ) φ = 0 := by
  first | exact @GlobalTheory.NormRatio.ip_om_cosetVec_eq_zero | exact GlobalTheory.NormRatio.ip_om_cosetVec_eq_zero | (intros; apply GlobalTheory.NormRatio.ip_om_cosetVec_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsComponentFiniteDimensionalAndSpanned
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem cuspOn_fd_and_span_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → (∀ τ i, i < Dw.mult τ → 1 ≤ a (τ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → FiniteDimensional c.F (cuspOn U Z (wtZ a n)) ∧ ∀ P ∈ holSub (U σ).X (modelWt (U σ) (wtZ a n)), (∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z → P k y = 0) → P ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z (wtZ a n) : Set (Rul Xo c))) := by
  intro E _ _ _ H Dw l Xo c r U x h Z σ hσ a n hD hpos hn
  refine ⟨?_, fun P hP hoffZ => ?_⟩
  · haveI := GlobalTheory.cuspForms_finiteDimensional_of_goodEmb E H Dw l Xo c r U σ hσ (h.unf σ hσ) a n hD
    have hle : cuspOn U Z (wtZ a n) ≤ cusp Xo c U a n := by
      rw [← cuspW_wtZ]; exact cuspOn_le U Z (wtZ a n)
    exact Submodule.finiteDimensional_of_le hle
  · have hpts : HasPts U Z := GlobalTheory.FlatLine.hasPts U h.pos h.good h.unf Z
    have e : goodOf c σ = σ := if_pos hσ
    have htest := (hpts.1 σ).2
    rw [e] at htest
    have hoff : P ∈ offZero (U σ).X := fun k y hy => hoffZ k y fun hz => hy hz.1
    have hP0 : P ∈ holSub0 (U σ).X (laU (U σ) a n) := ⟨by rwa [← modelWt_wtZ], hoff⟩
    have hsp := h.onto σ hσ a n hD hpos hn hP0
    have hfix : rdU (U σ) (idem Z) * P = P := by
      funext k y
      show rdU (U σ) (idem Z) k y * P k y = P k y
      by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
      · obtain ⟨hd, hl⟩ := hz
        have h1 : rdU (U σ) (idem Z) k y = 1 := by
          simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hd, dif_pos]
          rw [evR_idem hl (htest _ ⟨hd, hl⟩ hd)]
          rfl
        rw [h1, one_mul]
      · rw [hoffZ k y hz, mul_zero]
    let g : FDSec (U σ).X →ₗ[ℂ] FDSec (U σ).X := LinearMap.mulLeft ℂ (rdU (U σ) (idem Z))
    have hmap := Submodule.mem_map_of_mem (f := g) hsp
    rw [Submodule.map_span] at hmap
    have hg : g P = P := hfix
    rw [hg] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨idem Z * f, ⟨?_, ?_⟩, ?_⟩
    · rw [← cuspW_wtZ] at hf
      exact GlobalTheory.CompRestr.idem_mul_mem_cuspW h.unf Z hf
    · rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
    · show rdU (U σ) (idem Z * f) = rdU (U σ) (idem Z) * rdU (U σ) f
      exact AllWt.rdU_mul (U σ) _ _

end GlobalTheory.FlatCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDegreeNonposOfAdelicDegreeNonpos
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem closedPoint_mem_nonzeroLocus {K : Type} [Field K] {C : Scheme.{0}} [IsIntegral C] (x : Sp K ⟶ C)
    [IsDominant x] {L : LB C} {σ : L.Sec} (hσ : σ ≠ 0) : x (IsLocalRing.closedPoint K) ∈ Out.nonzeroLocus σ := by
  have h : ∃ i, σ.f i ≠ 0 := by
    by_contra h
    push Not at h
    apply hσ
    obtain ⟨f, hf⟩ := σ
    obtain rfl : f = fun _ => 0 := funext h
    rfl
  obtain ⟨i, hi⟩ := h
  have hne : ((C.basicOpen (σ.f i) : C.Opens) : Set C).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro e
    exact hi ((basicOpen_eq_bot_iff _).1 (Opens.ext e))
  obtain ⟨y, hy⟩ := x.denseRange.exists_mem_open (C.basicOpen (σ.f i)).isOpen hne
  obtain rfl : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  exact Opens.mem_iSup.2 ⟨i, hy⟩

theorem deg_pos_of_integral {k K : Type} [Field k] [IsAlgClosed k] [Field K] [Algebra k K] {r : ℕ}
    {g : Place k K → Matrix (Fin r) (Fin r) K} (hg : admitted g) {f : K} (hf : f ≠ 0)
    (hfin : {v : Place k K | v.1 f ≠ 1}.Finite) (hsum : ∑ᶠ v : Place k K, ord v f = 0) {m : ℕ}
    (hle : ∀ v : Place k K, v.1 (f * (g v).det ^ m) ≤ 1) {w : Place k K} (hlt : w.1 (f * (g w).det ^ m) < 1) :
    0 < deg g := by
  have hne : ∀ v, f * (g v).det ^ m ≠ 0 := fun v => mul_ne_zero hf (pow_ne_zero _ (hg.1 v))
  have hadd : ∀ v : Place k K, ord v (f * (g v).det ^ m) = ord v f + m * ord v (g v).det := fun v => by
    rw [(ord_calculus k K v).1 _ _ hf (pow_ne_zero _ (hg.1 v)), ← (ord_calculus k K v).2.1 _ (hg.1 v), zpow_natCast]
  have f₁ : (Function.support fun v : Place k K => ord v f).Finite :=
    hfin.subset fun v hv e => hv (((ord_calculus k K v).2.2.2.1 _ hf).1 e)
  have f₂ : (Function.support fun v : Place k K => ord v (g v).det).Finite :=
    hg.2.subset fun v hv e => hv (((ord_calculus k K v).2.2.2.1 _ (hg.1 v)).1 e.2)
  have f₃ : (Function.support fun v : Place k K => (m : ℤ) * ord v (g v).det).Finite :=
    f₂.subset fun v hv e => hv (by simp only [e, mul_zero])
  have hs : ∑ᶠ v : Place k K, ord v (f * (g v).det ^ m) = m * deg g := by
    simp only [hadd]
    rw [finsum_add_distrib f₁ f₃, hsum, zero_add, deg, mul_finsum' _ _ f₂]
  have h0 : ∀ v : Place k K, 0 ≤ ord v (f * (g v).det ^ m) := fun v =>
    ((ord_calculus k K v).2.2.1 _ (hne v)).1 (hle v)
  have hw : 0 < ord w (f * (g w).det ^ m) :=
    (h0 w).lt_of_ne fun e => hlt.ne (((ord_calculus k K w).2.2.2.1 _ (hne w)).2 e.symm)
  have f₄ : (Function.support fun v : Place k K => ord v (f * (g v).det ^ m)).Finite := by
    refine (f₁.union f₃).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
    exact hv (by simp only [hadd, h.1, h.2, add_zero])
  have hpos : 0 < (m : ℤ) * deg g := by
    rw [← hs]
    exact hw.trans_le (single_le_finsum w f₄ h0)
  by_contra h
  exact absurd hpos (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg m) (not_lt.1 h)))

theorem interNum_det_nonpos_of_deg_nonpos : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty → IsFrame s → admitted g → (∀ v, LocFrame x s v (g v)) → deg g ≤ 0 → interNum k (GlobalTheory.structureModule C) ![det W r] ≤ 0 := by
  intro k K _ _ _ _ _ C _ x hx W r hW V₀ s g hV hs hg hloc hdeg
  by_contra hpos
  have := LieSemineg.isIntegral_curve hx.1.1 hx.1.2.2
  have := hx.2.1.1
  obtain ⟨m, σ, c, -, hσ, hc⟩ := GlobalTheory.T.exists_lineBundle_pow_section_vanishing_degree_pos k C hx.1 (det W r) hW.isLB_det (not_le.1 hpos)
  obtain ⟨w, b, hb, hbc⟩ := GlobalTheory.T.curve_closedPoint_isCentreOfPlace k K C x hx c fun e => hc (e ▸ closedPoint_mem_nonzeroLocus x hσ)
  obtain ⟨f, hf, H⟩ := GlobalTheory.T.detPowSection_rational_genericPoint k K C x hx W r hW V₀ s hV hs m σ hσ
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx) f hf
  exact (deg_pos_of_integral hg hf hfin hsum (fun v => (H v _ (hloc v)).1)
    ((H w _ (hloc w)).2 b hb (hbc ▸ hc))).not_ge hdeg

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedFrameCMUnitaryProofStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsBalancedFrameCMUnitary_proof : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.BalancedPointStatement E := by
  first | exact @GlobalTheory.BalancedPointPf.balancedPoint | exact GlobalTheory.BalancedPointPf.balancedPoint | (intros; apply GlobalTheory.BalancedPointPf.balancedPoint <;> assumption)
end

