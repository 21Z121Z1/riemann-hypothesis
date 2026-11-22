import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CohomologicalCsdTemperedUnrOfFull
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
import Formalism.LocalToGlobal.KernelLattices.KerStd

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedGLOfHasSatGL
section
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CuspRep ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem mem_integer_iff (x : w.adicCompletion E) : x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Formalism.UG.Ov (F := E) w := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff, ← map_one (valuation _), ← Valuation.vle_iff_le, Valuation.vle_iff_le Valued.v, map_one]
  rfl

theorem range_eq {K : Type} [Field K] {A B : Subring K} (h : A = B) (n : ℕ) :
    (Formalism.UG.bc (n := Fin n) B.subtype).range = (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap A K)).range := by
  subst h; rfl

theorem kgl_eq_ko (n : ℕ) : GlobalTheory.LFun.KGL w n = GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) :=
  range_eq (SetLike.ext fun x => mem_integer_iff w x) n

theorem isSpherical_of_hasSatGL (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w ρ B) :
    GlobalTheory.SmGL.IsSpherical ρ := by
  have h1 := h.1
  unfold GlobalTheory.LGrp.IsSpherical at h1
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rwa [← kgl_eq_ko]

theorem isTemperedGL_of_hasSatGL (hT : GlobalTheory.CohomologicalConjSelfDualTempered.CohomologicalCsdTemperedUnr) (L : Type) [Field L] [NumberField L]
    [IsCMField L] (n : ℕ) (hn : 2 ≤ n) (π : CuspSub L n) (hc : π.IsCsd) (hcoh : GlobalTheory.GKCoh.IsCohomological π)
    (y : HeightOneSpectrum (𝓞 L)) (σ : SmIrr (GL (Fin n) (y.adicCompletion L))) (hσ : π.IsLocComp y σ)
    {B : Multiset ℂˣ} (hB : GlobalTheory.LFun.HasSatGL y σ.ρ B) : GlobalTheory.LocGL.IsTemperedGL σ.ρ :=
  hT L n hn π hc hcoh y σ hσ (isSpherical_of_hasSatGL y n hB)

theorem isSpherical_trivial (n : ℕ) :
    GlobalTheory.SmGL.IsSpherical (1 : Representation ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) := by
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rw [Submodule.ne_bot_iff]
  refine ⟨1, ?_, one_ne_zero⟩
  intro h
  simp

end GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalCut

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

omit [IsAlgClosure E Ω] in

def Weak (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous r ∧ UpperTheory.V.Af.AttC ι r π

def IsWeight (π : CuspSub E a) (wt : ℤ) : Prop :=
  ∀ τ : E →+* ℂ, (CG.mk π).infChar (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) =
    ((CG.mk π).infChar τ).map fun z => (a : ℂ) - 1 - (wt : ℂ) - z

inductive Clause
  | ss | pure | dR | crys | iwa

def ClauseAt (c : Clause) (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  match c with
  | .ss => ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ →
      ∀ g : Weil h, (wdOf h hl ι r).charPol g = (rc (algNorm σ)).charPol g
  | .pure => ∀ (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (wt : ℤ), IsWeight π wt →
      ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered
  | .dR => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
      IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
        ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' → ∀ J : Multiset ℤ,
          J.map (fun n : ℤ => (n : ℂ)) = ((CG.mk π).infChar (ι.toRingHom.comp τ)).map (fun z => ((a : ℂ) - 1) / 2 - z) →
          IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ J
  | .crys => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
      ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)
  | .iwa => ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
        IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
          ∀ rc, IsRec h rc → wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

def Good (l : ℕ) (π : CuspSub E a) : Prop :=
  (∃ x : E, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : E)) ∧ Even (Module.finrank ℚ (maximalRealSubfield E)) ∧
    ∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat w B

inductive Level
  | all | good | csd

def InScope (s : Level) (l : ℕ) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) : Prop :=
  (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.PolarizedPair π χ ∧
    match s with
    | .all => True
    | .good => Good l π
    | .csd => Good l π ∧ χ = quadChar E ^ a

def PlaceOK (s : Level) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  match s with
  | .all => True
  | _ => GlobalTheory.UnitaryBC.IsSplitAt w

def Ex (s : Level) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∃ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r

def Holds (s : Level) (c : Clause) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
    InScope s l π χ → ∀ r : G E Ω →* GL (Fin a) (Qbar l), Weak π ι r → ∀ w, PlaceOK s w → ClauseAt c π ι r w

structure IsLift {K M : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M]
    (π : CuspSub K a) (P : CuspSub M a) : Prop where
  sat : ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ) (B : Multiset ℂˣ), normV w = normV (w.under (𝓞 K)) ^ f →
    (CG.mk π).HasSat (w.under (𝓞 K)) B → (CG.mk P).HasSat w (B.map (· ^ f))
  inf : ∀ τ : M →+* ℂ, (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap K M))
  loc : ∀ (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) (i : v.adicCompletion K ≃+* w.adicCompletion M),
    Continuous i → (∀ x : K, i (algebraMap K _ x) = algebraMap M _ (algebraMap K M x)) →
    ∀ σ σ', π.IsLocComp v σ → P.IsLocComp w σ' →
      ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)

def QuadLift : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub K a,
    (∃ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 K)) B) →
    ∃ P : CuspSub M a, IsLift π P

theorem InScope.all {s : Level} {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} (h : InScope s l π χ) : InScope .all l π χ :=
  ⟨h.1, h.2.1, trivial⟩

end GlobalTheory.GalCut

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
section
noncomputable section

namespace GlobalTheory.AtG

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open scoped ComplexConjugate

def JetSplitAmb : Prop :=
  ∀ {D : D7} {X : Fields} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → TaylorLogMetric.IsChi D χ →
    ∀ (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E a)) (N' : Submodule (𝓞 X.E) (Formalism.L2.Col.Sp X.E b))
      (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), Even a → Even b → Formalism.L2.Col.IsSdLat N → Formalism.L2.Col.IsSdLat N' →
      s.StdAtP p N → s.StdAtP p N' → ¬ (p : ℤ) ∣ NumberField.discr X.E → (∀ τ, ‖ι (cD τ)‖ ≤ 1) → 5 ≤ p →
      ¬ p ∣ D.host.d → (ambOf s B χ cD : Amb X).LaHyp a b S →
      ∀ (π : ℂ) (pE : 𝓞 X.E), Formalism.L2.AlgTh.IsQInt D.host.d π → π * conj π = (p : ℂ) → Formalism.L2.AlgTh.SplitS (ambOf s B χ cD) S p π pE →
      ∀ (c' : ℕ) (x : Formalism.L2.Col.HomE X.E a b), 0 < c' → ¬ p ∣ c' → x ∈ Formalism.L2.Col.divLat c' (Formalism.L2.Col.homAt S N N') → ∀ m : DVar X.Tau a b →₀ ℕ,
        ‖ι ((ambOf s B χ cD : Amb X).σ₀ ((ambOf s B χ cD : Amb X).jetK S N N' (p * c') x m))‖ * ‖ι (conj π)‖ ^ m.degree *
          ‖(p : ℂ_[p])‖ ^ (Fintype.card X.Tau * b * a) ≤ 1

open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound in

def TiesAt (D : D7) (EX : ErrX D) (Dx : DivX D) (μ : D.what₂.Tup) : Prop :=
  ∃ (Ch : Chars (recFields D) (recPrimes EX) D.R.m) (mu0 : _) (eta : _) (sel : _) (δ : ℂ) (B : Base D D.host.ccK δ) (χ : _) (cD : _),
    HostTie EX ∧ CharTie Ch mu0 eta sel ∧ AnTie D δ χ cD ∧ ∀ u, ChainTie Ch sel Dx mu0 (ambOf (recSeam D) B χ cD) u μ

open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.KerRat in

def RowPin {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : (I.rec7 l Z).what₂.Tup) : Prop :=
  ∀ u : B.Word, ∃ e : (I.per l u a).Mt ≃ₗ[ℂ] (I.rec7 l Z).what₂.Amb a,
    (a = (I.rec7 l Z).what₂.mu0 → HEq e ((I.rec7 l Z).eMt u)) ∧ (a ≠ (I.rec7 l Z).what₂.mu0 → e = (I.rec7 l Z).eMtTw u a) ∧
    (∀ v ∈ ((I.rec7 l Z).what₂.Mtilde a).gen, ∃ z, e (rowForm I l h u a z) = v) ∧
    ∀ z, z ∈ Formalism.L2.Col.MtildeL (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps ↔ ∃ c : (I.rec7 l Z).what₂.Amb a → 𝓞 (I.rec7 l Z).what₂.LL,
      e (rowForm I l h u a z) = ∑ v ∈ ((I.rec7 l Z).what₂.Mtilde a).gen, (I.rec7 l Z).what₂.embLL ((c v : 𝓞 (I.rec7 l Z).what₂.LL) : (I.rec7 l Z).what₂.LL) • v

end GlobalTheory.AtG

end
end

