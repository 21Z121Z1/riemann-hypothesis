import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DSymmHypsInhabited
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CarSumSqZeroOfAnti
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.CechPic

namespace GlobalTheory.Mix

variable {k K : Type} [CommRing k] [CommRing K] {X G : Scheme.{0}} {p : X ⟶ Sp k} {q : G ⟶ Sp K} {j : G ⟶ X} {ρ : k →+* K}

def bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (z : CxPts q τ) : CxPts p (τ.comp ρ) := CxPts.bcMap w τ z

theorem bcPt_val (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (z : CxPts q τ) : (bcPt w τ z).1 = z.1 ≫ j := rfl

theorem continuous_bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) : Continuous (bcPt w τ) :=
  CxPts.continuous_of_comp (bcPt_val w τ)

theorem cInfAt_bcPt (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) {f : CxPts p (τ.comp ρ) → ℝ} {z : CxPts q τ}
    (h : CInfAt f (bcPt w τ z)) : CInfAt (fun y => f (bcPt w τ y)) z := by
  have hm : ∀ y, (bcPt w τ y).1 = y.1 ≫ j := bcPt_val w τ
  unfold CInfAt at h ⊢
  obtain ⟨W, ι, hι, g, F, O, hW, hO, hmem, hF, he⟩ := h
  refine ⟨j ⁻¹ᵁ W, ι, hι, fun a => j.app W (g a), F, O, (CxPts.mem_ptsIn_preimage hm).2 hW, hO, ?_, hF, ?_⟩
  · simpa only [CxPts.ev_of_comp hm] using hmem
  · filter_upwards [(continuous_bcPt w τ).continuousAt.tendsto.eventually he] with y hy
    simpa only [CxPts.ev_of_comp hm] using hy

def MLine.bc (w : j ≫ p = q ≫ spMap ρ) (τ : K →+* ℂ) (A : MLine p (τ.comp ρ)) : MLine q τ where
  B := A.B.pull j
  φ := A.φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => bcPt w τ) fun _ _ => rfl
  cInf i z hz := (cInfAt_bcPt w τ (A.cInf _ _ (mem_of_mem_linComb (m := fun _ => bcPt w τ z)
    (fun _ => rfl) hz PUnit.unit))).congr (.of_forall fun y => by simp [Weight.linComb])

end GlobalTheory.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
section
noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev blockAlg detbP OmP dMode)
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.PsCo.PcEF

variable {n : ℕ}

def PolyOnK (ε : Fin n → Bool) (f : Mat n → ℂ) : Prop := ∃ P : Poly n, ∀ k ∈ Formalism.REAL.Kset ε, f k = ev k P

def trK {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (T : Mat n → (W →L[ℂ] W)) (k : Mat n) : ℂ :=
  LinearMap.trace ℂ W (T k : W →ₗ[ℂ] W)

def IsKIrr (ε : Fin n → Bool) (γ : Fin n → ℝ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (T : Mat n → (W →L[ℂ] W)) : Prop :=
  Nontrivial W ∧ Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T ∧ Formalism.MainNotions.S.IsKTypeOf ε T γ ⊤

abbrev dD (ε : Fin n → Bool) {M : Type} [AddCommGroup M] [Module ℂ M] (E : Fin n → Fin n → Module.End ℂ M) :
    Module.End ℂ (TensorProduct ℂ M (Fock n)) := dOp ε (eT E) cpT + dOp' ε (eT E) cmT

abbrev tor (θ : Fin n → ℝ) : Fin n → ℂ := fun a => Complex.exp (θ a * Complex.I)

def BlockForm : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P : Poly n), ∃ (M : ℕ) (Q : Poly n), Q ∈ blockAlg ε ∧
    ∀ k ∈ Formalism.REAL.Kset ε, ev k P = ev k (detbP n ^ M * Q)

def CoefPoly : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
    ∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ

def TrPoly : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)), (∀ v w : W, PolyOnK ε fun k => ⟪w, T k v⟫_ℂ) → PolyOnK ε fun k => conj (trK T k)

def AvgMap : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (T : Mat n → (W →L[ℂ] W)) (Z : Type) [NormedAddCommGroup Z] [InnerProductSpace ℂ Z] [FiniteDimensional ℂ Z]
    (S : Mat n → (Z →L[ℂ] Z)) (Γ : Z →ₗ[ℂ] Z), Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) T →
    Formalism.MainNotions.S.IsURepOn (Formalism.REAL.Kset ε) S →
    ∫ k : KG ε, conj (trK T (toMK k)) * LinearMap.trace ℂ Z (Γ ∘ₗ (S (toMK k) : Z →ₗ[ℂ] Z)) ∂(muK ε) ≠ 0 →
    ∃ Φ : W →ₗ[ℂ] Z, Φ ≠ 0 ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ v, Φ (T k v) = S k (Φ v)

def SchurOne : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (γ : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (T : Mat n → (W →L[ℂ] W)), IsKIrr ε γ T →
    ∫ k : KG ε, conj (trK T (toMK k)) * trK T (toMK k) ∂(muK ε) = 1

def SumTypes : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → ∀ S : Submodule ℂ H, FiniteDimensional ℂ S →
    Formalism.MainNotions.S.IsKStableOn ε σ S → S ≤ sSup {S' | S' ≤ S ∧ ∃ μ, Formalism.MainNotions.S.IsKTypeOf ε σ μ S'}

def PolyAvg : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ), ∃ A : Set (Fin n → ℝ), A.Finite ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat n → (H →L[ℂ] H)),
      IsURepOn (UJset ε) σ → ∀ u : H, ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ Formalism.MainNotions.S.IsKStableOn ε σ S ∧
        (∀ P : Poly n, P.totalDegree ≤ d → ∫ k : KG ε, ev (toMK k) P • σ (toMK k) u ∂(muK ε) ∈ S) ∧
        ∀ (μ : Fin n → ℝ) (s : H), s ∈ S → s ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ μ s → μ ∈ A

def DatumEquiv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), StdGap ε lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat n → (H →L[ℂ] H)),
    IsURepOn (UJset ε) σ → Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ →
    ∀ V : Submodule ℂ (smD ε σ), IsKIrrHW ε (smE ε σ) (lowK ε lam) V → V ≠ ⊥ →
    (∀ v ∈ V, casimir (smE ε σ) v = (casVal lam : ℂ) • v) →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Mat n → (X →L[ℂ] X)), Formalism.MainNotions.S.IsDS ε lam D →
    ∃ U : H ≃ₗᵢ[ℂ] X, ∀ g ∈ UJset ε, ∀ x, U (σ g x) = D g (U x)

def MatRep : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (π : UJ ε →* (U →L[ℂ] U)),
    IsUnitaryRep π → IsTopIrreducible π → ∃ σ : Mat n → (U →L[ℂ] U), IsURepOn (UJset ε) σ ∧
      Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ ∧ ∀ g : UJ ε, σ (toM g) = π g

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def toSub {G : Type} [Group G] (H : Subgroup G) (g : G) : H := if h : g ∈ H then ⟨g, h⟩ else 1

def trOn {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V) (L : V →ₗ[ℂ] V) : ℂ :=
  if h : ∀ v ∈ M, L v ∈ M then LinearMap.trace ℂ M (L.restrict h) else 0

def hint {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ) : ℂ :=
  (((rStab u ⊓ K).relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : H ⧸ (rStab u ⊓ K), u q.out

structure IsoDat (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Type 1 where
  c : ℕ
  N : Fin c → ℕ
  h : ∑ i, N i = n
  V : ∀ i, Submodule ℂ (Sm E (N i))
  σ : ∀ i (w : Pl E), SmIrr (GLw (N i) w)
  m : Fin c → (E →+* ℂ) → Multiset ℂ
  P : ∀ w : Pl E, SmIrr (GLw n w)
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, IsCsdGL (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)
  iso : ∀ w, Nonempty ((P w).ρ.Equiv (locProd h w (σ · w)))

def IsoDat.HasWt (D : IsoDat E n) (lam : InfinitePlace E → DomWeight n) : Prop :=
  ∀ v : InfinitePlace E, ∑ i, D.m i v.embedding = infOfWeight (lam v)

def IsoDat.CompAt (D : IsoDat E n) (π : Submodule ℂ (UA E n → ℂ)) (w : Pl E) : Prop :=
  IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) (D.P w).ρ

def IsMu (μ : HChar E) (e : InfinitePlace E → ℤ) : Prop :=
  μ.IsUnitary ∧ (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) ∧
    (∀ w : Pl E, ¬ IsSplitAt w → μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (-1)) ∧ (∀ v, Odd (e v)) ∧
    ∀ z : (Cinf E)ˣ, (chiInf μ z : ℂ) = ∏ v, (z.1 v / (‖z.1 v‖ : ℂ)) ^ e v

def pairRep {a b : ℕ} (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (σ₁ : SmIrr (GLw a w))
    (σ₂ : SmIrr (GLw b w)) :=
  GlobalTheory.SmGL.ind₂ (GlobalTheory.SmGL.stdSum h) (GlobalTheory.SmGL.extTensor (twRep σ₁.ρ ((μ ^ b).comp GeneralLinearGroup.det))
    (twRep σ₂.ρ ((μ ^ a).comp GeneralLinearGroup.det)))

structure PairTerm (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (μ : HChar E) : Type 1 where
  a : ℕ
  ha : a ≤ n
  t₁ : Term E a
  t₂ : Term E (n - a)
  D : IsoDat E n
  link : ∀ w, Nonempty ((D.P w).ρ.Equiv (pairRep (Nat.add_sub_cancel' ha) w (μ.loc w) (t₁.P w) (t₂.P w)))

def PairTerm.fac {μ : HChar E} (T : PairTerm E n μ) (w : Pl E) (K' : Subgroup (UL n w)) (f : UL n w → ℂ)
    (K₁ : ∀ a, Subgroup (GLw a w)) (K₂ : ∀ a, Subgroup (GLw (n - a) w))
    (φ : ∀ a, GLw a w × GLw (n - a) w → ℂ) : ℂ :=
  if IsSplitAt w then twTr ((T.D.P w).ρ.comp (UL n w).subtype) (KL n w) K' f LinearMap.id
  else twTr (extT (T.t₁.rep w) (T.t₂.rep w)) ((GlobalTheory.LFun.KGL w T.a).prod (GlobalTheory.LFun.KGL w (n - T.a)))
    ((K₁ T.a).prod (K₂ T.a)) (φ T.a) (TensorProduct.map (T.t₁.A w) (T.t₂.A w))

def MainId : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ),
    IsMu μ e → ∀ S : Set (Pl E), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
      (K₁ : ∀ (w : Pl E) a, Subgroup (GLw a w)) (K₂ : ∀ (w : Pl E) a, Subgroup (GLw (n - a) w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    (∀ a ≤ n, IsLevelFam (thL a) (fun w : Pl E => GlobalTheory.LFun.KGL w a) (K₁ · a) ∧
      IsLevelFam (thL (n - a)) (fun w : Pl E => GlobalTheory.LFun.KGL w (n - a)) (K₂ · a)) →
    ∃ (ι : Type) (_ : Fintype ι) (T : ι → PairTerm E n μ) (C : ι → ℂ), (∀ j, (T j).D.HasWt lam) ∧
      ∀ (f : ∀ w : Pl E, UL n w → ℂ) (φ : ∀ (w : Pl E) a, GLw a w × GLw (n - a) w → ℂ), IsTest (KL n) K' f →
        (∀ a ≤ n, (∀ w, ¬ IsSplitAt w → IsHecke ((K₁ w a).prod (K₂ w a)) (φ w a) ∧ Match n a (n - a) w 1 (f w) (φ w a)) ∧
          ∀ᶠ w in cofinite, ¬ IsSplitAt w →
            φ w a = (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w (n - a)) : Subgroup _) : Set _).indicator 1) →
        (∃ w ∈ S, (∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) ∧
          (¬ IsSplitAt w → ∀ a ≤ n, RegAt2 a (n - a) w (φ w a))) →
        geomU S lam f = ∑ j, C j * ∏ᶠ w ∈ S, (T j).fac w (K' w) (f w) (K₁ w) (K₂ w) (φ w)

def blk {a b : ℕ} (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    GLw n w :=
  let M := Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
    (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)
  if hM : IsUnit M then hM.unit else 1

def intMat (a b : ℕ) (w : Pl E) : Subgroup (Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E))) :=
  Subgroup.closure {X | ∀ i j, Valued.v (Multiplicative.toAdd X i j) ≤ 1}

def ct {a b : ℕ} (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (m : GLw a w × GLw b w) : ℂ :=
  absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) *
    hint (intMat a b w) fun X => avg fun k : GlobalTheory.LFun.KGL w n => f ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)

def ctMu {a b : ℕ} (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ)
    (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) *
    ct h w (fun y => f (toSub _ y)) m

def iwGL (n : ℕ) (w : Pl E) : Subgroup (GLw n w) := GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin n)

def tdiag {w : Pl E} (ϖ : (w.adicCompletion E)ˣ) (a : Fin n → ℤ) : GLw n w :=
  GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin n) fun i => ϖ ^ a i

def dcos (n : ℕ) (w : Pl E) (t : GLw n w) : GLw n w → ℂ :=
  fun y => if ∃ x ∈ iwGL n w, ∃ z ∈ iwGL n w, y = x * t * z then 1 else 0

def IsUnifAt {w : Pl E} (ϖ : (w.adicCompletion E)ˣ) : Prop := ordL (ϖ : w.adicCompletion E) = 1 ∧ cj w ϖ = ϖ

def IsWitt (n : ℕ) (w : Pl E) (b : GLw n w) : Prop :=
  b ∈ GlobalTheory.LFun.KGL w n ∧ (b.val.map (cj w))ᵀ * b.val = antiJ (w.adicCompletion E) n

def iwU (n : ℕ) (w : Pl E) (b : GLw n w) : Subgroup (UL n w) :=
  ((iwGL n w).map (MulAut.conj b).toMonoidHom).subgroupOf (UL n w)

def wexp (n : ℕ) (l : Fin (n / 2) → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < n / 2 then l ⟨i, h⟩ else if h' : n - 1 - i.val < n / 2 then -l ⟨_, h'⟩ else 0

def sexp (n : ℕ) (l : Fin (n / 2) → ℤ) (i : Fin n) : ℤ :=
  if h : i.val < n / 2 then l ⟨i, h⟩ - l ⟨i, h⟩ / 2 else if h' : n - 1 - i.val < n / 2 then -(l ⟨_, h'⟩ / 2) else 0

def Cone {m : ℕ} (l : Fin m → ℤ) : Prop := (∀ i j : Fin m, (j : ℕ) = i + 1 → 2 ≤ l i - l j) ∧ ∀ i, 2 ≤ l i

def fU (n : ℕ) (w : Pl E) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) : UL n w → ℂ :=
  fun γ => if ∃ x ∈ iwU n w b, ∃ z ∈ iwU n w b, γ.1 = x.1 * (b * tdiag ϖ (wexp n l) * b⁻¹) * z.1 then 1 else 0

def qh (w : Pl E) : ℂ := (Real.sqrt (qV E w : ℝ) : ℝ)

def dlt (n : ℕ) (w : Pl E) (l : Fin (n / 2) → ℤ) : ℂ := qh w ^ (∑ i : Fin (n / 2), ((n : ℤ) - 1 - 2 * (i : ℕ)) * l i)

def vRes (n a : ℕ) (l : Fin (n / 2) → ℤ) (s : Finset (Fin (n / 2))) : ℤ :=
  -2 * (∑ i ∈ s, ∑ j ∈ sᶜ, max (l i) (l j)) -
    (if n % 2 = 1 then (if a % 2 = 1 then ∑ j ∈ sᶜ, l j else ∑ j ∈ s, l j) else 0)

def phiU (n : ℕ) (w : Pl E) (b : GLw n w) (ϖ : (w.adicCompletion E)ˣ) (l : Fin (n / 2) → ℤ) (a : ℕ)
    (y : GLw a w × GLw (n - a) w) : ℂ :=
  ∑ s : Finset (Fin (n / 2)), if h : s.card = a / 2 ∧ sᶜ.card = (n - a) / 2 ∧ a % 2 + (n - a) % 2 = n % 2 then
    (-qh w) ^ (-vRes n a l s) * (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ *
      ((iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) : ℕ) * ((iwGL (n - a) w).relIndex (GlobalTheory.LFun.KGL w (n - a)) : ℕ) *
      dcos a w (tdiag ϖ (sexp a (l ∘ s.orderEmbOfFin h.1))) y.1 *
      dcos (n - a) w (tdiag ϖ (sexp (n - a) (l ∘ sᶜ.orderEmbOfFin h.2.1))) y.2 else 0

def HasVals {w : Pl E} (Q : (w.adicCompletion E)[X]) (a : Fin n → ℤ) : Prop :=
  ∃ u : Fin n → w.adicCompletion E, Q = ∏ i, (X - C (u i)) ∧ ∀ i, u i ≠ 0 ∧ ordL (u i) = a i

def pw {m : ℕ} (y : Fin m → ℂˣ) (l : Fin m → ℤ) : ℂ := ∏ i, ((y i ^ l i : ℂˣ) : ℂ)

def pm {m : ℕ} (y : Fin m → ℂˣ) : Multiset ℂˣ := Finset.univ.val.map y + Finset.univ.val.map fun i => (y i)⁻¹

def UnrSupp {w : Pl E} (σ : SmIrr (GLw n w)) (B : Multiset ℂˣ) : Prop :=
  ∃ χ : Fin n → ℂˣ, Finset.univ.val.map χ = B ∧
    GlobalTheory.SmGL.IsSubquotient σ.ρ (GlobalTheory.SmGL.prinSeries fun i => GlobalTheory.SmGL.unrChar (w.adicCompletion E) (χ i))

def SatUL {w : Pl E} (b : GLw n w) (ϖ : w.adicCompletion E) (q : ℕ) (σ : SmIrr (UL n w)) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∃ (p : UL n w ≃* GU (cj w) n) (σ' : SmIrr (GU (cj w) n)), (∀ x, (p x).1 = b⁻¹ * x.1 * b) ∧
    GlobalTheory.LFun.HasSatU ϖ q σ'.ρ α ∧ Nonempty (σ.ρ.Equiv (σ'.ρ.comp p.toMonoidHom))

def UE (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Subgroup (GL (Fin n) E) :=
  UJ (IsCMField.complexConj E).toRingEquiv.toRingHom 1

def finPt (γ : UE E n) : finU E n := toSub _ (toSub _ (finGL E n (ratF E n γ.1)))

def ratFinU (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Subgroup (finU E n) :=
  (((UE E n).map ((finGL E n).comp (ratF E n))).comap (UA E n).subtype).comap (finU E n).subtype

def locPt (w : Pl E) (γ : UE E n) : UL n w := toSub _ (GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ.1)

def globLev (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) : Subgroup (finU E n) :=
  ⨅ w ∈ S, ((K' w).map (UL n w).subtype).comap ((cLoc w).comp (finU E n).subtype)

def globFn (S : Set (Pl E)) (f : ∀ w : Pl E, UL n w → ℂ) (x : finU E n) : ℂ := ∏ᶠ w ∈ S, f w (toSub _ (cLoc w x.1))

def RF (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : Representation ℂ (finU E n) (UA E n → ℂ) :=
  (RU E n).comp (finU E n).subtype

def forms (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)) :
    Submodule ℂ (UA E n → ℂ) :=
  ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∀ v, HasWeightAt π v.embedding (lam v)),
    π ⊓ fixed (RF E n) (globLev S K')

def hop (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) :
    (UA E n → ℂ) →ₗ[ℂ] (UA E n → ℂ) :=
  levOp (RF E n) (globLev S (KL n)) (globLev S K') (globFn S f) LinearMap.id

def dimW (lam : InfinitePlace E → DomWeight n) : ℂ :=
  ∏ v, LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n (lam v) 1)

def geomURat (lam : InfinitePlace E → DomWeight n) (orb : UE E n → ℂ) : ℂ :=
  ∑ᶠ c : TwCl (MonoidHom.id (UE E n)), if c.rep.1.val.charpoly.Separable then
    mass (MonoidHom.id _) (ratFinU E n) (finPt c.rep) * chW lam c.rep.1.val.charpoly * orb c.rep else 0

def nfac {k : Type} [Field k] (P : k[X]) : ℕ := Multiset.card (UniqueFactorizationMonoid.normalizedFactors P)

end GlobalTheory.BCT
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWLit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}

def blk {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  (Matrix.fromBlocks a b c d).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def IsWittBasis (J : Matrix (Fin n) (Fin n) E) (l : E) (T : GL (Fin (n + n)) E) : Prop :=
  ∃ Z : Matrix (Fin n) (Fin n) E, (2 : E) • (J * Z.map σ) = l • (1 : Matrix (Fin n) (Fin n) E) ∧ T.1 = blk 1 Z 1 (-Z)

def inBasis {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (T : GL (Fin (n + n)) E) (g : UA σ J₂) :
    Matrix (Fin (n + n)) (Fin (n + n)) (AE F E) := incM F (T⁻¹).1 * mat g * incM F T.1

def IsStdK {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} (T : GL (Fin (n + n)) E) (K : Subgroup (UA σ J₂)) : Prop :=
  ∀ g, g ∈ K ↔
    (∀ v i j, compFin F E v (inBasis σ T g i j) ∈ intLoc F E v ∧ compFin F E v (inBasis σ T g⁻¹ i j) ∈ intLoc F E v) ∧
    ∀ (w : InfinitePlace F) (τ : EmbOver E w), (inBasis σ T g).map (piInf τ) ∈ Matrix.unitaryGroup (Fin (n + n)) ℂ

variable {JV : Matrix (Fin m) (Fin m) E} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E} {κ : Type} [Fintype κ]

def IsAdapted (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ) : Prop :=
  (∀ x : Matrix (Fin m) (Fin (n + n)) E, ∃ y z : κ → F,
    co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
  (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) ∧
  ∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0

variable (F κ) in

def IsTamagawa [MeasurableSpace (κ → AF F)] (μ : Measure (κ → AF F)) : Prop :=
  μ.IsAddHaarMeasure ∧ ∃ 𝓕 : Set (κ → AF F), μ 𝓕 = 1 ∧
    IsAddFundamentalDomain (AddMonoidHom.compLeft (algebraMap F (AF F)).toAddMonoidHom κ).range 𝓕 μ

structure IsWeilFormulas (ψ : AddChar (AF F) ℂ) (χ : Chr F E) (T : GL (Fin (n + n)) E)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ)
    [MeasurableSpace (κ → AF F)] (μ : Measure (κ → AF F))
    (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ)) : Prop where

  pres : ∀ p, ∀ Φ ∈ schA F κ, om p Φ ∈ schA F κ

  lin : ∀ h, ∀ Φ ∈ schA F κ, ∀ u : Matrix (Fin m) (Fin (n + n)) (AE F E), (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) →
    om (h, 1) Φ (co.e u).1 = Φ (co.e (mat h⁻¹ * u)).1

  levi : ∀ p : siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype,
    (p : UA σ J₂) ∈ leviSubOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype →
    ∀ Φ ∈ schA F κ, ∀ u : Matrix (Fin m) (Fin (n + n)) (AE F E), (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) →
    om (1, (p : UA σ J₂)) Φ (co.e u).1 = (χ (aOf finSumFinEquiv _ p) : ℂ) *
      npow (absE F E (aOf finSumFinEquiv _ p)) ((m : ℂ) / 2) * Φ (co.e (u * (mat (p : UA σ J₂)⁻¹)ᵀ)).1

  unip : ∀ b ∈ unipOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype,
    ∀ Φ ∈ schA F κ, ∀ u : Matrix (Fin m) (Fin (n + n)) (AE F E), (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) →
    om (1, b) Φ (co.e u).1 =
      ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂) (u * (mat b)ᵀ) u) * Φ (co.e u).1

  weyl : ∀ w : UA σ J₂, inBasis σ T w = blk 0 1 (-1) 0 → ∃ (γ : ℂ) (k : ℕ), 0 < k ∧ γ ^ k = 1 ∧
    ∀ Φ ∈ schA F κ, ∀ u : Matrix (Fin m) (Fin (n + n)) (AE F E), (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) →
    om (1, w) Φ (co.e u).1 = γ * ∫ y, Φ y * ψ (y ⬝ᵥ (co.e (u * (mat w⁻¹)ᵀ)).2) ∂μ

end GlobalTheory.SWLit

end
end

