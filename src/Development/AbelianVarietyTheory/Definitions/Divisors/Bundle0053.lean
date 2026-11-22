import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.AnisoClauseOfFirstTerm
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FirstTermSplit

open GlobalTheory.RegSch

def AnisoClause : Prop :=
  ∀ (D : D7) (n : ℕ) (T T' : HSp D) (t : ℕ) (d : HypDec T T' t),
    T.rank + T'.rank = 2 * n → T'.rank < T.rank → 0 < T'.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ T.rank →
  ∀ (μ : Measure (Mx D T.rank n)) (𝓕 : Set (Mx D T.rank n)), IsCovolOne (ratMx D T.rank n) μ 𝓕 →
  ∀ (μ' : Measure (Mx D T'.rank n)) (𝓕' : Set (Mx D T'.rank n)), IsCovolOne (ratMx D T'.rank n) μ' 𝓕' →
  ∀ (μ₁ : Measure (Mx D t n)) (𝓕₁ : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ₁ 𝓕₁ →
  ∀ (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ T.rank n)) (ω' : StdUnn.G D n →* Module.End ℂ (schwartzA θ T'.rank n)),
    StdUnn.IsWeilSch ψ χ θ T μ ω → StdUnn.IsWeilSch ψ χ θ T' μ' ω' →
  ∀ H : StdUnn.G D n → ℝ≥0, StdUnn.IsHeight H →
  ∀ (l : Lvl T) (l' : Lvl T'), l.Good → l'.Good → Compat d l l' → HasIw d l.K →
  ∀ ν : Measure l.K, ν.IsHaarMeasure → IsProbabilityMeasure ν →
  ∀ m : Measure (GA D T'), m.IsHaarMeasure →
  ∀ lr : D.what₂.Tau → ℝ, StdUnn.HasRealPar ψ θ lr →
  ∀ s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ τ, IsCartanInv (gramAt D T τ) (s τ)) →
    (∀ k ∈ l.K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T k) * s τ = s τ * compAt θ τ (Formalism.L2.Theta.mt T k)) →
    IsAniso T' → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Φ : schwartzA θ T.rank n, Φ.1 ∈ StdUnn.fockA θ T n lr s → KFin ω Φ →
      ∀ Φ' : schwartzA θ T'.rank n, Φ'.1 = ikS d μ₁ (projS ν Φ.1) → ∀ g (A : ℂ),
        ResidueAt (eisS ω H Φ g) (StdUnn.s0 T n) A → A = κ * StdUnn.thetaInt ω' m Φ' g

def IsoClause : Prop :=
  ∀ (D : D7) (n : ℕ) (T T' : HSp D) (t : ℕ) (d : HypDec T T' t),
    T.rank + T'.rank = 2 * n → T'.rank < T.rank → 0 < T'.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ → ∀ θ : InfFam D, IsInfFam θ →
  ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → ResEta D χ T.rank →
  ∀ (μ : Measure (Mx D T.rank n)) (𝓕 : Set (Mx D T.rank n)), IsCovolOne (ratMx D T.rank n) μ 𝓕 →
  ∀ (μ' : Measure (Mx D T'.rank n)) (𝓕' : Set (Mx D T'.rank n)), IsCovolOne (ratMx D T'.rank n) μ' 𝓕' →
  ∀ (μ₁ : Measure (Mx D t n)) (𝓕₁ : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ₁ 𝓕₁ →
  ∀ (ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ T.rank n)) (ω' : StdUnn.G D n →* Module.End ℂ (schwartzA θ T'.rank n)),
    StdUnn.IsWeilSch ψ χ θ T μ ω → StdUnn.IsWeilSch ψ χ θ T' μ' ω' →
  ∀ H : StdUnn.G D n → ℝ≥0, StdUnn.IsHeight H →
  ∀ (l : Lvl T) (l' : Lvl T'), l.Good → l'.Good → Compat d l l' → HasIw d l.K →
  ∀ ν : Measure l.K, ν.IsHaarMeasure → IsProbabilityMeasure ν →
  ∀ m : Measure (GA D T'), m.IsHaarMeasure →
  ∀ lr : D.what₂.Tau → ℝ, StdUnn.HasRealPar ψ θ lr →
  ∀ s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ τ, IsCartanInv (gramAt D T τ) (s τ)) →
    (∀ k ∈ l.K, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T k) * s τ = s τ * compAt θ τ (Formalism.L2.Theta.mt T k)) →
    ∀ (T₀ : HSp D) (r' : ℕ) (d₀ : HypDec T' T₀ r'), IsAniso T₀ → 0 < r' →
    ∀ l₀ : Lvl T₀, l₀.Good → Compat d₀ l' l₀ → HasIw d₀ l'.K →
    ∀ (τ : D.what₂.Tau) (zG zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), IsRegS τ ω' d₀ l'.K zG zH P →
      ∃ κ : ℂ, κ ≠ 0 ∧ ∀ Φ : schwartzA θ T.rank n, Φ.1 ∈ StdUnn.fockA θ T n lr s → KFin ω Φ →
        ∀ Φ' Ψ : schwartzA θ T'.rank n, Φ'.1 = ikS d μ₁ (projS ν Φ.1) → Ψ.1 = cenH θ τ T' zH Φ'.1 → ∀ g (A B : ℂ),
          ResidueAt (eisS ω H Φ g) (StdUnn.s0 T n) A → ResidueAt (regIntS ω' d₀ l'.K m P Ψ g) (rhoH T' r') B → A = κ * B

theorem firstTerm_iff : GlobalTheory.Published.FirstTermIdentityResidues ↔ AnisoClause ∧ IsoClause := by
  constructor
  · intro h
    constructor
    · intro D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk
      exact (h D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk).1
    · intro D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk
      exact (h D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk).2
  · rintro ⟨ha, hi⟩ D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk
    exact ⟨ha D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk,
      hi D n T T' t d h₁ h₂ h₃ ψ hψ θ hθ χ hχ hη μ 𝓕 hμ μ' 𝓕' hμ' μ₁ 𝓕₁ hμ₁ ω ω' hω hω' H hH l l' hl hl' hc hI ν hν hν' m hm lr hlr s hs hk⟩

theorem anisoClause_of_firstTerm (h : GlobalTheory.Published.FirstTermIdentityResidues) : AnisoClause :=
  (firstTerm_iff.1 h).1

theorem isoClause_of_firstTerm (h : GlobalTheory.Published.FirstTermIdentityResidues) : IsoClause :=
  (firstTerm_iff.1 h).2

theorem firstTerm_of_clauses (ha : AnisoClause) (hi : IsoClause) : GlobalTheory.Published.FirstTermIdentityResidues :=
  firstTerm_iff.2 ⟨ha, hi⟩

example (ha : AnisoClause) : GlobalTheory.Published.FirstTermIdentityResidues ↔ IsoClause :=
  ⟨isoClause_of_firstTerm, firstTerm_of_clauses ha⟩

example (hi : IsoClause) : GlobalTheory.Published.FirstTermIdentityResidues ↔ AnisoClause :=
  ⟨anisoClause_of_firstTerm, fun ha => firstTerm_of_clauses ha hi⟩

end GlobalTheory.FirstTermSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsotropicComplGram
section
noncomputable section

open scoped TensorProduct NNReal Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWInt

open GlobalTheory.SWLit GlobalTheory.SWWeil

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
  {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

def IsWeylElt (T : GL (Fin (n + n)) E) (w : UA σ J₂) : Prop := inBasis σ T w = blk 0 1 (-1) 0

variable {σ}

omit [NumberField E] in

theorem incM_mul_inv {k : ℕ} (T : GL (Fin k) E) : incM F T.1 * incM F (T⁻¹).1 = 1 := by
  rw [incM, incM, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

omit [NumberField E] in

theorem mat_eq_inBasis (T : GL (Fin (n + n)) E) (g : UA σ J₂) :
    mat g = incM F T.1 * inBasis σ T g * incM F (T⁻¹).1 := by
  rw [inBasis, ← Matrix.mul_assoc, ← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul, Matrix.mul_assoc, incM_mul_inv,
    Matrix.mul_one]

omit [NumberField E] in

theorem inBasis_mul (T : GL (Fin (n + n)) E) (g h : UA σ J₂) :
    inBasis σ T (g * h) = inBasis σ T g * inBasis σ T h := by
  have e : mat (g * h) = mat g * mat h := rfl
  rw [inBasis, inBasis, inBasis, e]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (incM F T.1), incM_mul_inv, Matrix.one_mul]

section Weyl

variable {T : GL (Fin (n + n)) E} {w w' : UA σ J₂}

omit [NumberField E] in

theorem exists_isWeylElt (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} {l : E} (hl : l ≠ 0)
    (hJ : ∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) (h₂ : J₂ = dblGram finSumFinEquiv J) (hT : IsWittBasis σ J l T) :
    ∃ w ∈ ratU σ J₂, IsWeylElt σ T w := WittModel.exists_weyl hσ hl hJ h₂ hT

omit [NumberField E] in

theorem IsWeylElt.mat_mul (h : IsWeylElt σ T w) : mat w * incM F T.1 = incM F T.1 * blk 0 1 (-1) 0 := by
  rw [← h, inBasis, ← Matrix.mul_assoc, ← Matrix.mul_assoc, incM_mul_inv, Matrix.one_mul]

omit [NumberField E] in

theorem IsWeylElt.mat_mul_self (h : IsWeylElt σ T w) : mat (w * w) = -1 := by
  have e : (blk 0 1 (-1) 0 * blk 0 1 (-1) 0 : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)) = -1 := by
    rw [WittModel.blk_mul, ← WittModel.blk_one]
    refine congrArg (fun X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) =>
      X.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) (a₂ := -Matrix.fromBlocks 1 0 0 1) ?_
    rw [Matrix.fromBlocks_neg]
    simp
  rw [mat_eq_inBasis T, inBasis_mul, h, e, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, incM_mul_inv]

omit [NumberField E] in

theorem IsWeylElt.mulVec_diag (h : IsWeylElt σ T w) {J : Matrix (Fin n) (Fin n) E} {l : E} (hT : IsWittBasis σ J l T)
    {v : Fin (n + n) → AE F E} (hv : v ∈ diagSub (AE F E) finSumFinEquiv) :
    mat w *ᵥ v ∈ antiSub (AE F E) finSumFinEquiv := by
  obtain ⟨Z, -, hZ⟩ := hT
  have hT : incM F T.1 = blk 1 (incM F Z) 1 (-incM F Z) := by
    simp only [hZ, incM, blk, ← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_neg _ (map_neg (inclR (F := F) (E := E) (AF F)))]
  have hb : ∀ (a b c d : Matrix (Fin n) (Fin n) (AE F E)) (x y : Fin n → AE F E), blk a b c d *ᵥ pairVec finSumFinEquiv x y =
      pairVec finSumFinEquiv (a *ᵥ x + b *ᵥ y) (c *ᵥ x + d *ᵥ y) := fun a b c d x y => by simp [mulVec_pairVec, blk]
  obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hv
  have e : pairVec finSumFinEquiv x x = incM F T.1 *ᵥ pairVec finSumFinEquiv x 0 := by simp [hT, hb]
  rw [e, Matrix.mulVec_mulVec, h.mat_mul, ← Matrix.mulVec_mulVec, hT, hb, hb, pairVec_mem_antiSub]
  simp [Matrix.neg_mulVec, Matrix.mulVec_neg]

omit [NumberField E] in

theorem IsWeylElt.not_mem_siegelOf (h : IsWeylElt σ T w) {J : Matrix (Fin n) (Fin n) E} {l : E} (hT : IsWittBasis σ J l T)
    (hn : 1 ≤ n) : w ∉ siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype := fun hw => by
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  haveI : Invertible (2 : AE F E) := Invertible.copy (Invertible.map (algebraMap F (AE F E)) 2) 2 (map_ofNat _ 2).symm
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  haveI : Nontrivial (AE F E) := inferInstanceAs (Nontrivial (AF F ⊗[F] E))
  have hv : pairVec finSumFinEquiv (1 : Fin n → AE F E) 1 ∈ diagSub (AE F E) finSumFinEquiv := (pairVec_mem_diagSub _).2 rfl
  have h0 : mat w *ᵥ pairVec finSumFinEquiv (1 : Fin n → AE F E) 1 = 0 :=
    Submodule.disjoint_def.1 (isCompl_diagSub_antiSub finSumFinEquiv).disjoint _ ((hw _).1 hv) (h.mulVec_diag hT hv)
  have h1 := congrArg (mat w *ᵥ ·) h0
  have e : mat w * mat w = -1 := h.mat_mul_self
  simp only [Matrix.mulVec_mulVec, e, Matrix.neg_mulVec, Matrix.one_mulVec, Matrix.mulVec_zero, neg_eq_zero] at h1
  have h2 := congrFun h1 (finSumFinEquiv (.inl ⟨0, hn⟩))
  rw [pairVec_inl] at h2
  exact one_ne_zero h2

end Weyl

variable (σ) in

def IsNormN (νN : Measure (unipN σ J₂)) : Prop :=
  νN.IsHaarMeasure ∧ ∃ 𝓓 : Set (unipN σ J₂), IsFundamentalDomain (ratN σ J₂) 𝓓 νN ∧ νN 𝓓 = 1

section Int

variable (νN : Measure (unipN σ J₂)) (w : UA σ J₂)

def intM (f : UA σ J₂ → ℂ) (g : UA σ J₂) : ℂ := ∫ x : unipN σ J₂, f (w * x * g) ∂νN

def IntConv (f : UA σ J₂ → ℂ) (g : UA σ J₂) : Prop := Integrable (fun x : unipN σ J₂ => f (w * x * g)) νN

def HasIntCont (f : ℂ → UA σ J₂ → ℂ) : Prop :=
  (∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → ∀ g, IntConv νN w (f s) g) ∧ ∀ g, Cont.Continues fun s => intM νN w (f s) g

def coefM (f : ℂ → UA σ J₂ → ℂ) (s₁ : ℂ) (k : ℤ) (g : UA σ J₂) : ℂ := Cont.laurent (fun s => intM νN w (f s) g) s₁ k

def contM (f : ℂ → UA σ J₂ → ℂ) (s : ℂ) (g : UA σ J₂) : ℂ := Cont.cont (fun z => intM νN w (f z) g) s

variable {νN w} {f f' : UA σ J₂ → ℂ} {g : UA σ J₂}

omit [NumberField E] in

theorem IntConv.add (h : IntConv νN w f g) (h' : IntConv νN w f' g) : IntConv νN w (f + f') g := Integrable.add h h'

omit [NumberField E] in

theorem IntConv.smul (h : IntConv νN w f g) (c : ℂ) : IntConv νN w (c • f) g := Integrable.smul c h

omit [NumberField E] in

theorem intM_smul (c : ℂ) (f : UA σ J₂ → ℂ) (g : UA σ J₂) : intM νN w (c • f) g = c * intM νN w f g :=
  integral_const_mul c _

variable {φ : ℂ → UA σ J₂ → ℂ}

end Int

section Eis

variable (K : Subgroup (UA σ J₂))

def eisFlat (φ : UA σ J₂ → ℂ) (t : ℂ) (g : UA σ J₂) (z : ℂ) : ℂ :=
  Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂)
    (flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K φ t z) g

def eisAt (φ : UA σ J₂ → ℂ) (t : ℂ) (g : UA σ J₂) : ℂ := Cont.cont (eisFlat K φ t g) t

variable {K}

end Eis

section Sec

variable {JV : Matrix (Fin m) (Fin m) E} {κ : Type} (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ))
  (K : Subgroup (UA σ J₂))

def secMap : ((κ → AF F) → ℂ) →ₗ[ℂ] (UA σ J₂ → ℂ) where
  toFun Φ g := om (1, g) Φ 0
  map_add' Φ Ψ := funext fun g => by simp
  map_smul' a Φ := funext fun g => by simp

omit [NumberField E] in

@[simp] theorem secMap_apply (Φ : (κ → AF F) → ℂ) (g : UA σ J₂) : secMap om Φ g = om (1, g) Φ 0 := rfl

omit [NumberField E] in

theorem kFin_iff (Φ : (κ → AF F) → ℂ) : FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) ↔
    ∃ W : Submodule ℂ ((κ → AF F) → ℂ), FiniteDimensional ℂ W ∧ ∀ k ∈ K, om (1, k) Φ ∈ W :=
  ⟨fun h => ⟨_, h, fun k hk => Submodule.subset_span ⟨k, hk, rfl⟩⟩, fun ⟨_, _, h⟩ =>
    Submodule.finiteDimensional_of_le (Submodule.span_le.2 (by rintro _ ⟨k, hk, rfl⟩; exact h k hk))⟩

variable [Fintype κ]

def kFinSch : Submodule ℂ ((κ → AF F) → ℂ) where
  carrier := {Φ | Φ ∈ schA F κ ∧ FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ})}
  zero_mem' := ⟨zero_mem _, (kFin_iff om K _).2 ⟨⊥, inferInstance, fun k _ => by simp⟩⟩
  add_mem' := fun {Φ Ψ} h h' => ⟨add_mem h.1 h'.1, by
    obtain ⟨W, _, hW⟩ := (kFin_iff om K _).1 h.2
    obtain ⟨W', _, hW'⟩ := (kFin_iff om K _).1 h'.2
    exact (kFin_iff om K _).2 ⟨W ⊔ W', inferInstance, fun k hk => by
      rw [map_add]; exact Submodule.add_mem_sup (hW k hk) (hW' k hk)⟩⟩
  smul_mem' := fun c Φ h => ⟨Submodule.smul_mem _ c h.1, by
    obtain ⟨W, _, hW⟩ := (kFin_iff om K _).1 h.2
    exact (kFin_iff om K _).2 ⟨W, inferInstance, fun k hk => by rw [map_smul]; exact W.smul_mem c (hW k hk)⟩⟩

def secSpace : Submodule ℂ (UA σ J₂ → ℂ) := (kFinSch om K).map (secMap om)

variable {om K}

omit [NumberField E] in

theorem mem_secSpace {f : UA σ J₂ → ℂ} : f ∈ secSpace om K ↔
    ∃ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) ∧
      f = fun g => om (1, g) Φ 0 :=
  ⟨fun ⟨Φ, h, e⟩ => ⟨Φ, h.1, h.2, e.symm⟩, fun ⟨Φ, h, h', e⟩ => ⟨Φ, ⟨h, h'⟩, e.symm⟩⟩

end Sec

section Compl

variable {L : Type} [Field L]

def complGram (l : L) (JV : Matrix (Fin m) (Fin m) L) (t : ℕ) : Matrix (Fin (m + (t + t))) (Fin (m + (t + t))) L :=
  blkMat finSumFinEquiv JV (l⁻¹ • blk (0 : Matrix (Fin t) (Fin t) L) 1 1 0)

end Compl

example : complGram (2 : ℚ) !![3] 1 = !![3, 0, 0; 0, 0, 1 / 2; 0, 1 / 2, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [complGram, blkMat, blk, finSumFinEquiv, Fin.addCases, Matrix.fromBlocks]

example : (blk (n := 1) 0 1 (-1) 0 : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] := by
  decide

example (w g : UA σ J₂) (f : UA σ J₂ → ℂ) (hf : Measurable f) (x : unipN σ J₂)
    (hm : Measurable fun y : unipN σ J₂ => w * y * g) : intM (Measure.dirac x) w f g = f (w * x * g) :=
  integral_dirac' _ _ (hf.comp hm).stronglyMeasurable

end GlobalTheory.SWInt

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj)
open GlobalTheory.PRep (IsAdmissible)

noncomputable section

namespace GlobalTheory.TrMult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def finFn (V : HSp D) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) : GfC V → ℂ :=
  fun g => ∏ᶠ v, ff v (proj D.sp.cm.sig V.gram v (g : GA D V))

def IsFinMeas (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (ν : Measure (GfC V)) : Prop :=
  ν.IsHaarMeasure ∧ ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∫ g, finFn V ff g ∂ν = ∏ᶠ v, ∫ x, ff v x ∂μf v

def HasTypeVec {V : HSp D} (T : TypeDataG V) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) : Prop :=
  ∃ x : W, x ≠ 0 ∧ (∀ v ∉ T.S, ∀ k ∈ Kv V v, σ (locFin V v k) x = x) ∧
    ∀ v : T.S, x ∈ Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W,
      (∀ (k : Kv V v) z, φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ}

def SphRest {V : HSp D} (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) : Prop :=
  ∀ v ∉ T.S, v ≠ U.u → ∀ k ∈ Kv V v, ∀ k' ∈ Kv V v, ∀ g, ff v (k * g * k') = ff v g

def IsIrrFam {V : HSp D} {n : ℕ} {W : Fin n → Type} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GfC V) (W i)) : Prop :=
  (∀ i, (σ i).IsIrreducible) ∧ (∀ i, IsAdmissible (σ i)) ∧ ∀ i j, i ≠ j → IsEmpty ((σ i).Equiv (σ j))

def TRCusp : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V),
    Odd V.rank → (∀ ρ, Gap (lam ρ)) → (∀ ρ i, M.lam ρ i = lam ρ i) → NoFixed T →
    ∀ (V' : HSp D) (hr : V'.rank = V.rank) (S' : D.what₂.Tau → SPar) (M' : DSModel V' S'), (∀ ρ i, M'.lam ρ i = lam ρ (i.cast hr)) →
    ∀ j : ∀ v, GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v, (∀ v, IsLatticeConj (frameLat V) (frameLat V') (j v)) →
    ∀ Φ : GfC V ≃ₜ* GfC V', (∀ v g, Φ (locFin V v g) = locFin V' v (j v g)) →
    ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (μ' : Measure (GA D V')) [μ'.IsHaarMeasure]
      [μ'.IsMulRightInvariant] (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W),
      σ.IsIrreducible → IsAdmissible σ → HasTypeVec T σ →
      mCuspDS μ σ M = mCuspDS μ' (σ.comp Φ.symm.toMulEquiv.toMonoidHom) M'

def SpecFin : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
      mCuspDS μ σ M < Cardinal.aleph0) ∧
    ∀ K : Subgroup (GfC V), IsOpen (K : Set (GfC V)) →
      ∃ (n : ℕ) (Ws : Fin n → Type) (_ : ∀ i, AddCommGroup (Ws i)) (_ : ∀ i, Module ℂ (Ws i))
        (σs : ∀ i, Representation ℂ (GfC V) (Ws i)), IsIrrFam σs ∧
        ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
          mCuspDS μ σ M ≠ 0 → (∃ x : W, x ≠ 0 ∧ ∀ k ∈ K, σ k x = x) → ∃ i, Nonempty (σ.Equiv (σs i))

def SpecTrace : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestData V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν →
    ∀ (n : ℕ) (Ws : Fin n → Type) [∀ i, AddCommGroup (Ws i)] [∀ i, Module ℂ (Ws i)] (σs : ∀ i, Representation ℂ (GfC V) (Ws i)),
      IsIrrFam σs →
      (∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
        mCuspDS μ σ M ≠ 0 → ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V ff) 0 → ∃ i, Nonempty (σ.Equiv (σs i))) →
      ∀ c : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i)) →
        HasTrace (RopG V μ (tensor D.sp.cm.sig V.gram fa ff)) (∑ i, ((mCuspDS μ (σs i) M).toNat : ℂ) * c i)

def Separation : Prop :=
  ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V), U.u ∉ T.S →
    ∀ (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) →
    ∀ ν, IsFinMeas V μf ν →
    ∀ (n : ℕ) (Ws : Fin n → Type) [∀ i, AddCommGroup (Ws i)] [∀ i, Module ℂ (Ws i)] (σs : ∀ i, Representation ℂ (GfC V) (Ws i)),
      IsIrrFam σs → ∀ a : Fin n → ℂ,
      (∀ ff, IsTestFin T U μf ff → SphRest T U ff →
        ∀ c : Fin n → ℂ, (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν (σs i) (finFn V ff) (c i)) → ∑ i, a i * c i = 0) →
      ∀ i, HasTypeVec T (σs i) → a i = 0

def HyperZero : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestData V lam M T U μa μf μ fa ff →
    ∀ γ : GRat D.sp.cm.sig V.gram, IsRegSS γ.1.1 → ¬ Irreducible γ.1.1.charpoly →
      ¬ GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1 →
      GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.ZeroClause μ (tensor D.sp.cm.sig V.gram fa ff) (ratEmb D.sp.cm.sig V.gram γ)

def EllTrace : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w))
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]
    (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ),
    IsTestData V lam M T U μa μf μ fa ff →
      HasTrace (RopG V μ (tensor D.sp.cm.sig V.gram fa ff))
        (∫ q, descend (GQ V) (ellKernel V (tensor D.sp.cm.sig V.gram fa ff)) q ∂autMeasure V μ)

def RealStable : Prop :=
  ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S)
    (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ),
    Odd V.rank → (∀ ρ, StrictAnti (lam ρ)) → (∀ ρ i, M.lam ρ i = lam ρ i) → (∀ w, (μa w).IsHaarMeasure) → IsTestArchG M μa fa →
    ∀ (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau) (dt : Measure (Tor P (placeOf D ρ).Completion)), dt.IsHaarMeasure →
      Phi (J := V.gram) (μa (placeOf D ρ)) dt (fa (placeOf D ρ)) = PhiReal P (embOverOf D ρ) (lam ρ) dt

end GlobalTheory.TrMult

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.OverPair
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

def OverPair (ι : Qbar l ≃+* ℂ) (w₀ : HeightOneSpectrum (𝓞 E)) (τ : E →+* ℂ) : Prop :=
  (∀ x : 𝓞 E, x ∈ w₀.asIdeal → ‖ι.symm (τ (x : E))‖ < 1) ∨
    (∀ x : 𝓞 E, x ∈ w₀.asIdeal → ‖ι.symm (τ (IsCMField.complexConj E (x : E)))‖ < 1)

def CongTyWt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (w₀ : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ →
    ∀ (K : Subgroup (UA E a)), IsLevelAway w₀ K → ∀ (lam lam' : (E →+* ℂ) → DomWeight a) (Jx : Type)
      (t : Jx → (UA E a →₀ ℂ)) (η : Submodule ℂ (UA E a → ℂ) → Jx → ℂ),
      (∀ j, IsIntegralOpW ι lam w₀ (t j)) → (∀ j, IsIntegralOpW ι lam' w₀ (t j)) → ActsBy K t η →
      (∀ τ, lam' τ ≠ lam τ → OverPair ι w₀ τ) →
      (∃ U₀ : Submodule ℂ (UA E a → ℂ), IsAutRepU U₀ ∧ ∀ τ, HasWeightAt U₀ τ (lam' τ)) →
    ∀ (m : ℕ) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))), IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) →
      IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) → (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) →
      (∀ x ∈ J, ∃ y : Matrix (Fin a) (Fin a) (w₀.adicCompletion E), IntMat w₀ y ∧
        ((x : GL (Fin a) (w₀.adicCompletion E)) : Matrix (Fin a) (Fin a) (w₀.adicCompletion E)) =
          1 + ((l : w₀.adicCompletion E) ^ m) • y) →
    ∀ (θ : J →* Multiplicative (ZMod (l ^ m))), Function.Surjective θ →
    ∀ U, OfType lam K U → HasTypeVec w₀ K J θ 1 U →
      ∃ (s : Finset (Jx → Qbar l)) (c : (Jx → Qbar l) → Qbar l),
        (s : Set (Jx → Qbar l)) ⊆ {ϑ | ∃ U', OfType lam' K U' ∧ (∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧
          HasTypeVec w₀ K J θ χ U') ∧ ϑ = fun j => ι.symm (η U' j)} ∧
        ∀ P : MvPolynomial Jx ℤ, ‖MvPolynomial.aeval (fun j => ι.symm (η U j)) P - ∑ ϑ ∈ s, c ϑ * MvPolynomial.aeval ϑ P‖ ≤
          ((l : ℝ)⁻¹) ^ m

end GlobalTheory.CongW
end
end

