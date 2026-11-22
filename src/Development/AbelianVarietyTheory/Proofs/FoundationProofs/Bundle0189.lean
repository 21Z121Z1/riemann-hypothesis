import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0183
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfMemKummer
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem GlobalTheory.KZ.exists_pot_rel_of_mem_bSet : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.BSet N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), H3.Rel X l b F := by
  intro Ω _ _ _ ε X _ hj N l w hl h2 hN hc hw b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨φ, hφ, hφ'⟩ := hj
  exact GlobalTheory.T.exists_kummerPotentialRelation_padic Ω ε X l ⟨φ, hφ', hφ⟩ N w (by omega) h2
    ((Nat.Prime.coprime_iff_not_dvd hl.out).1 hc.symm) hw b (Submodule.subset_span hb)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInjectiveCuspExpansionRingHomStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_cuspExpansion_ringHom : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ e : GlobalTheory.FN.ring ε.range →+* HahnSeries ℚ Ω, Function.Injective e ∧ ∀ a : GlobalTheory.FN.ring ε.range, IsExp ε a (e a) := by
  first | exact @GlobalTheory.FN.expansion_injective_ringHom | exact GlobalTheory.FN.expansion_injective_ringHom | (intros; apply GlobalTheory.FN.expansion_injective_ringHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSturmBoundIsModularFormCoeffSeqStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sturmBound_isModularFormCoeffSeq : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a, MF k L (ch ε) a → (∀ n < B, a n = 0) → a = 0 := by
  first | exact @GlobalTheory.EisM.sturm_coef_zero | exact GlobalTheory.EisM.sturm_coef_zero | (intros; apply GlobalTheory.EisM.sturm_coef_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ForallFieldIffForallSubgroup
section
noncomputable section

namespace GlobalTheory.PointIrredCompare

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ReductionClauses
open scoped Pointwise

section Galois

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem mem_smul_iff (A : ValuationSubring Ω) (g : G F Ω) (y : Ω) :
    y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := by
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]

theorem valuation_smul_lt_one_iff (A : ValuationSubring Ω) (g : G F Ω) (y : Ω) :
    (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', mem_smul_iff, mem_smul_iff, map_inv₀,
    map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]

theorem conj_mem_Ine_of_smul {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, mem_smul_iff]
      have : (g⁻¹ : G F Ω) (g x) = x := by
        show (g⁻¹ * g) x = x
        simp
      rw [this]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (valuation_smul_lt_one_iff A g _).1 (hσ.2 _ hx')
    have e : (g⁻¹ : G F Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
      rw [map_sub]
      congr 1
      show (g⁻¹ * g) x = x
      simp
    rwa [e] at h

theorem Ine_le_of_normal [IsAlgClosure F Ω] {A B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)}
    (hA : IsPlaceOver A w) (hB : IsPlaceOver B w) (Hs : Subgroup (G F Ω)) [hn : Hs.Normal]
    (h : Ine (F := F) A ≤ Hs) : Ine (F := F) B ≤ Hs := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver hA hB
  intro σ hσ
  have := hn.conj_mem _ (h (conj_mem_Ine_of_smul hσ)) g
  simpa [mul_assoc] using this

end Galois

section Hyps

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem lpDim_spehLoc (p : Part A.CG) (w : PlE H) : A.lpDim (spehLoc N A p w) = p.a * p.d := by
  have h : ∀ l : List ℝ, A.lpDim (l.foldr
      (fun k acc => A.lpSum (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) acc) (A.lpZero w)) =
      p.a * l.length := by
    intro l
    induction l with
    | nil => simp [A.lpDim_zero]
    | cons a l ih => simp only [List.foldr_cons, A.lpDim_sum, A.lpDim_tw, A.locG_dim, ih, List.length_cons]; ring
  unfold spehLoc
  rw [h]
  simp

theorem lpDim_isoLoc (P : List (Part A.CG)) (w : PlE H) : A.lpDim (isoLoc N A P w) = rankIso N A P := by
  induction P with
  | nil => simp [isoLoc, rankIso, A.lpDim_zero]
  | cons p P ih =>
    have : isoLoc N A (p :: P) w = A.lpSum (spehLoc N A p w) (isoLoc N A P w) := rfl
    rw [this, A.lpDim_sum, ih, lpDim_spehLoc]
    simp [rankIso]

theorem rank_of_hasParamX {i : N.Loc} {x : N.X i} {Sig : List (Part A.CG)} (h : HasParamX N A i x Sig) :
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso N A Sig = R.r := by
  obtain ⟨P, -, h1, -, h3, -⟩ := h
  refine ⟨fun p hp => ?_, ?_⟩
  · have := h1 ⟨p.a, A.tw p.π A.etaTinv, p.d⟩
      (List.mem_map.2 ⟨p, List.mem_append_left _ hp, rfl⟩)
    exact ⟨this.1, this.2.1⟩
  · simp only [rankIso, twistIso, muPart, List.map_map, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Ranks.nV] at h3 ⊢
    have e : List.map ((fun p : Part A.CG => p.a * p.d) ∘
        fun p : Part A.CG => (⟨p.a, A.tw p.π A.etaTinv, p.d⟩ : Part A.CG)) Sig =
        List.map (fun p : Part A.CG => p.a * p.d) Sig := rfl
    rw [e] at h3
    omega

def FullLabels (Sig : List (Part A.CG)) : Prop :=
  ∀ (k : Fin 2) (v : N.PlG k),
    (A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v))).natDegree = A.lpDim (isoLoc N A Sig (A.plGw k v))

theorem fullLabels_of_good {i : N.Loc} {x : N.X i} {Sig : List (Part A.CG)} (h : HasParamX N A i x Sig)
    (hg : goodSig N A Sig) : FullLabels N A Sig := fun k v => by
  rw [lpDim_isoLoc, (rank_of_hasParamX N A h).2]
  exact ((hg k).1.1 v).2.1

def WildTrivial (Sig : List (Part A.CG)) : Prop :=
  ∀ k, ∀ w ∈ placesOver H.E (H.g k), DepthZero N A (isoLoc N A Sig w)

def TameChosen (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) : Prop :=
  ∀ k : Fin 2, N.l i ≠ H.g k → ∀ w ∈ placesOver H.E (H.g k),
    ¬ ((redRep N i ρ (N.gam0 i w) : GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) :
        Matrix (Fin R.r) (Fin R.r) (IsLocalRing.ResidueField (N.O i))).charpoly.IsRoot
      (IsLocalRing.residue (N.O i) ((N.chi i 1 (N.gam0 i w) : (N.O i)ˣ) : N.O i))

def CoreConcl (i : N.Loc) (Sig : List (Part A.CG)) : Prop :=
  IsCuspIso N A Sig ∧ ∀ ρ, IsRepOfSig N A i Sig ρ → ClauseB N A i ρ ∧ ClauseC N A i ρ ∧ TameChosen N i ρ

variable {A} in

def SurplusConcl (T : NTypes A) (i : N.Loc) (Sig : List (Part A.CG)) : Prop :=
  (∀ π : A.CG R.r, Sig = [⟨R.r, π, 1⟩] → A.csd π ∧ A.ralg π) ∧
  (∀ i', i' ≠ i → ∀ ρ, IsRepOfSig N A i' Sig ρ → ClauseB N A i' ρ ∧ ClauseC N A i' ρ) ∧
  ∀ i' ρ, IsRepOfSig N A i' Sig ρ → ClauseD N T i' ρ ∧ ClauseTame N i' ρ

end Hyps

def Core (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Part D.naut.CG)), HasParamX D.nd D.naut i x Sig →
    goodSig D.nd D.naut Sig → CoreConcl D.nd D.naut i Sig

def CoreTame (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Part D.naut.CG)), HasParamX D.nd D.naut i x Sig →
    WildTrivial D.nd D.naut Sig → goodSig D.nd D.naut Sig → CoreConcl D.nd D.naut i Sig

def Surplus (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Part D.naut.CG)), HasParamX D.nd D.naut i x Sig →
    WildTrivial D.nd D.naut Sig → goodSig D.nd D.naut Sig → SurplusConcl D.nd D.ntypes i Sig

def DepthLink (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (x : D.nd.X i) (Sig : List (Part D.naut.CG)), HasParamX D.nd D.naut i x Sig →
    FullLabels D.nd D.naut Sig → WildTrivial D.nd D.naut Sig

end GlobalTheory.PointIrredCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisUniformizerRingStable
section
noncomputable section

namespace GlobalTheory.RingAsStable

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

section General

variable {R : Type} [CommRing R]

def adicHull (C : Subring R) (π : R) : Subring R :=
  ⨅ m : ℕ, (C.map (Ideal.Quotient.mk (Ideal.span {π ^ m}))).comap
    (Ideal.Quotient.mk (Ideal.span {π ^ m}))

theorem mem_adicHull {C : Subring R} {π a : R} :
    a ∈ adicHull C π ↔ ∀ m : ℕ, ∃ p ∈ C, π ^ m ∣ p - a := by
  simp only [adicHull, Subring.mem_iInf, Subring.mem_comap, Subring.mem_map, Ideal.Quotient.eq,
    Ideal.mem_span_singleton]

theorem le_adicHull (C : Subring R) (π : R) : C ≤ adicHull C π := fun a ha =>
  mem_adicHull.2 fun _ => ⟨a, ha, by simp⟩

theorem mem_adicHull_of_approx {C : Subring R} {π a : R}
    (h : ∀ m : ℕ, ∃ p ∈ adicHull C π, π ^ m ∣ p - a) : a ∈ adicHull C π := by
  refine mem_adicHull.2 fun m => ?_
  obtain ⟨p, hp, hpa⟩ := h m
  obtain ⟨q, hq, hqp⟩ := mem_adicHull.1 hp m
  exact ⟨q, hq, by simpa using dvd_add hqp hpa⟩

theorem stable_closure (S : Set R) (π : R) (A : Subring R)
    (hA : Subring.closure (insert π S) ≤ A) (σ : R →+* R) (hS : ∀ w ∈ S, σ w = w)
    (u : R) (hu : u ∈ A) (hσ : σ π = π * u) (p : R) (hp : p ∈ Subring.closure (insert π S)) :
    σ p ∈ A ∧ ∃ b ∈ A, σ p - p = π * b := by
  have hπ : π ∈ A := hA (Subring.subset_closure (Set.mem_insert _ _))
  have key : ∃ b ∈ A, σ p - p = π * b := by
    induction hp using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨u - 1, A.sub_mem hu A.one_mem, by rw [hσ]; ring⟩
      · exact ⟨0, A.zero_mem, by rw [hS x hx]; ring⟩
    | zero => exact ⟨0, A.zero_mem, by simp⟩
    | one => exact ⟨0, A.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨b, hb, h⟩ := hx
      obtain ⟨c, hc, h'⟩ := hy
      exact ⟨b + c, A.add_mem hb hc, by rw [map_add]; linear_combination h + h'⟩
    | neg x _ hx =>
      obtain ⟨b, hb, h⟩ := hx
      exact ⟨-b, A.neg_mem hb, by rw [map_neg]; linear_combination -h⟩
    | mul x y hx' hy' hx hy =>
      obtain ⟨b, hb, h⟩ := hx
      obtain ⟨c, hc, h'⟩ := hy
      refine ⟨(x + π * b) * c + b * y, A.add_mem (A.mul_mem (A.add_mem (hA hx')
        (A.mul_mem hπ hb)) hc) (A.mul_mem hb (hA hy')), ?_⟩
      rw [map_mul]
      linear_combination (σ y) * h + (x + π * b) * h'
  refine ⟨?_, key⟩
  obtain ⟨b, hb, h⟩ := key
  have : σ p = p + π * b := by linear_combination h
  rw [this]
  exact A.add_mem (hA hp) (A.mul_mem hπ hb)

theorem stable_adicHull [IsDomain R] (S : Set R) (π : R) (hπ0 : π ≠ 0) (σ : R →+* R)
    (hS : ∀ w ∈ S, σ w = w) (u : R) (hu : u ∈ adicHull (Subring.closure (insert π S)) π)
    (hσ : σ π = π * u) (a : R) (ha : a ∈ adicHull (Subring.closure (insert π S)) π) :
    σ a ∈ adicHull (Subring.closure (insert π S)) π ∧
      ∃ b ∈ adicHull (Subring.closure (insert π S)) π, σ a - a = π * b := by
  have H := stable_closure S π _ (le_adicHull _ π) σ hS u hu hσ
  have approx : ∀ m : ℕ, ∃ b ∈ adicHull (Subring.closure (insert π S)) π,
      ∃ r, σ a - a = π * (b + π ^ m * r) := by
    intro m
    obtain ⟨p, hp, r, hr⟩ := mem_adicHull.1 ha (m + 1)
    obtain ⟨-, b, hb, h⟩ := H p hp
    have h2 := congrArg σ hr
    rw [map_sub, map_mul, map_pow, hσ, mul_pow] at h2
    exact ⟨b, hb, r - u ^ (m + 1) * σ r, by linear_combination h - h2 + hr⟩
  obtain ⟨b0, -, r0, h0⟩ := approx 0
  have hb : b0 + π ^ 0 * r0 ∈ adicHull (Subring.closure (insert π S)) π := by
    refine mem_adicHull_of_approx fun m => ?_
    obtain ⟨b, hb, r, h⟩ := approx m
    refine ⟨b, hb, -r, ?_⟩
    have := mul_left_cancel₀ hπ0 (h0.symm.trans h)
    linear_combination -this
  refine ⟨?_, _, hb, h0⟩
  have : σ a = a + π * (b0 + π ^ 0 * r0) := by linear_combination h0
  rw [this]
  exact Subring.add_mem _ ha (Subring.mul_mem _
    (le_adicHull _ π (Subring.subset_closure (Set.mem_insert _ _))) hb)

end General

theorem piS_ne_zero {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s ≠ 0 := by
  intro h
  have h1 : WittVector.teichmuller l (AI.εroot s) = 1 := sub_eq_zero.1 h
  have h2 : AI.εroot s = 1 := by
    have := congrArg (fun x : Ainf l => x.coeff 0) h1
    simpa using this
  apply AI.ε_ne_one
  have h3 : ((frobeniusEquiv (OCb l) l).symm)^[s] (1 : OCb l) = 1 :=
    Function.iterate_fixed (map_one _) s
  exact ((frobeniusEquiv (OCb l) l).symm.injective.iterate s) (h2.trans h3.symm)

theorem ringAs_stable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (σ : Ainf l →+* Ainf l), (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.wittFixedFrobeniusPow K, σ w = w) → (∃ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s, σ (GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s) = GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s * u) → ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s, σ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s ∧ ∃ b ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s, σ a - a = GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s * b := by
  intro l _ P AI K s σ hS ⟨u, hu, hσ⟩ a ha
  haveI : IsDomain (Ainf l) := inferInstance
  exact stable_adicHull _ _ (piS_ne_zero AI s) σ hS u hu hσ a ha

end GlobalTheory.RingAsStable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussValuationUniqueOnLthRootLevelFieldsStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussValuation_unique_on_lthRoot_level_fields : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring (AlgebraicClosure X.K), Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₁ → Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₂ → ∀ (θ : AlgebraicClosure X.K) (f : X.Kˣ), f ∈ X.Un l → Lev X M₀ f → θ ^ l = algebraMap X.K (AlgebraicClosure X.K) (f : X.K) → ∀ x ∈ IntermediateField.adjoin (levF X M₀) {θ}, x ∈ W₁ ↔ x ∈ W₂ := by
  first | exact @GlobalTheory.KZ.ES.UniqRoot.gauss_unique_root | exact GlobalTheory.KZ.ES.UniqRoot.gauss_unique_root | (intros; apply GlobalTheory.KZ.ES.UniqRoot.gauss_unique_root <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobalPositivityIneqMultiplicativeCoeffStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_positivity_ineq_multiplicative_coeff : ∀ (M : ℕ) (b ω : ℕ → ℂ) (s C : ℝ), 0 < s → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → ∀ X : ℕ, Real.exp (∑ p ∈ (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M), ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s)) ≤ 2 * (1 + 1 / s) * ‖LSeries b ((1 + s : ℝ) : ℂ)‖ ^ 2 * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) := by
  first | exact @GlobalTheory.EisM.global_positivity_ineq | exact GlobalTheory.EisM.global_positivity_ineq | (intros; apply GlobalTheory.EisM.global_positivity_ineq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodTupleProjectorIsProjCentralStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodTupleProjector_isProj_central : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (m : ℕ) (ι : Type) [Fintype ι] (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ), (∀ v, IsSeries (τ v)) → IsProj (eGood τ ch) ∧ ∀ a, conv (eGood τ ch) a = conv a (eGood τ ch) := by
  first | exact @GlobalTheory.BadShare.eGood_isProj_central | exact GlobalTheory.BadShare.eGood_isProj_central | (intros; apply GlobalTheory.BadShare.eGood_isProj_central <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumInvariantOfStableStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacterSlashSum_invariant_of_stable : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι : Type) [Fintype ι] (β : ι → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → N ∣ L' → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → (∀ δ ∈ Δ, ∀ γ : SL(2, ℤ), (L' : ℤ) ∣ γ 1 0 → δ * (γ : M2) ∈ Δ) → LRep L Δ β → Inv k L (ch ε) f → Inv k L' (ch ε) (hsum k (ch ε) β f) := by
  first | exact @GlobalTheory.EisM.hsum_inv_of_stable | exact GlobalTheory.EisM.hsum_inv_of_stable | (intros; apply GlobalTheory.EisM.hsum_inv_of_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeStableCongruenceConjDiamondMatrixStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeStableCongruence_conj_diamondMatrix : ∀ (N l d : ℕ) (σ : SL(2, ℤ)) (r : Matrix (Fin 2) (Fin 2) ℤ), IsDiam N l d σ → PP N l r → PP N l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
  first | exact @GlobalTheory.KZ.StabHecke.congruenceCondition_conj_diamond | exact GlobalTheory.KZ.StabHecke.congruenceCondition_conj_diamond | (intros; apply GlobalTheory.KZ.StabHecke.congruenceCondition_conj_diamond <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermiteRightFactorOfPrimeDvdDetStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermite_right_factor_of_prime_dvd_det : ∀ (p : ℕ), p.Prime → ∀ (m : Matrix (Fin 2) (Fin 2) ℤ), (p : ℤ) ∣ m.det → (∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![(p : ℤ), 0; 0, 1]) ∨ ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![1, (k : ℤ); 0, (p : ℤ)] := by
  first | exact @GlobalTheory.hermite_right_factor_prime_det | exact GlobalTheory.hermite_right_factor_prime_det | (intros; apply GlobalTheory.hermite_right_factor_prime_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowMulExpUnitStripOneLeStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_im_rpow_mul_exp_unitStrip_one_le : ∀ (r c : ℝ), 0 < c → IntegrableOn (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im)) {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
  first | exact @GlobalTheory.EisM.integrableOn_im_rpow_mul_exp_strip_one_le | exact GlobalTheory.EisM.integrableOn_im_rpow_mul_exp_strip_one_le | (intros; apply GlobalTheory.EisM.integrableOn_im_rpow_mul_exp_strip_one_le <;> assumption)
end

