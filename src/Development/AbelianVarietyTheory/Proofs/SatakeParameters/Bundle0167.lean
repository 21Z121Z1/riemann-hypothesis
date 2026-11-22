import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
import Formalism.LocalToGlobal.KernelLattices.KerMtPin
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0116
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0146
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.ClusteredLetterwiseBoxes
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsAtPrimeUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DivUnique

section Abstract

variable {R K : Type} [CommRing R] [CommRing K] {n : ℕ}

theorem read_one {Λ : (Fin n → R) → Prop} {O : R → Prop} {OK : Subring K} {ε : R} (φ : R →+* K) (s : K → R)
    (hs : ∀ t, φ (s t) = t) (hε : φ ε = 1) (hO : ∀ x, O x → φ x ∈ OK) (hO' : ∀ t ∈ OK, O (s t))
    {B B' : Matrix (Fin n) (Fin n) R}
    (h1 : ∀ z : Fin n → R, (∀ i, O (z i)) → Λ (ε • B *ᵥ z))
    (h2 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • y = ε • B' *ᵥ z)
    (w : Fin n → K) (hw : ∀ i, w i ∈ OK) :
    ∃ w' : Fin n → K, (∀ i, w' i ∈ OK) ∧ B.map φ *ᵥ w = B'.map φ *ᵥ w' := by
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, φ ∘ (M *ᵥ x) = M.map φ *ᵥ (φ ∘ x) := fun M x =>
    funext fun i => RingHom.map_mulVec φ M x i
  have sm : ∀ x : Fin n → R, φ ∘ (ε • x) = φ ∘ x := fun x => funext fun i => by simp [hε]
  have ss : φ ∘ (s ∘ w) = w := funext fun i => hs _
  obtain ⟨z, hz, e⟩ := h2 _ (h1 (s ∘ w) fun i => hO' _ (hw i))
  refine ⟨φ ∘ z, fun i => hO _ (hz i), ?_⟩
  calc B.map φ *ᵥ w = φ ∘ (B *ᵥ (s ∘ w)) := by rw [mv, ss]
    _ = φ ∘ (ε • (ε • B *ᵥ (s ∘ w))) := by rw [sm, sm]
    _ = φ ∘ (ε • B' *ᵥ z) := by rw [e]
    _ = B'.map φ *ᵥ (φ ∘ z) := by rw [sm, mv]

theorem read_step {Λ : (Fin n → R) → Prop} {O : R → Prop} {OK : Subring K} {ε : R} (φ : R →+* K) (s : K → R)
    (hs : ∀ t, φ (s t) = t) (hε : φ ε = 1) (hO : ∀ x, O x → φ x ∈ OK) (hO' : ∀ t ∈ OK, O (s t))
    {A B B' : Matrix (Fin n) (Fin n) R} {u u' : Fin n → R}
    (h4 : ∀ z : Fin n → R, (∀ i, O (z i)) → ∃ y, Λ y ∧ ε • A *ᵥ y = ε • B *ᵥ (fun i => u i * z i))
    (h3 : ∀ y, Λ y → ∃ z : Fin n → R, (∀ i, O (z i)) ∧ ε • A *ᵥ y = ε • B' *ᵥ (fun i => u' i * z i))
    (w : Fin n → K) (hw : ∀ i, w i ∈ OK) :
    ∃ w' : Fin n → K, (∀ i, w' i ∈ OK) ∧
      (B.map φ * Matrix.diagonal (fun i => φ (u i))) *ᵥ w =
        (B'.map φ * Matrix.diagonal (fun i => φ (u' i))) *ᵥ w' := by
  have mv : ∀ (M : Matrix (Fin n) (Fin n) R) x, φ ∘ (M *ᵥ x) = M.map φ *ᵥ (φ ∘ x) := fun M x =>
    funext fun i => RingHom.map_mulVec φ M x i
  have sm : ∀ x : Fin n → R, φ ∘ (ε • x) = φ ∘ x := fun x => funext fun i => by simp [hε]
  have hu : ∀ u z : Fin n → R, φ ∘ (fun i => u i * z i) = Matrix.diagonal (fun i => φ (u i)) *ᵥ (φ ∘ z) :=
    fun u z => funext fun i => by simp [Matrix.mulVec_diagonal]
  have ss : φ ∘ (s ∘ w) = w := funext fun i => hs _
  obtain ⟨y, hy, e⟩ := h4 (s ∘ w) fun i => hO' _ (hw i)
  obtain ⟨z, hz, e'⟩ := h3 y hy
  refine ⟨φ ∘ z, fun i => hO _ (hz i), ?_⟩
  calc (B.map φ * Matrix.diagonal (fun i => φ (u i))) *ᵥ w
      = φ ∘ (B *ᵥ (fun i => u i * (s ∘ w) i)) := by rw [mv, hu, ss, Matrix.mulVec_mulVec]
    _ = φ ∘ (ε • B *ᵥ (fun i => u i * (s ∘ w) i)) := (sm _).symm
    _ = φ ∘ (ε • B' *ᵥ (fun i => u' i * z i)) := by rw [← e, e']
    _ = (B'.map φ * Matrix.diagonal (fun i => φ (u' i))) *ᵥ (φ ∘ z) := by
      rw [sm, mv, hu, Matrix.mulVec_mulVec]

theorem coset (OK : Subring K) {b b' c c' T T' U : Matrix (Fin n) (Fin n) K}
    (hb : c * b = 1) (hb' : c' * b' = 1) (hT : T' * T = 1)
    (H1 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ b *ᵥ y = b' *ᵥ z)
    (H2 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ b' *ᵥ y = b *ᵥ z)
    (H3 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ (b * T) *ᵥ y = (b' * U) *ᵥ z)
    (H4 : ∀ y : Fin n → K, (∀ i, y i ∈ OK) → ∃ z : Fin n → K, (∀ i, z i ∈ OK) ∧ (b' * U) *ᵥ y = (b * T) *ᵥ z) :
    ∃ k₁ ∈ (Formalism.UG.bc (n := Fin n) OK.subtype).range, ∃ k₂ ∈ (Formalism.UG.bc (n := Fin n) OK.subtype).range,
      k₁.1 * T * k₂.1 = U := by
  obtain ⟨M, hM⟩ := GlobalTheory.PlaceDiv.exists_factor OK b b' H1
  obtain ⟨N, hN⟩ := GlobalTheory.PlaceDiv.exists_factor OK b' b H2
  obtain ⟨M₂, hM₂⟩ := GlobalTheory.PlaceDiv.exists_factor OK (b * T) (b' * U) H3
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.PlaceDiv.exists_factor OK (b' * U) (b * T) H4
  have hMN : M.map OK.subtype * N.map OK.subtype = 1 := by
    calc M.map OK.subtype * N.map OK.subtype = c' * b' * (M.map OK.subtype * N.map OK.subtype) := by
          rw [hb', Matrix.one_mul]
      _ = c' * (b' * M.map OK.subtype * N.map OK.subtype) := by simp only [Matrix.mul_assoc]
      _ = c' * b' := by rw [← hM, ← hN]
      _ = 1 := hb'
  have hl : T' * c * (b * T) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc c, hb, Matrix.one_mul, hT]
  have hNM : N₂.map OK.subtype * M₂.map OK.subtype = 1 := by
    calc N₂.map OK.subtype * M₂.map OK.subtype
        = T' * c * (b * T) * (N₂.map OK.subtype * M₂.map OK.subtype) := by rw [hl, Matrix.one_mul]
      _ = T' * c * (b * T * N₂.map OK.subtype * M₂.map OK.subtype) := by simp only [Matrix.mul_assoc]
      _ = T' * c * (b * T) := by rw [← hN₂, ← hM₂]
      _ = 1 := hl
  obtain ⟨k₁, hk₁, e₁⟩ := GlobalTheory.PlaceDiv.mem_range_of_mul_eq_one OK M N hMN
  obtain ⟨k₂, hk₂, e₂⟩ := GlobalTheory.PlaceDiv.mem_range_of_mul_eq_one OK N₂ M₂ hNM
  refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
  rw [e₁, e₂]
  calc M.map OK.subtype * T * N₂.map OK.subtype = c' * b' * (M.map OK.subtype * T * N₂.map OK.subtype) := by
        rw [hb', Matrix.one_mul]
    _ = c' * (b' * M.map OK.subtype * T * N₂.map OK.subtype) := by simp only [Matrix.mul_assoc]
    _ = c' * (b' * U) := by rw [← hM, ← hN₂]
    _ = U := by rw [← Matrix.mul_assoc, hb', Matrix.one_mul]

end Abstract

set_option maxHeartbeats 1000000 in

theorem div_unique : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d d' : List ℤ) (g : GA D V), IsPrimeIdem P e f → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.Pairwise (fun a b => b ≤ a) → d'.Pairwise (fun a b => b ≤ a) → DivAt V e (ϖ : D.host.E) d g → DivAt V e (ϖ : D.host.E) d' g → d = d' := by
  intro D V P e f ϖ d d' g hP h1 h2 hd hd' hD hD'
  have he : e * e = e := by
    rcases id hP with ⟨hs, -⟩ | ⟨rfl, -⟩
    · exact hs.1.1
    · exact ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P _ _ hP).1
  obtain ⟨φ, s, hs, hε, -, hO, hO', hinc⟩ :=
    GlobalTheory.SphLabelOps.exists_component he (GlobalTheory.SphLabelOps.tie_of_isPrimeIdem hP)
  have hee : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he]
  rw [GlobalTheory.DivDual.divAt_iff] at hD hD'
  obtain ⟨l, B, b1, b2, b3, b4⟩ := hD
  obtain ⟨l', B', b1', b2', b3', b4'⟩ := hD'
  obtain ⟨C, -, c2⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B hee fun y hy => (b2 y hy).imp fun _ h => h.2
  obtain ⟨C', -, c2'⟩ := (GlobalTheory.LatIntFacts.int_facts V).2.2 _ B' hee fun y hy => (b2' y hy).imp fun _ h => h.2
  have mp : ∀ X Y : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E),
      finPart D e • (X * Y) = finPart D e • (1 : Matrix (Fin V.rank) (Fin V.rank) _) → X.map φ * Y.map φ = 1 := by
    intro X Y hXY
    rw [← Matrix.map_mul, ← Matrix.map_one φ (map_zero φ) (map_one φ)]
    refine Matrix.ext fun i j => ?_
    have := congrArg φ (congrFun (congrFun hXY i) j)
    rwa [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, map_mul, hε, one_mul,
      one_mul] at this
  have hv : Formalism.UG.IsUnifV D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) :=
    (P.valuedAdicCompletion_eq_valuation' (ϖ : D.host.E)).trans
      ((P.valuation_of_algebraMap ϖ).trans (GlobalTheory.LatIntFacts.intValuation_uniformiser P h1 h2))
  have h0 := Formalism.UG.P.cartan_unif_ne_zero D.host.E P _ hv
  have e1 : ∀ a : List ℤ, (Matrix.diagonal fun i : Fin V.rank =>
      φ (finPart D (incA D ((ϖ : D.host.E) ^ (a.getD i.1 0))))) =
      Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) fun i : Fin V.rank => a.getD i.1 0 := by
    intro a
    unfold Formalism.UG.diagPow
    congr 1
    funext i
    rw [hinc, map_zpow₀]
  have hinv : (Matrix.diagonal fun i : Fin V.rank => (algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E)) ^ (-(d.getD i.1 0))) *
      Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) (fun i : Fin V.rank => d.getD i.1 0) = 1 := by
    unfold Formalism.UG.diagPow
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← zpow_add₀ h0, neg_add_cancel, zpow_zero]
  obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ := coset (Formalism.UG.Ov D.host.E P) (b := B.map φ) (b' := B'.map φ)
    (c := C.map φ) (c' := C'.map φ)
    (T := Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) fun i : Fin V.rank => d.getD i.1 0)
    (U := Formalism.UG.diagPow D.host.E P (algebraMap D.host.E _ (ϖ : D.host.E)) fun i : Fin V.rank => d'.getD i.1 0)
    (mp _ _ c2) (mp _ _ c2') hinv
    (read_one (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b1 b2')
    (read_one (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b1' b2)
    (by
      rw [← e1, ← e1]
      exact read_step (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b4 b3')
    (by
      rw [← e1, ← e1]
      exact read_step (Λ := fun y => y ∈ Formalism.L2.NTheta.LamHat V) (O := fun x => x ∈ intAE D) φ s hs hε hO hO' b4' b3)
  have anti : ∀ a : List ℤ, a.length = V.rank → a.Pairwise (fun a b => b ≤ a) →
      Antitone fun i : Fin V.rank => a.getD i.1 0 := by
    intro a la ha i j hij
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    · have hi : i.1 < a.length := by rw [la]; exact i.2
      have hj : j.1 < a.length := by rw [la]; exact j.2
      simp only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj]
      exact List.pairwise_iff_getElem.1 ha _ _ hi hj hlt
  have key := Formalism.UG.Final.CartanUnique D.host.E P V.rank _ (Formalism.UG.P.cartan_unif_lt_one D.host.E P _ hv).le hv
    _ _ (anti d l hd) (anti d' l' hd') k₁ hk₁ k₂ hk₂ hk
  refine List.ext_getElem (l.trans l'.symm) fun i hi hi' => ?_
  have := congrFun key ⟨i, by rw [← l]; exact hi⟩
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hi'] using this

end GlobalTheory.DivUnique
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNeZeroMulConjEqOfUnitary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Host Formalism.L2.Col Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.NormOneHilbert90Units

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ne_zero_mul_conj_eq_of_unitary (D : D7) (z : unitary D.host.E) :
    ∃ w : D.host.E, w ≠ 0 ∧ (z : D.host.E) * D.host.conj w = w := by
  have hz : (z : D.host.E) * star (z : D.host.E) = 1 := z.2.2
  have key : ∀ a : D.host.E, (z : D.host.E) * star (a + (z : D.host.E) * star a) = a + (z : D.host.E) * star a := by
    intro a
    rw [star_add, star_mul, star_star]
    linear_combination a * hz
  obtain ⟨x, hx⟩ : ∃ x : D.host.E, star x ≠ x := by
    by_contra h
    push_neg at h
    apply NumberField.IsCMField.complexConj_ne_one D.host.E
    refine AlgEquiv.ext fun x => ?_
    rw [← Formalism.BasicNotions.Examples₂.cmStar_apply]
    exact h x
  by_cases h1 : (1 : D.host.E) + (z : D.host.E) * star (1 : D.host.E) = 0
  · refine ⟨x + (z : D.host.E) * star x, ?_, ?_⟩
    · intro h2
      have hz1 : (z : D.host.E) = -1 := by rw [star_one] at h1; linear_combination h1
      rw [hz1] at h2
      exact hx (by linear_combination -h2)
    · rw [← Formalism.BasicNotions.Examples₂.star_eq_conj]; exact key x
  · exact ⟨_, h1, by rw [← Formalism.BasicNotions.Examples₂.star_eq_conj]; exact key 1⟩

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

end Comparison₂

end GlobalTheory.NormOneHilbert90Units
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.SplitRead

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem eig_lpOfChar (ξ : Weil h →* ℂˣ) (hξ : WeilDeligne.IsSmooth ξ) (σ : Weil h) :
    (WD.lpOfChar h ξ hξ).eig σ = {(ξ σ : ℂ)} := by
  rw [WD.lpOfChar, WD.eig_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp

theorem cls_eq_ofChar (χ : (w.adicCompletion E)ˣ →* ℂˣ) (c : Irr (w.adicCompletion E) 1)
    (hc : Nonempty (c.π.Equiv (detRep (Fin 1) χ))) :
    ∃ hχ : IsSmoothChar χ, cls (toIrrRep c) = .ofChar χ hχ := by
  obtain ⟨φ⟩ := hc
  have h1 : IsSmoothChar (detChar (Fin 1) χ) := (isSmooth_ofChar_iff _).1
    ((IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).isSmooth c.smooth)
  have h2 : Continuous (Matrix.GeneralLinearGroup.scalar (R := w.adicCompletion E) (Fin 1)) :=
    Units.continuous_map (continuous_matrix fun i j => by
      rw [Subsingleton.elim i j]; simpa using continuous_id')
  have h3 : (detChar (Fin 1) χ).comp (Matrix.GeneralLinearGroup.scalar (Fin 1)) = χ := by
    refine MonoidHom.ext fun z => congrArg χ ?_
    ext; simp [Matrix.GeneralLinearGroup.scalar]
  exact ⟨h3 ▸ h1.comp _ h2, congrArg (Sigma.mk 1) (IrrRep.cl_eq_iff.2 ⟨φ⟩)⟩

theorem IsRec.recSupp {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) :
    RecSupp fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  intro n s π d σ hs g
  have h1 := (hasSupport_of_isCuspSupport hs).of_equiv (equivRep (toIrrRep π))
  have h2 := H.supp (cls (toIrrRep π)) _ h1 g
  rw [Multiset.map_map] at h2
  exact h2

theorem IsRec.recUnit {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) :
    RecUnit fun _ (π : Irr (w.adicCompletion E) _) => rc (cls (toIrrRep π)) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  intro χ c hu hc g α hα
  obtain ⟨hχ, e⟩ := cls_eq_ofChar χ c hc
  simp only [e, H.one, eig_lpOfChar, Multiset.mem_singleton] at hα
  rw [hα]
  exact hu _

theorem IsRec.surj {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) (n : ℕ) (y : WD h)
    (hy : y.lpDim = n) : ∃ π : Irr (w.adicCompletion E) n, rc (cls (toIrrRep π)) = y := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  subst hy
  obtain ⟨π, hπ⟩ := H.exists_rep y
  exact ⟨Irr.ofIrrRep π, hπ⟩

end GlobalTheory.LocLanglands
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalCombinationOfFixedLocalTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphAvg

section Abstract

variable {G : Type} [Group G]

open GlobalTheory.SphLabelOps

theorem finiteIndex_stab {K : Subgroup G} {g : G} {R : Finset G} (hR : Reps K g R) :
    (MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K)).FiniteIndex := by
  have hfin : (MulAction.orbit K (QuotientGroup.mk g : G ⧸ K)).Finite := by
    refine (R.finite_toSet.image (fun γ => (QuotientGroup.mk γ : G ⧸ K))).subset ?_
    rintro _ ⟨k, rfl⟩
    obtain ⟨γ, ⟨hγ, e⟩, -⟩ := hR.2 ((k : G) * g) ⟨k, k.2, 1, one_mem _, by simp⟩
    refine ⟨γ, hγ, ?_⟩
    show (QuotientGroup.mk γ : G ⧸ K) = (k : G) • (QuotientGroup.mk g : G ⧸ K)
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq]
    exact e
  refine ⟨?_⟩
  rw [MulAction.index_stabilizer]
  exact ((Set.ncard_pos hfin).2 ⟨_, MulAction.mem_orbit_self _⟩).ne'

theorem mem_of_stab {K : Subgroup G} {g : G} {n : K} (hn : n ∈ MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K)) :
    g⁻¹ * (n : G) * g ∈ K := by
  have h : ((n : G) • (QuotientGroup.mk g : G ⧸ K)) = QuotientGroup.mk g := hn
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq] at h
  have := inv_mem h
  convert this using 1
  group

theorem card_pos {K : Subgroup G} {g : G} {R : Finset G} (hR : Reps K g R) : 0 < R.card := by
  obtain ⟨γ, ⟨hγ, -⟩, -⟩ := hR.2 g ⟨1, one_mem _, 1, one_mem _, by simp⟩
  exact Finset.card_pos.2 ⟨γ, hγ⟩

theorem fixed_comb {K : Subgroup G} {ι : Type} (s : Finset ι) (g : ι → G) (R : ι → Finset G)
    (hR : ∀ i ∈ s, Reps K (g i) (R i)) (a : ι → ℂ) {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : G →* Module.End ℂ M) (u : M) (hu : ∀ k ∈ K, π k u = u)
    (hw : ∀ k ∈ K, π k (∑ i ∈ s, a i • π (g i) u) = ∑ i ∈ s, a i • π (g i) u) :
    ∑ i ∈ s, a i • π (g i) u = ∑ i ∈ s, (a i / ((R i).card : ℂ)) • ∑ γ ∈ R i, π γ u := by
  classical
  have fix : ∀ x, ∀ l ∈ K, π (x * l) u = π x u := fun x l hl => by
    rw [map_mul, Module.End.mul_apply, hu l hl]
  let St : ι → Subgroup K := fun i => MulAction.stabilizer K (QuotientGroup.mk (g i) : G ⧸ K)
  have hSt : (⨅ i ∈ s, St i).FiniteIndex := Subgroup.finiteIndex_iInf' St fun i hi => finiteIndex_stab (hR i hi)
  let N : Subgroup K := (⨅ i ∈ s, St i).normalCore
  haveI : N.FiniteIndex := Subgroup.finiteIndex_normalCore _
  haveI : Fintype (K ⧸ N) := Fintype.ofFinite _
  have hN : ∀ i ∈ s, ∀ n ∈ N, ∀ x : G, π (x * (n : G) * g i) u = π (x * g i) u := by
    intro i hi n hn x
    have h1 : n ∈ St i := (iInf₂_le i hi : (⨅ i ∈ s, St i) ≤ St i) (Subgroup.normalCore_le _ hn)
    have := fix (x * g i) _ (mem_of_stab h1)
    rw [← this]
    congr 1
    group
  let T : ι → M := fun i => ∑ q : K ⧸ N, π ((q.out : G) * g i) u

  have hT : ∀ i ∈ s, ∀ k₁ ∈ K, ∑ q : K ⧸ N, π ((q.out : G) * k₁ * g i) u = T i := by
    intro i hi k₁ hk₁
    have e := Fintype.sum_equiv (Equiv.mulRight (QuotientGroup.mk (⟨k₁, hk₁⟩ : K) : K ⧸ N))
      (fun q => π (((q * QuotientGroup.mk (⟨k₁, hk₁⟩ : K) : K ⧸ N).out : G) * g i) u)
      (fun q => π ((q.out : G) * g i) u) (fun q => rfl)
    refine Eq.trans ?_ e
    refine Finset.sum_congr rfl fun q _ => ?_
    have hq : (q.out * ⟨k₁, hk₁⟩)⁻¹ * (q * QuotientGroup.mk (⟨k₁, hk₁⟩ : K) : K ⧸ N).out ∈ N := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have := hN i hi _ hq ((q.out : G) * k₁)
    rw [← this]
    congr 2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev]
    group
  have hC : ∀ i ∈ s, ((R i).card : ℂ) • T i = (Fintype.card (K ⧸ N) : ℂ) • ∑ γ ∈ R i, π γ u := by
    intro i hi
    have e1 : ∑ γ ∈ R i, ∑ q : K ⧸ N, π ((q.out : G) * γ) u = ∑ γ ∈ R i, T i := by
      refine Finset.sum_congr rfl fun γ hγ => ?_
      obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := (hR i hi).1 γ hγ
      rw [← hT i hi k₁ h₁]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← fix ((q.out : G) * k₁ * g i) k₂ h₂]
      congr 1
      group
    have e2 : ∑ γ ∈ R i, ∑ q : K ⧸ N, π ((q.out : G) * γ) u = ∑ q : K ⧸ N, ∑ γ ∈ R i, π γ u := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun q _ => (hR i hi).sum_eq (hR i hi) q.out.2 (fun x => π x u) fix
    rw [e1, Finset.sum_const, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
      ← Nat.cast_smul_eq_nsmul ℂ] at e2
    exact e2
  have hQ : (Fintype.card (K ⧸ N) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have main : (Fintype.card (K ⧸ N) : ℂ) • ∑ i ∈ s, a i • π (g i) u = ∑ i ∈ s, a i • T i := by
    have e : ∀ q : K ⧸ N, π (q.out : G) (∑ i ∈ s, a i • π (g i) u) = ∑ i ∈ s, a i • π ((q.out : G) * g i) u := by
      intro q
      simp only [map_sum, map_smul, map_mul, Module.End.mul_apply]
    calc (Fintype.card (K ⧸ N) : ℂ) • ∑ i ∈ s, a i • π (g i) u
        = ∑ q : K ⧸ N, π (q.out : G) (∑ i ∈ s, a i • π (g i) u) := by
          rw [Nat.cast_smul_eq_nsmul ℂ, ← Finset.card_univ, ← Finset.sum_const]
          exact Finset.sum_congr rfl fun q _ => (hw _ q.out.2).symm
      _ = ∑ i ∈ s, a i • T i := by
          simp only [e, T, Finset.smul_sum]
          exact Finset.sum_comm
  refine smul_right_injective M hQ ?_
  simp only
  rw [main, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [smul_comm, ← hC i hi, smul_smul, div_mul_cancel₀ _ (Nat.cast_ne_zero.2 (card_pos (hR i hi)).ne')]

end Abstract

end GlobalTheory.SphAvg

namespace GlobalTheory.SphAvg

open GlobalTheory.SphLabelOps GlobalTheory.IdemSupport

theorem fixed_comb_eq_opOf : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ e f, IsPrimeIdem P e f → ∀ a : GA D V →₀ ℂ, (∀ g ∈ a.support, SuppF V f g) → ∃ c : List ℤ →₀ ℂ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → (∀ k ∈ hyp V P, π k (a.sum fun g z => z • π g u) = a.sum fun g z => z • π g u) → (a.sum fun g z => z • π g u) = opOf π P c u := by
  classical
  intro D V P e f h a ha
  obtain ⟨K, hK⟩ := exists_hyp V P
  obtain ⟨-, ϖ, -, h1, h2⟩ := exists_real_unif D P
  have he := (GlobalTheory.HeckeDual.idem_of_isPrimeIdem h).1
  have hd : ∀ g, ∃ d, SuppF V f g → Reps K g (rep V P d) := by
    intro g
    by_cases hg : SuppF V f g
    · obtain ⟨d, hd, hD⟩ := exists_divAt V he (tie_of_isPrimeIdem h) h1 h2 g
      exact ⟨d, fun _ => reps_of_sphOp hK h h1 h2 hg hD (sphOp_rep (isLab_of_divAt h h1 h2 hd hg hD))⟩
    · exact ⟨[], fun h' => absurd h' hg⟩
  choose d hd using hd
  refine ⟨∑ g ∈ a.support, Finsupp.single (d g) (a g / ((rep V P (d g)).card : ℂ)), ?_⟩
  intro M _ _ π u hu hw
  have hu' : ∀ k ∈ K, π k u = u := fun k hk => hu k (by rw [hK]; exact hk)
  have hw' : ∀ k ∈ K, π k (∑ g ∈ a.support, a g • π (id g) u) = ∑ g ∈ a.support, a g • π (id g) u :=
    fun k hk => hw k (by rw [hK]; exact hk)
  rw [Finsupp.sum]
  refine (fixed_comb a.support id (fun g => rep V P (d g)) (fun g hg => hd g (ha g hg)) a π u hu' hw').trans ?_
  rw [opOf, ← Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by rw [add_smul]), LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finsupp.sum_single_index (by simp), LinearMap.smul_apply, LinearMap.sum_apply]

end GlobalTheory.SphAvg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamJointBCD
section
open NumberField IsDedekindDomain Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem HTW.RecS.fam_jointBCD : ∀ {eps : ℝ} (Fm : FamP eps) (R : KillingConditions.RowK), (∀ D : D7, LocalSituation.adm7 D) → (∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL (D := D) i) → ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (j : Fm.Ix x) (HW : HWOf (Fm.D x j).loc) (X : KillingConditions.HubData (Fm.D x j)), GlobalTheory.HTW.LJ.ConclusionJa (Fm.D x j) → (∀ i, TwistedPlaces.TwLoc (Fm.D x j) i → TwistedPlaces.InertK (Fm.D x j) ((Fm.D x j).nd.l i) → ∀ π ∈ (Fm.D x j).nd.Zgood i, GlobalTheory.HTW.RecS.PtIn i (X.r i) (X.ρ i) π) → KillingConditions.JointParametersHubConditions (Fm.L x j) HW X R := by
  intro eps Fm R a b
  obtain ⟨x0, h⟩ := GlobalTheory.HTW.RecS.fam_joints Fm R.C₂ a b
  exact ⟨x0, fun x hx h1 j HW X hJ hP =>
    GlobalTheory.Survey.ClusteredLetterwiseBoxes.frozenBCD_of _ HW X R (h x hx h1 j HW hJ).1 (h x hx h1 j HW hJ).2 hP⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinSigmaFinEquivSymmStrictMonoToLexStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finSigmaFinEquiv_symm_strictMono_toLex : ∀ (s : ℕ) (t : Fin s → ℕ), StrictMono fun c : Fin (∑ a, t a) => (toLex (finSigmaFinEquiv.symm c) : Σₗ a, Fin (t a)) := by
  first | exact @GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex | exact GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex | (intros; apply GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAutomorphismOrbitMemFiniteExtensionPadicStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.ConjugateSelfDual GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_automorphism_orbit_mem_finite_extension_padic : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (J : Type) (z : J → ℂ), (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (z j)).Finite → ∃ L : IntermediateField ℚ_[l] (Qbar l), FiniteDimensional ℚ_[l] L ∧ ∀ j, ι.symm (z j) ∈ L := by
  first | exact @GlobalTheory.orbit_finite_mem_finite_ext | exact GlobalTheory.orbit_finite_mem_finite_ext | (intros; apply GlobalTheory.orbit_finite_mem_finite_ext; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteSkewHermitianValuationMaxQuotSumStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_skewHermitian_valuationMax_quot_sum : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → (∀ K : ℕ, ∃ R : Finset L, (∀ r ∈ R, r ∈ Formalism.UG.intL L) ∧ ∀ c ∈ Formalism.UG.intL L, ∃ r ∈ R, Valued.v (c - r) ≤ Valued.v ϖ ^ K) →
  ∀ (r : ℕ) (e : Fin r → ℕ), Finite (↥(GlobalTheory.Hk3.GramSep.gam σ ϖ e) ⧸
    (GlobalTheory.Hk3.GramSep.gam0 σ ϖ e).addSubgroupOf (GlobalTheory.Hk3.GramSep.gam σ ϖ e)) := by
  first | exact @GlobalTheory.Hk3.GramSep.gam_quot_finite | exact GlobalTheory.Hk3.GramSep.gam_quot_finite | (intros; apply GlobalTheory.Hk3.GramSep.gam_quot_finite <;> assumption)
end

