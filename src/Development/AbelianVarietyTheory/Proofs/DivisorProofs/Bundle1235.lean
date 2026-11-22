import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1196
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1053
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1037
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalEquationChangeFormPerturbedDivisor
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem isLogEqn_changeForm_add : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (n : ℕ),
    topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (η η' : RatForms p n) (x : X) (m mD l : ℕ)
    (gG fD g a F : X.functionFieldˣ) (A : CartierDiv X) (δ t : ℚ), η' ≠ 0 → η = (F : X.functionField) • η' →
    0 < m → 0 < mD → IsLogEqn p Δ η x m gG →
    (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord fD : ℚ) / mD) → A.IsEqn x a →
    ∃ (m₂ : ℕ) (g₂ : X.functionFieldˣ), 0 < m₂ ∧
      IsLogEqn p (Δ + (1 - δ) • D + t • qWeil (CartierDiv.principal g + l • A) 1) η' x m₂ g₂ ∧
      ∀ E : DivOver p, discrep E η' m₂ g₂ = E.formOrd η' + E.ord F - E.ord gG / m
        - (1 - δ) * (E.ord fD / mD) - t * E.ord (g * a ^ l) := by
  intro X _ _ p _ n hn Δ D η η' x m mD l gG fD g a F A δ t hη' hηF hm hmD hg hD hA
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'

  set gG' : X.functionFieldˣ := gG * F ^ (-(m : ℤ)) with hgG'
  have hord (E : DivOver p) : (E.ord gG' : ℚ) = E.ord gG - m * E.ord F := by
    rw [hgG', E.ord_mul, divOver_ord_zpow]
    push_cast
    ring
  have h1 : IsLogEqn p Δ η' x m gG' := by
    intro z hz E hE
    have e := hg z hz E hE
    rw [hηF, E.formOrd_smul hn hη' F] at e
    rw [hord, ← e]
    push_cast
    ring
  have hd1 (E : DivOver p) : discrep E η' m gG' = E.formOrd η' + E.ord F - E.ord gG / m := by
    rw [discrep, hord]
    field_simp
    ring

  obtain ⟨m₁, g₁, hm₁, h2, hd2⟩ := isLogEqn_add_smul X p n Δ D η' x m mD gG' fD (1 - δ) hm hmD h1 hD

  have hB : (CartierDiv.principal g + l • A).IsEqn x (g * a ^ l) :=
    (CartierDiv.isEqn_principal g x).add (hA.nsmul l)
  obtain ⟨V, hxV, hV⟩ := hB.exists_nhds
  have hD' : ∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z →
      qWeil (CartierDiv.principal g + l • A) 1 z = (E.ord (g * a ^ l) : ℚ) / (1 : ℕ) := by
    intro z hz E hE
    rw [qWeil, (hV z (hz.mem_open V.isOpen hxV)).mult_eq, ← hE.ord_eq]
  obtain ⟨m₂, g₂, hm₂, h3, hd3⟩ := isLogEqn_add_smul X p n (Δ + (1 - δ) • D)
    (qWeil (CartierDiv.principal g + l • A) 1) η' x m₁ 1 g₁ (g * a ^ l) t hm₁ Nat.one_pos h2 hD'
  refine ⟨m₂, g₂, hm₂, h3, fun E => ?_⟩
  rw [hd3, hd2, hd1]
  push_cast
  ring

end GlobalTheory.PairStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisorStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Γ D : X → ℚ) (η : RatForms p n) (x : X) (m m' : ℕ) (g f : X.functionFieldˣ) (c : ℚ), 0 < m → 0 < m' → IsLogEqn p Γ η x m g → (∀ z, z ⤳ x → ∀ E : DivOver p, E.IsAt z → D z = (E.ord f : ℚ) / m') → ∃ (m'' : ℕ) (g'' : X.functionFieldˣ), 0 < m'' ∧ IsLogEqn p (Γ + c • D) η x m'' g'' ∧ ∀ E : DivOver p, discrep E η m'' g'' = discrep E η m g - c * ((E.ord f : ℚ) / m') := by
  first | exact @GlobalTheory.PairStep.isLogEqn_add_smul | exact GlobalTheory.PairStep.isLogEqn_add_smul | (intros; apply GlobalTheory.PairStep.isLogEqn_add_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPsEffPullReducedClosedOfDimLeStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPsEff_pull_reduced_closed_of_dim_le : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ), (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k Y) → topologicalKrullDim Y ≤ (d : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) → ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ M : LB X, IsNef k M → ∀ Z : Closeds X, IsIrreducible (Z : Set X) → topologicalKrullDim (Z : Set X) ≤ (d : ℕ) → IsPsEff (M.pull (redι Z)) := by
  first | exact @GlobalTheory.IsNef.isPsEff_pull_red_of_dim_le | exact GlobalTheory.IsNef.isPsEff_pull_red_of_dim_le | (intros; apply GlobalTheory.IsNef.isPsEff_pull_red_of_dim_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPseudoEffectiveReducedUnivOfSectionPowStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPseudoEffective_reducedUniv_of_section_pow : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (M : LB X), M.IsLB → ∀ r : ℕ, 1 ≤ r → HasNonzeroSec (lbPow M r) → ∀ Z : Closeds X, (Z : Set X) = Set.univ → IsPsEff (M.pull (redι Z)) := by
  first | exact @GlobalTheory.isPsEff_pull_redι_univ_of_hasNonzeroSec_pow | exact GlobalTheory.isPsEff_pull_redι_univ_of_hasNonzeroSec_pow | (intros; apply GlobalTheory.isPsEff_pull_redι_univ_of_hasNonzeroSec_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeminormBallFamilySectionBallsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSeminormBallFamily_sectionBalls : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ a b : ℤ, IsBallFam (P.H a b) (P.Bl a b) := by
  first | exact @GlobalTheory.VolBr.Pair.isBallFam | exact GlobalTheory.VolBr.Pair.isBallFam | (intros; apply GlobalTheory.VolBr.Pair.isBallFam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisOfKaehlerWedgeFreeGeneratorStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTranscendenceBasis_of_kaehlerWedge_freeGenerator : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q), 0 < D →
  IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) → TrBasis cL (fun i => (x i : L)) := by
  first | exact @GlobalTheory.FieldPair.trBasis_of_isFreeGen_dForm | exact GlobalTheory.FieldPair.trBasis_of_isFreeGen_dForm | (intros; apply GlobalTheory.FieldPair.trBasis_of_isFreeGen_dForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitStalkTransitionPulledBackFlagFrames
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem GlobalTheory.FlagPush.Dbl.transition_par_stalk : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ z : W.Z, ∀ A₁ ∈ E'.S (W.p₁ z), ∀ A₂ ∈ E'.S (W.p₂ z), Par 0 (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) := by
  intro F _ X Y ι _ m E E' φ f hR W hW z A₁ hA₁ A₂ hA₂
  have hbase := GlobalTheory.T.maps_comp_eq_of_functionField_maps_agree F X Y φ f hR.hom W hW
  have hf : f (W.p₁ z) = f (W.p₂ z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hbase]
  obtain ⟨A, hA⟩ := E.nonempty (f (W.p₁ z))
  have hA' : A ∈ E.S (f (W.p₂ z)) := hf ▸ hA
  have h₁ := hR.sub _ A₁ hA₁ A hA
  have h₂ := hR.sub _ A₂ hA₂ A hA'
  have reg : ∀ (p : W.Z ⟶ Y.X) [IsDominant p], ∀ x ∈ ((ratOf Y).O (p z)).toSubring,
      functionFieldMap p x ∈ (algebraMap (W.Z.presheaf.stalk z) W.Z.functionField).range := by
    intro p _ x hx
    obtain ⟨a, rfl⟩ := mem_O_ratOf.1 hx
    exact ⟨_, (functionFieldMap_algebraMap p z a).symm⟩
  have k₁ := h₁.map W.α₁ (reg W.p₁)
  have k₂ := h₂.map W.α₂ (reg W.p₂)
  set B : Mat m Y.Fn := A.map φ with hBdef
  have hB : ∀ τ, (B τ).det ≠ 0 := fun τ => by
    intro h
    exact Fr.det_ne hA τ ((map_eq_zero (φ : X.Fn →+* Y.Fn)).1 (((φ : X.Fn →+* Y.Fn).map_det (A τ)).trans h))
  have hB₂ : ∀ τ, (B.map W.α₂ τ).det ≠ 0 := fun τ => by
    rw [Mat.det_map]; exact (map_ne_zero _).2 (hB τ)
  have e12 : B.map W.α₁ = B.map W.α₂ := by
    funext τ; ext i j; exact hW (A τ i j)
  have d₁ : A₁ = A₁ * B⁻¹ * B := by rw [mul_assoc, Mat.inv_mul hB, mul_one]
  have d₂ : A₂ = A₂ * B⁻¹ * B := by rw [mul_assoc, Mat.inv_mul hB, mul_one]
  have key : A₁.map W.α₁ * (A₂.map W.α₂)⁻¹ = (A₁ * B⁻¹).map W.α₁ * ((A₂ * B⁻¹).map W.α₂)⁻¹ := by
    conv_lhs => rw [d₁, d₂]
    rw [Mat.map_mul _ _ W.α₁, Mat.map_mul _ _ W.α₂, e12, Mat.mul_inv_rev, mul_assoc, ← mul_assoc (B.map W.α₂),
      Mat.mul_inv hB₂, one_mul]
  rw [key]
  exact k₁.mul k₂.inv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataLogTerminalLogCanonicalGenerisationStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kawamataLogTerminal_logCanonical_generisation : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), ∀ (Γ : X → ℚ) (x z : X), z ⤳ x → (KltAt p n Γ x → KltAt p n Γ z) ∧ (LcAt p n Γ x → LcAt p n Γ z) := by
  first | exact @GlobalTheory.Discrepancy.kltAt_lcAt_generisation | exact GlobalTheory.Discrepancy.kltAt_lcAt_generisation | (intros; apply GlobalTheory.Discrepancy.kltAt_lcAt_generisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def kernSum (S : Set (Pl E)) (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w))
    (f : ∀ w : Pl E, UL n w → ℂ) : ℂ :=
  (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (globLev S K' : Set (finU E n)),
      ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU E n)) :
        ℂ))⁻¹ *
      ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * chW lam γ.1.val.charpoly

def clsSum (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ) (γ : UE E n) : ℂ :=
  (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ q : DoubleCoset.Quotient ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt γ) : Subgroup (finU E n)) : Set (finU E n))
        (globLev S K' : Set (finU E n)),
      ((Nat.card ((ratFinU E n ⊓ twCent (MonoidHom.id _) (finPt γ)) ⊓
          (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU E n)) : ℂ))⁻¹ *
        globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q)

end GlobalTheory.BCT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KottwitzPairTermEqPointSumAnyTrivialisation
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem term_eq_termAt : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ), 0 < r → (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K, ∀ g, φ (k⁻¹ * g * sigG G r k) = φ g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (δ z : Gr G r), IsNrm G r P.atP δ z → P.term Kf f r K φ = P.termAt Kf f r K φ x t hx δ z := by
  intro p _ G P Kf f r K φ hr hf hφ x t hx δ z hn
  have hex : ∃ dz : Gr G r × Gr G r, IsNrm G r P.atP dz.1 dz.2 := ⟨(δ, z), hn⟩
  unfold term
  rw [dif_pos hex]
  set x₀ := P.trivAf.choose
  set t₀ := P.trivAf.choose_spec.choose
  have h₀ : Triv G (AfP p) P.β x₀ t₀ := P.trivAf.choose_spec.choose_spec
  set δ₀ := hex.choose.1
  set z₀ := hex.choose.2
  have hn₀ : IsNrm G r P.atP δ₀ z₀ := hex.choose_spec
  obtain ⟨_, hreg, hcent⟩ := GlobalTheory.T.similitudePair_regular_image_at_p p G P
  obtain ⟨g, hgx⟩ := GlobalTheory.T.hermitianTripleTrivializations_differ_by_group_point p G (AfP p) (P.β : G.C) x x₀ t t₀ hx h₀
  obtain ⟨g₂, hδ, hcz⟩ := GlobalTheory.T.twistedConj_of_twistedNormConj_hermitianTriple_regular p G r P.atP δ z δ₀ z₀ hr hreg hn hn₀
  have htw := GlobalTheory.T.map_centralizer_regular_twistedCentraliser p G r P.atP δ z hr hreg hn
  have hAf : P.toAf x₀ t₀ h₀ = (MulAut.conj g⁻¹⁻¹).toMonoidHom.comp (P.toAf x t hx) := by
    ext y : 1
    apply Subtype.ext
    apply Prod.ext
    · have e : x₀ = (g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 * x := by rw [hgx, inv_mul_cancel_right]
      simp only [toAf, MonoidHom.comp_apply, MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, Prod.fst_mul, Prod.fst_inv, MonoidHom.prodMap, MonoidHom.prod_apply, Subgroup.coe_subtype]
      rw [e]; group
    · simp only [toAf, MonoidHom.comp_apply, MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, Prod.snd_mul, Prod.snd_inv, MonoidHom.prodMap, MonoidHom.prod_apply, Subgroup.coe_subtype]
      rw [mul_comm, inv_mul_cancel_left]
  have hQr : P.toQr r z₀ = (MulAut.conj g₂⁻¹).toMonoidHom.comp (P.toQr r z) := by
    ext y : 1
    have := hcz (locC G y.1) (hcent y)
    simp only [toQr, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [this]
  have hself : P.toAf x₀ t₀ h₀ P.self = g⁻¹⁻¹ * P.toAf x t hx P.self * g⁻¹ := by
    rw [hAf]; simp [MulAut.conj_apply]
  unfold termAt
  rw [hself, hAf, hQr, hδ]
  refine GlobalTheory.T.kottwitzIsogenyClassPointSum_conj_data _ _ _ _ _ _ _ _ _ _ _ hf hφ ?_ ?_
  · intro y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · exact y.2.1
    · exact mul_comm _ _
  · intro y
    have hm : P.toQr r z y ∈ GlobalTheory.BCT.twCent (sigG G r) δ := by
      rw [← htw]; exact ⟨locC G y.1, hcent y, rfl⟩
    exact hm

end GlobalTheory.LKMid.Pair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsEqIffGLintCoset
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLatCoset

variable {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
  (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ} (b : Module.Basis (Fin m) K.E B.A)

def vec (y : Fin m → w.adicCompletion E) : B.A := ∑ i, e.symm (y i) • b i

def crd (a : B.A) : Fin m → w.adicCompletion E := fun i => e (b.repr a i)

def IntV (y : Fin m → w.adicCompletion E) : Prop := ∀ i, y i ∈ Ov E w

lemma vec_crd (a : B.A) : vec e b (crd e b a) = a := by
  simp [vec, crd, b.sum_repr]

lemma crd_vec (y : Fin m → w.adicCompletion E) : crd e b (vec e b y) = y := by
  funext i; simp only [vec, crd]; rw [Module.Basis.repr_sum_self]; simp

lemma sum_cols (M : Matrix (Fin m) (Fin m) (w.adicCompletion E)) (x : Fin m → w.adicCompletion E) :
    ∑ j, e.symm (x j) • vec e b (fun i => M i j) = vec e b (M *ᵥ x) := by
  simp only [vec, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

lemma memOv (x : w.adicCompletion E) : x ∈ Ov E w ↔ Valued.v x ≤ 1 := by
  simp [Ov, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]

lemma intV_mulVec {M : Matrix (Fin m) (Fin m) (w.adicCompletion E)} (hM : ∀ i j, M i j ∈ Ov E w)
    {z : Fin m → w.adicCompletion E} (hz : IntV z) : IntV (M *ᵥ z) := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hM i j) (hz j)

lemma intV_single (j : Fin m) : IntV (w := w) (Pi.single j 1) := by
  intro i
  rcases eq_or_ne i j with rfl | h
  · simp [Subring.one_mem]
  · simp [Pi.single_apply, h, Subring.zero_mem]

lemma gl_vec (h : GL (Fin m) (w.adicCompletion E)) (z : Fin m → w.adicCompletion E) :
    (↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ ((↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

lemma gl_vec' (h : GL (Fin m) (w.adicCompletion E)) (z : Fin m → w.adicCompletion E) :
    (↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ ((↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

lemma preserves_iff (h : GL (Fin m) (w.adicCompletion E)) :
    (∀ z, IntV ((↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z) ↔ IntV z) ↔ h ∈ GLint (Fin m) (Ov E w) := by
  constructor
  · intro H
    have hh : ∀ i j, (↑h : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j ∈ Ov E w := by
      intro i j
      have := (H (Pi.single j 1)).2 (intV_single j) i
      simpa [Matrix.mulVec_single_one] using this
    have hi : ∀ i j, (↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j ∈ Ov E w := by
      intro i j
      have := (H ((↑h⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ Pi.single j 1)).1 (by rw [gl_vec']; exact intV_single j) i
      simpa [Matrix.mulVec_single_one] using this
    have inj : Function.Injective ((Ov E w).subtype.mapMatrix :
        Matrix (Fin m) (Fin m) (Ov E w) →+* Matrix (Fin m) (Fin m) (w.adicCompletion E)) := by
      intro A A' hAA
      exact Matrix.ext fun i j => Subtype.ext (congrArg (fun M : Matrix (Fin m) (Fin m) (w.adicCompletion E) => M i j) hAA)
    let M1 : Matrix (Fin m) (Fin m) (Ov E w) := Matrix.of fun i j => ⟨_, hh i j⟩
    let M2 : Matrix (Fin m) (Fin m) (Ov E w) := Matrix.of fun i j => ⟨_, hi i j⟩
    have e1 : (Ov E w).subtype.mapMatrix M1 = ↑h := Matrix.ext fun i j => rfl
    have e2 : (Ov E w).subtype.mapMatrix M2 = ↑h⁻¹ := Matrix.ext fun i j => rfl
    let k : GL (Fin m) (Ov E w) :=
      ⟨M1, M2, inj (by rw [map_mul, map_one, e1, e2, ← Units.val_mul, mul_inv_cancel, Units.val_one]),
        inj (by rw [map_mul, map_one, e1, e2, ← Units.val_mul, inv_mul_cancel, Units.val_one])⟩
    exact ⟨k, Units.ext (Matrix.ext fun i j => rfl)⟩
  · rintro ⟨k, rfl⟩ z
    have ent : ∀ (k : GL (Fin m) (Ov E w)) i j,
        ((bc (Ov E w).subtype k : GL (Fin m) (w.adicCompletion E)) : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j ∈ Ov E w :=
      fun k i j => (k.val i j).2
    constructor
    · intro hz
      have := intV_mulVec (ent k⁻¹) hz
      rwa [map_inv, gl_vec] at this
    · exact intV_mulVec (ent k)

lemma mem_lat (hI : ∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) (g : GLw m w) (a : B.A) :
    a ∈ GlobalTheory.TwLat.lat e b g ↔
      IntV ((↑g⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a) := by
  constructor
  · intro ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      have : crd e b (∑ i, e.symm ((↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) • b i) =
          (↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ Pi.single j 1 := by
        rw [Matrix.mulVec_single_one]
        exact crd_vec e b _
      rw [this, gl_vec]
      exact intV_single j
    | zero =>
      have : crd e b (0 : B.A) = 0 := by funext i; simp [crd]
      rw [this, Matrix.mulVec_zero]
      intro i; exact Subring.zero_mem _
    | add x y _ _ hx hy =>
      have : crd e b (x + y) = crd e b x + crd e b y := by funext i; simp [crd]
      rw [this, Matrix.mulVec_add]
      intro i; exact Subring.add_mem _ (hx i) (hy i)
    | smul c x _ hx =>
      have hc : e (algebraMap K.O K.E c) ∈ Ov E w := (memOv _).2 ((hI _).1 ⟨c, rfl⟩)
      have : crd e b (c • x) = e (algebraMap K.O K.E c) • crd e b x := by
        funext i; simp only [crd, Pi.smul_apply, smul_eq_mul]; rw [← algebraMap_smul K.E c x, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
      rw [this, Matrix.mulVec_smul]
      intro i; exact Subring.mul_mem _ hc (hx i)
  · intro hx
    set x := (↑g⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a with hxdef
    have hr : ∀ j, e.symm (x j) ∈ (algebraMap K.O K.E).range := fun j =>
      (hI _).2 (by rw [RingEquiv.apply_symm_apply]; exact (memOv _).1 (hx j))
    choose c hc using hr
    have hsum : a = ∑ j, c j • vec e b (fun i => (↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) := by
      simp_rw [← algebraMap_smul K.E (c _), hc]
      rw [sum_cols, hxdef, gl_vec', vec_crd]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem lat_coset : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) →
    (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) →
    (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ)
    (b : Module.Basis (Fin m) K.E B.A),
    (∀ g g' : GLw m w, GlobalTheory.TwLat.lat e b g = GlobalTheory.TwLat.lat e b g' ↔ g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w m) ∧
      ∀ g : GLw m w, GlobalTheory.UnitLemma.IsLat K.O K.E (GlobalTheory.TwLat.lat e b g) := by
  intro E _ _ _ _ w _ K e _ hI _ B m b
  refine ⟨fun g g' => ?_, fun g => ?_⟩
  · show _ ↔ g⁻¹ * g' ∈ GLint (Fin m) (Ov E w)
    rw [SetLike.ext_iff, ← preserves_iff]
    simp only [mem_lat e b hI]
    constructor
    · intro H z
      have := H (vec e b ((↑g' : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ z))
      rw [crd_vec, gl_vec] at this
      rwa [Units.val_mul, ← Matrix.mulVec_mulVec]
    · intro H a
      have := H ((↑g'⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a)
      rwa [Units.val_mul, ← Matrix.mulVec_mulVec, gl_vec'] at this
  · refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
    rw [eq_top_iff]
    intro a _
    have hsum : a = ∑ j, e.symm (((↑g⁻¹ : Matrix (Fin m) (Fin m) (w.adicCompletion E)) *ᵥ crd e b a) j) •
        vec e b (fun i => (↑g : Matrix (Fin m) (Fin m) (w.adicCompletion E)) i j) := by
      rw [sum_cols, gl_vec', vec_crd]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩))

end GlobalTheory.TwLatCoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSpannedByGLColumnsMulLeftMatrixEqMul
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.TwLatMul

theorem col_eq {E : Type} [Field E] [NumberField E] {w : Pl E} {K : GlobalTheory.UnitLemma.UQ}
    (e : K.E ≃+* w.adicCompletion E) {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ}
    (b : Module.Basis (Fin m) K.E B.A) (a : B.A) (g h : GLw m w)
    (hh : h.val = GlobalTheory.TwLat.mulMat e b a * g.val) (j : Fin m) :
    ∑ i, e.symm (h.val i j) • b i = a * ∑ i, e.symm (g.val i j) • b i := by
  set M := LinearMap.toMatrix b b (LinearMap.mulLeft K.E a) with hM
  have hij : ∀ i, e.symm (h.val i j) = ∑ k, M i k * e.symm (g.val k j) := by
    intro i
    rw [hh]
    simp [Matrix.mul_apply, GlobalTheory.TwLat.mulMat, map_sum, map_mul, hM]
  have hab : ∀ k, a * b k = ∑ i, M i k • b i := by
    intro k
    simp only [hM, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply]
    exact (b.sum_repr _).symm
  simp_rw [hij, Finset.mul_sum, mul_smul_comm, hab, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  simp_rw [mul_comm]

theorem lat_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A), ∀ (a : B.A) (g h : GLw m w), h.val = GlobalTheory.TwLat.mulMat e b a * g.val → GlobalTheory.TwLat.lat e b h = GlobalTheory.UnitLemma.mulLat K.O a (GlobalTheory.TwLat.lat e b g) := by
  intro E _ _ _ _ w _ K e _ _ _ B m b a g h hh
  unfold GlobalTheory.TwLat.lat GlobalTheory.UnitLemma.mulLat
  rw [Submodule.map_span, ← Set.range_comp]
  refine congrArg _ (congrArg Set.range (funext fun j => ?_))
  exact col_eq e b a g h hh j

end GlobalTheory.TwLatMul
end

