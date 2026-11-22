import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0687
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.ConjugateSelfDual.Statement
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0860
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianVolumeLieBasis
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoordLattice

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLastRowMonomialReadsCoefficientStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPairing_lastRow_monomial_reads_coefficient : ∀ (K : Type) [Field K] (n : ℕ) (b : Fin n → ℕ), (∀ (x : BP K n) (p : MvPolynomial (Fin n × Fin n) K), fockB x (zmon K n b * emb K n p) = (bfact b : K) * fockB (coefOne K n b (incl K n x)) p) ∧ ∀ p q : MvPolynomial (Fin n × Fin n) K, fockB (zmon K n b * emb K n q) (zmon K n b * emb K n p) = (bfact b : K) * fockB q p := by
  first | exact @GlobalTheory.BrCoefFock.fockB_zmon_emb | exact GlobalTheory.BrCoefFock.fockB_zmon_emb | (intros; apply GlobalTheory.BrCoefFock.fockB_zmon_emb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfRegularForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG Polynomial
open scoped TensorProduct

namespace GlobalTheory.SphPar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def HasDiv {n : ℕ} (O : Subring L) (d : List ℤ) (g : GL (Fin n) L) : Prop :=
  ∃ ϖ : L, Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
    ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O,
      (g : Matrix (Fin n) (Fin n) L) =
        (a : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) * (b : Matrix (Fin n) (Fin n) L)

def divInd {n : ℕ} (O : Subring L) (d : List ℤ) : GL (Fin n) L → ℂ := Set.indicator {g | HasDiv O d g} 1

def bcPar (n : ℕ) (α : Fin (n / 2) → ℂ) : Multiset ℂ :=
  Finset.univ.val.map α + Finset.univ.val.map (fun i => (α i)⁻¹) + Multiset.replicate (n % 2) 1

def ParU (σ : L →+* L) (q n : ℕ) (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) : Prop :=
  (0 : ℂ) ∉ s ∧ (∃ α, bcPar n α = s) ∧ ∀ α : Fin (n / 2) → ℂ, bcPar n α = s →
    ∀ φ : GU σ n → ℂ, IsSphericalU q α φ → ∀ d, lab d →
      hAct (KU σ n) (fun g : GU σ n => divInd (intL L) d (g : GL (Fin n) L)) φ 1 = c d * φ 1

end Local

section Global

variable {E : Type} [Field E] [NumberField E]

def ParGL (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) : Prop :=
  s.card = n ∧ (0 : ℂ) ∉ s ∧ ∀ α : Fin n → ℂ, Finset.univ.val.map α = s →
    ∀ φ : GL (Fin n) (P.adicCompletion E) → ℂ, IsSpherical E P α φ → ∀ d, lab d →
      hAct (GLint (Fin n) (Ov E P)) (divInd (Ov E P) d) φ 1 = c d * φ 1

variable [StarRing E]

def IsConjAt (P : HeightOneSpectrum (𝓞 E)) (σ : P.adicCompletion E →+* P.adicCompletion E) : Prop :=
  ∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (star x)

def IsPar (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (lab : List ℤ → Prop) (c : List ℤ → ℂ) (s : Multiset ℂ) : Prop :=
  (Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal ≠ P.asIdeal → ParGL P n lab c s) ∧
  (Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = P.asIdeal →
    ∀ (σ : P.adicCompletion E →+* P.adicCompletion E) (ϖ : P.adicCompletion E) (q : ℕ),
      IsConjAt P σ → IsUnramInv ϖ σ q → ParU σ q n lab c s)

end Global

def frobPoly (q n : ℕ) (s : Multiset ℂ) : ℂ[X] :=
  (s.map fun a => X - C (a * (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ))).prod

variable {D : D7}

def Lab (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) : Prop :=
  ∃ R, Hecke₂ V J χ S P d R

def HasGalois (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Formalism.ConjugateSelfDual.Qbar l ≃+* ℂ),
    ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E (AlgebraicClosure D.host.E) →* GL (Fin V.rank) (Formalism.ConjugateSelfDual.Qbar l), Continuous ρ ∧
      ∀ P : HeightOneSpectrum (𝓞 D.host.E), OffS D S P → ((l : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal →
        ∃ s, IsPar P V.rank (Lab V J χ S P) (c P) s ∧
          ∀ (A : ValuationSubring (AlgebraicClosure D.host.E)) (g : Formalism.ConjugateSelfDual.G D.host.E (AlgebraicClosure D.host.E)),
            Formalism.ConjugateSelfDual.IsPlaceOver (F := D.host.E) A P → Formalism.ConjugateSelfDual.IsFrob (F := D.host.E) A (Formalism.ConjugateSelfDual.normV P) g →
              ((ρ g⁻¹ : GL (Fin V.rank) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.ConjugateSelfDual.Qbar l)).charpoly.map
                (ι : Formalism.ConjugateSelfDual.Qbar l →+* ℂ) = frobPoly (Formalism.ConjugateSelfDual.normV P) V.rank s

def RegularWt {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Prop :=
  ∀ τ (a b : Fin V.rank), a < b → M.lam τ b + 2 ≤ M.lam τ a

def GaloisOfRegularForms : Prop :=
  ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ),
    IsInfFam θ → RegularWt M → SphOff J χ Sb → partFull θ M J χ Sb c ≠ ⊥ → HasGalois V J χ Sb c

theorem bcPar_map_inv (n : ℕ) (α : Fin (n / 2) → ℂ) : (bcPar n α).map (·⁻¹) = bcPar n α := by
  simp only [bcPar, Multiset.map_add, Multiset.map_map, Function.comp_def, inv_inv, Multiset.map_replicate, inv_one]
  rw [add_comm (Multiset.map (fun i => (α i)⁻¹) _)]

end GlobalTheory.SphPar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorTranslateRatioGlobalUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT.Hecke.PullInj

noncomputable section
namespace GlobalTheory.UPel.HT.Hecke.PullInj

theorem gen_transl_ratio : ∀ (X X' : Scheme.{0}) (π : X ⟶ X') (Q₁ Q₂ : LB X'), Q₁.IsLB → Q₂.IsLB →
    ∀ (w : LB.Iso (Q₁.pull π) (Q₂.pull π)), w.IsGen → ∀ τ : X ⟶ X, τ ≫ π = π → ∃ f : Γ(X, ⊤)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)),
        r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
        gm (r ≫ τ) z _ (w.s k) = gm r z ⊤ f * gm r z _ (w.s k) := by
  intro X X' π Q₁ Q₂ hQ₁ hQ₂ w hw τ hτ
  have hπτ : ∀ x : X, π (τ x) = π x := fun x => by
    rw [← Scheme.Hom.comp_apply, hτ]
  have hmem : ∀ {x : X} {k : (PUnit → Q₂.ι) × (PUnit → Q₁.ι)},
      x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k → τ x ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k := by
    intro x k hx
    rw [mem_divPull] at hx ⊢
    rw [hπτ]; exact hx
  have hle : ∀ k, (LB.div (Q₂.pull π) (Q₁.pull π)).U k ≤ τ ⁻¹ᵁ (LB.div (Q₂.pull π) (Q₁.pull π)).U k :=
    fun k x hx => hmem hx
  let u : ∀ k, Γ(X, (LB.div (Q₂.pull π) (Q₁.pull π)).U k)ˣ := fun k =>
    res (hle k) (pullU τ _ (w.s k)) * (w.s k)⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k, r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      gm r z _ (u k) = gm (r ≫ τ) z _ (w.s k) * (gm r z _ (w.s k))⁻¹ := by
    intro Z r z k hz
    show gm r z _ (res (hle k) (pullU τ _ (w.s k)) * (w.s k)⁻¹) = _
    rw [map_mul, map_inv, gm_res r z (hle k) hz, gm_pull r τ z _ (hmem hz)]
  have hg : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) k l, r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U k →
      r z ∈ (LB.div (Q₂.pull π) (Q₁.pull π)).U l →
      gm (r ≫ τ) z _ ((LB.div (Q₂.pull π) (Q₁.pull π)).g k l) = gm r z _ ((LB.div (Q₂.pull π) (Q₁.pull π)).g k l) := by
    intro Z r z k l hk hl
    have hk' := hmem hk
    have hl' := hmem hl
    rw [germ_div_g _ _ (r ≫ τ) z hk' hl', germ_div_g _ _ r z hk hl]
    have hk₀ := mem_divPull.1 hk
    have hl₀ := mem_divPull.1 hl
    have hk₁ := mem_divPull.1 hk'
    have hl₁ := mem_divPull.1 hl'
    rw [gm_pull_g Q₂ π (r ≫ τ) z hk₁.1 hl₁.1, gm_pull_g Q₁ π (r ≫ τ) z hk₁.2 hl₁.2,
      gm_pull_g Q₂ π r z hk₀.1 hl₀.1, gm_pull_g Q₁ π r z hk₀.2 hl₀.2, Category.assoc, hτ]
  have hc : (⊤ : X.Opens) ≤ iSup (LB.div (Q₂.pull π) (Q₁.pull π)).U := by
    intro x _
    obtain ⟨i, hi⟩ := exists_chart hQ₂ (π x)
    obtain ⟨j, hj⟩ := exists_chart hQ₁ (π x)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => i, fun _ => j), mem_divPull.2 ⟨hi, hj⟩⟩
  obtain ⟨f, hf⟩ := glue_unit (⊤ : X.Opens) (LB.div (Q₂.pull π) (Q₁.pull π)).U (fun _ => le_top) hc u (by
    intro k l x hx
    rw [hu _ _ _ k hx.1, hu _ _ _ l hx.2, gen_germ hw (𝟙 X ≫ τ) x (hmem hx.1) (hmem hx.2),
      gen_germ hw (𝟙 X) x hx.1 hx.2, hg _ _ _ k l hx.1 hx.2]
    simp only [← div_eq_mul_inv]
    exact mul_div_mul_left_eq_div _ _ _)
  refine ⟨f, fun Z r z k hz => ?_⟩
  rw [← gm_res r z (le_top : (LB.div (Q₂.pull π) (Q₁.pull π)).U k ≤ ⊤) hz f, hf k, hu Z r z k hz,
    inv_mul_cancel_right]

end GlobalTheory.UPel.HT.Hecke.PullInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorsInDualWeylModuleStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generators_in_dual_weyl_module : ∀ (K : Type) [Field K] (n : ℕ) (lam : DomWeight (n + 1)) (sg : DomWeight n), GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Interlace lam sg → GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.EqualLast lam sg → ∀ t : GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.Gen lam sg, GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.piGen K lam sg t ∈ dualWeyl K n n sg.natW ∧ ∃ G : BP K n, bmLift K n (lamN lam) (fun s => lamN lam s - sg.natW s) (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.piGen K lam sg t) G ∧ GlobalTheory.IndefiniteRowSideFullHecke.InterlacingNumerators.phiGen K lam sg t = incl K n G := by
  first | exact @GlobalTheory.BrCompare.LiftGen.piGen_mem_and_lift | exact GlobalTheory.BrCompare.LiftGen.piGen_mem_and_lift | (intros; apply GlobalTheory.BrCompare.LiftGen.piGen_mem_and_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointDvrFactorsValuationSubringClosure
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem geomPoint_factors_valuationSubring_algClosure :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L]
      [IsFractionRing W L] (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp W),
      ∃ (U : ValuationSubring (AlgebraicClosure L)) (j : W →+* U) (h : U →+* k),
        (algebraMap U (AlgebraicClosure L)).comp j = (algebraMap L (AlgebraicClosure L)).comp (algebraMap W L) ∧
          x = spMap h ≫ spMap j := by
  intro W L _ _ _ _ _ _ k _ _ x
  set j' : W →+* AlgebraicClosure L := (algebraMap L (AlgebraicClosure L)).comp (algebraMap W L) with hj'
  have hinj : Function.Injective j' :=
    (algebraMap L (AlgebraicClosure L)).injective.comp (IsFractionRing.injective W L)
  set g : W →+* k := (Spec.preimage x).hom with hg
  obtain ⟨U, hU, h, hh⟩ := GlobalTheory.T.exists_valuationSubring_extending_ringHom W (AlgebraicClosure L) k j' hinj g
  refine ⟨U, j'.codRestrict U.toSubring hU, h, ?_, ?_⟩
  · ext w; rfl
  · have hcomp : h.comp (j'.codRestrict U.toSubring hU) = g := by
      ext w; exact hh w
    have hx : x = Spec.map (Spec.preimage x) := (Spec.map_preimage x).symm
    rw [hx]
    simp only [spMap, Sp]
    rw [← Spec.map_comp]
    congr 1
    ext w
    change g w = h (j'.codRestrict U.toSubring hU w)
    rw [← hcomp]; rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPartLevelFormInfinitePlaceEqClassSum
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory

theorem hv_map_embedding : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G) (v0 : InfinitePlace K) (s : ℕ), BlockHyp B ℓ v0 s → ∀ v : InfinitePlace K, (B.HV ℓ).map v.embedding = ((Nat.card ℓ.P : ℂ)⁻¹) • (((B.vE ℓ).map v.embedding).conjTranspose * B.S.H.map v.embedding * (B.vE ℓ).map v.embedding) := by
  intro K _ _ _ G _ _ Pl0 B ℓ v0 s h v
  have hE : ∀ i j, B.vE ℓ i j ∈ Formalism.DivisionValues.cmMax K :=
    (Formalism.L2.DIV.good_part_hermitian_spec K v0 h.conj B.S h.ok.hrat h.ok.hpos G B.r h.ok.actRat ℓ.X h.irr ℓ.P ℓ.ψ).1
  have hct : ((B.vE ℓ)ᴴ).map v.embedding = ((B.vE ℓ).map v.embedding)ᴴ := by
    ext i j
    simp only [Matrix.map_apply, Matrix.conjTranspose_apply]
    exact hE j i v.embedding
  have hdef : B.HV ℓ = (Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ) := rfl
  rw [hdef, ← hct, ← Matrix.map_mul, ← Matrix.map_mul]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDiagonalSignatureTracelessBasisStatement
section
open NumberField Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_diagonal_signature_traceless_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Ψ : Finset (E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (p0 : Ψ → ℕ) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → G.det ≠ 0 → (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) → (∀ i, (e i).trace = 0 ∧ ∀ u w, ReciprocityTheory.ChartRestriction.G.FD.herm G (e i *ᵥ u) w + ReciprocityTheory.ChartRestriction.G.FD.herm G u (e i *ᵥ w) = 0) → LinearIndependent (maximalRealSubfield E) e → GlobalTheory.SUVol.riemLie Ψ G x = ENNReal.ofReal (Real.sqrt ‖∏ τ : Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖) • GlobalTheory.SUVol.formLie Ψ e := by
  first | exact @GlobalTheory.SUVol.LieMeasFree.riemLie_eq_smul_formLie_of_signs | exact GlobalTheory.SUVol.LieMeasFree.riemLie_eq_smul_formLie_of_signs | (intros; apply GlobalTheory.SUVol.LieMeasFree.riemLie_eq_smul_formLie_of_signs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramRePosDefAdjointPeriod
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

private def reHermBilin {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).re)
    (fun a b c => by simp [hermForm, add_dotProduct])
    (fun r a b => by simp [hermForm, smul_dotProduct])
    (fun a b c => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun r a b => by
      simp only [hermForm, star_smul, star_trivial, Matrix.mulVec_smul, dotProduct_smul]
      simp)

private theorem hermForm_swap' {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, star_star, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hH.apply i j, star_star]
  ring

private theorem form_eq_zero_of_im_span' {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (B : (Fin g → ℂ) → (Fin g → ℂ) → ℂ) (h1 : ∀ z z' w, B (z + z') w = B z w + B z' w)
    (h2 : ∀ (r : ℂ) z w, B (r • z) w = r * B z w) (h3 : ∀ z w w', B z (w + w') = B z w + B z w')
    (h4 : ∀ (r : ℝ) z w, B z (r • w) = r * B z w) (h0 : ∀ z ∈ s, ∀ w ∈ s, (B z w).im = 0) (z w : Fin g → ℂ) :
    B z w = 0 := by
  have hA : ∀ z ∈ s, ∀ w, (B z w).im = 0 := by
    intro z hz w
    have hw : w ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem w hw => exact h0 z hz w hw
    | zero => simpa using congrArg Complex.im (h4 0 z 0)
    | add w w' _ _ e e' => rw [h3, Complex.add_im, e, e', add_zero]
    | smul r w _ e => rw [h4, Complex.im_ofReal_mul, e, mul_zero]
  have hB : ∀ z w, (B z w).im = 0 := by
    intro z w
    have hz : z ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz => exact hA z hz w
    | zero => simpa using congrArg Complex.im (h2 0 0 w)
    | add z z' _ _ e e' => rw [h1, Complex.add_im, e, e', add_zero]
    | smul r z _ e =>
      have : r • z = (r : ℂ) • z := by ext k; simp
      rw [this, h2, Complex.im_ofReal_mul, e, mul_zero]
  apply Complex.ext
  · have := hB (Complex.I • z) w
    rw [h2] at this
    simpa using this
  · simpa using hB z w

private theorem hermForm_adj_of_im_span' {g : ℕ} (s : Set (Fin g → ℂ)) (hs : Submodule.span ℝ s = ⊤)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (A A' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h0 : ∀ z ∈ s, ∀ w ∈ s, (hermForm Hm (A z) w).im = (hermForm Hm z (A' w)).im) (z w : Fin g → ℂ) :
    hermForm Hm (A z) w = hermForm Hm z (A' w) := by
  have hr : ∀ (r : ℝ) (w : Fin g → ℂ), r • w = (r : ℂ) • w := fun r w => by ext k; simp
  have l1 : ∀ z z' w, hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := fun z z' w => by
    simp only [hermForm, add_dotProduct]
  have l2 : ∀ (r : ℂ) z w, hermForm Hm (r • z) w = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, smul_dotProduct, smul_eq_mul]
  have l3 : ∀ z w w', hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := fun z w w' => by
    simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]
  have l4 : ∀ (r : ℝ) z w, hermForm Hm z ((r : ℂ) • w) = r * hermForm Hm z w := fun r z w => by
    simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.star_def,
      Complex.conj_ofReal]
  refine sub_eq_zero.mp (form_eq_zero_of_im_span' s hs
    (fun z w => hermForm Hm (A z) w - hermForm Hm z (A' w)) ?_ ?_ ?_ ?_ ?_ z w)
  · intro z z' w
    simp only [map_add, l1]; ring
  · intro r z w
    simp only [map_smul, l2]; ring
  · intro z w w'
    simp only [map_add, l3]; ring
  · intro r z w
    simp only [hr, map_smul, l4]; ring
  · intro z hz w hw
    simp only [Complex.sub_im, h0 z hz w hw, sub_self]

theorem gram_re_posdef_adj : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ)
    (D : PLat O bar) (P : D.La →+ (Fin g → ℂ)) (r : ℕ) (e : Module.Basis (Fin r) ℤ D.La), IsPeriod D ρ P →
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.IsHermitian ∧ (∀ z : Fin r → ℂ, z ≠ 0 → 0 < (star z ⬝ᵥ (Q *ᵥ z)).re) ∧
      ∀ a : O, Q * actM D e ℂ (bar a) = (actM D e ℂ a)ᴴ * Q := by
  intro O _ bar g ρ D P r e hP
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, hE⟩ := hP
  set B := reHermBilin Hm with hBdef
  have hB : ∀ z w, B z w = (hermForm Hm z w).re := fun _ _ => rfl
  have hind : LinearIndependent ℝ (fun i => P (e i)) := by
    haveI : DiscreteTopology (LinearMap.range P.toIntLinearMap) := hdisc
    haveI : IsZLattice ℝ (LinearMap.range P.toIntLinearMap) := ⟨hspan⟩
    let bL := e.map (LinearEquiv.ofInjective P.toIntLinearMap hinj)
    have hfun : (fun i => P (e i)) = ⇑(bL.ofZLatticeBasis ℝ (LinearMap.range P.toIntLinearMap)) := by
      funext i
      rw [Module.Basis.ofZLatticeBasis_apply, Module.Basis.map_apply]
      rfl
    rw [hfun]
    exact (bL.ofZLatticeBasis ℝ (LinearMap.range P.toIntLinearMap)).linearIndependent
  have hBpos : ∀ v, v ≠ 0 → 0 < B v v := fun v hv => hpos v hv
  have hBnn : ∀ v, 0 ≤ B v v := fun v => by
    by_cases hv : v = 0
    · subst hv; simp
    · exact (hBpos v hv).le
  have hBsymm : ∀ v w, B v w = B w v := fun v w => by
    rw [hB, hB, hermForm_swap' hH v w]; simp
  refine ⟨Matrix.of fun i j => ((B (P (e i)) (P (e j)) : ℝ) : ℂ), ?_, ?_, ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, hBsymm]
  · intro z hz
    have hexp : ∀ x : Fin r → ℝ, B (∑ j, x j • P (e j)) (∑ j, x j • P (e j)) =
        ∑ i, ∑ j, B (P (e i)) (P (e j)) * (x i * x j) := by
      intro x
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hBsymm (P (e j))]
      ring
    have hq : (star z ⬝ᵥ (Matrix.of (fun i j => ((B (P (e i)) (P (e j)) : ℝ) : ℂ)) *ᵥ z)).re =
        ∑ i, ∑ j, B (P (e i)) (P (e j)) * ((z i).re * (z j).re) +
          ∑ i, ∑ j, B (P (e i)) (P (e j)) * ((z i).im * (z j).im) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Complex.re_sum, Finset.mul_sum, Pi.star_apply,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp [Complex.mul_re, Complex.mul_im]
      ring
    rw [hq, ← hexp, ← hexp]
    have hor : (fun i => (z i).re) ≠ 0 ∨ (fun i => (z i).im) ≠ 0 := by
      by_contra h
      push_neg at h
      apply hz
      funext i
      exact Complex.ext (congrFun h.1 i) (congrFun h.2 i)
    rcases hor with h | h
    · have hv : ∑ j, (z j).re • P (e j) ≠ 0 := fun h0 =>
        h (funext fun i => Fintype.linearIndependent_iff.1 hind _ h0 i)
      exact add_pos_of_pos_of_nonneg (hBpos _ hv) (hBnn _)
    · have hv : ∑ j, (z j).im • P (e j) ≠ 0 := fun h0 =>
        h (funext fun i => Fintype.linearIndependent_iff.1 hind _ h0 i)
      exact add_pos_of_nonneg_of_pos (hBnn _) (hBpos _ hv)
  · intro a
    have hadj : ∀ z w, hermForm Hm (ρ a *ᵥ z) w = hermForm Hm z (ρ (bar a) *ᵥ w) :=
      hermForm_adj_of_im_span' (Set.range P) hspan Hm (Matrix.mulVecLin (ρ a)) (Matrix.mulVecLin (ρ (bar a))) (by
        rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
        simp only [Matrix.mulVecLin_apply]
        rw [← hlin, ← hlin, hE, hE, D.adj])
    have hexpand : ∀ v : D.La, P v = ∑ k, e.repr v k • P (e k) := fun v => by
      conv_lhs => rw [← e.sum_repr v]
      simp only [map_sum, map_zsmul]
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, actM, Matrix.conjTranspose_apply, star_intCast]
    have h1 : B (P (e i)) (P (bar a • e j)) = ∑ k, B (P (e i)) (P (e k)) * (e.repr (bar a • e j) k : ℝ) := by
      rw [hexpand (bar a • e j), map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, zsmul_eq_mul, mul_comm]
    have h2 : B (P (a • e i)) (P (e j)) = ∑ k, (e.repr (a • e i) k : ℝ) * B (P (e k)) (P (e j)) := by
      rw [hBsymm, hexpand (a • e i), map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, zsmul_eq_mul, hBsymm]
    have h3 : B (P (e i)) (P (bar a • e j)) = B (P (a • e i)) (P (e j)) := by
      rw [hB, hB, hlin, hlin, hadj]
    have := congrArg (fun t : ℝ => (t : ℂ)) (h1.symm.trans (h3.trans h2))
    push_cast at this
    exact this

end GlobalTheory.PELU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionAtIffKottwitzModuleCondiStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorLieConditionAt_iff_kottwitzModuleCondition : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0})
  (A : Over S) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (R' : Type) [CommRing R'] (β : R →+* R')
  (x : Sp R' ⟶ S),
    LieAt b act β x ↔
      LieMod (ReciprocityTheory.ChartRestriction.G.PullbackSections.actR (x0 := x) (S := R') (act.toF D)) D.ω (β b.ρ) (fun i => β.comp (b.t i)) := by
  first | exact @GlobalTheory.UPel.HT.LieLin.lieAt_iff_lieMod | exact GlobalTheory.UPel.HT.LieLin.lieAt_iff_lieMod | (intros; apply GlobalTheory.UPel.HT.LieLin.lieAt_iff_lieMod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT

theorem objMap_comp : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S₁ S₂ S₃ : Scheme.{0}) (s₁ : S₁ ⟶ Sp R) (s₂ : S₂ ⟶ Sp R) (s₃ : S₃ ⟶ Sp R) (o₁ : Obj b N s₁) (o₂ : Obj b N s₂) (o₃ : Obj b N s₃) (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃), ObjMap o₁ o₂ f → ObjMap o₂ o₃ g → Nonempty (ObjMap o₁ o₃ (f ≫ g)) := by
  intro p _ D R _ b N S₁ S₂ S₃ s₁ s₂ s₃ o₁ o₂ o₃ f g h₁ h₂
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEltInvDivAtSplitLab
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem heckeElt_inv_divAt_splitLab : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → k ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) k α → DivAt V e (ϖ : D.host.E) (splitLab V.rank k) α⁻¹ :=
  fun V P e ϖ k α he hϖ hϖ2 hk hα => GlobalTheory.SplitHeckeLabel.divAt_inv V e P he ϖ hϖ hϖ2 k hk α hα

end GlobalTheory
end

