import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumRangeBlocks
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockDetGe
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMixedProj
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DivisionWithBasisOfDivision
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Formalism.LocalToGlobal.GroupLattices.JointServices.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2070
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2101

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationPreservesAdmissible
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

namespace GlobalTheory.ModelTrUnit

theorem exists_const : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ μ : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖e Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE _hbij μ hμ
  obtain ⟨ei, ev, hei, hev, hpure⟩ := hE.loc
  have hSB : ∀ v : Pl F, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v φ ∈ SB (Fin n × Fin d → Fv F v) := by
    intro v φ hφ
    rw [← (hev v).2]
    exact Submodule.mem_map_of_mem hφ
  have hfin : ∀ v : Pl F, ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (Fin n × Fin d → Fv F v) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
        ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ' ∈ SB (Fin n × Fin d → Fv F v),
          @integral _ ℂ _ _ (borel _) μ (fun x => ev v φ x * starRingEnd ℂ (ev v φ' x)) =
            (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => φ x * starRingEnd ℂ (φ' x)) := by
    intro v
    have h2 : (2 : Fv F v) ≠ 0 := by
      intro h
      apply two_ne_zero (α := F)
      apply (algebraMap F (Fv F v)).injective
      rw [map_ofNat, h, map_zero]
    letI : Invertible (2 : Fv F v) := invertibleOfNonzero h2
    obtain ⟨ψv, hc, hne, A, hA⟩ := GlobalTheory.T.exists_addChar_normalizing_schrodinger_action F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure v
    exact GlobalTheory.T.local_intertwiner_unique_scalar F v (Fin n × Fin d) ψv hc hne (ev v) A (hSB v) hA
  have hinf : ∃ c : ℝ, 0 ≤ c ∧ ∀ μ : @Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) (borel _),
      @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ f f' : SInf F (Fin n × Fin d),
        @integral _ ℂ _ _ (borel _) μ (fun x => ei f x * starRingEnd ℂ (ei f' x)) =
          (c : ℂ) * @integral _ ℂ _ _ (borel _) μ (fun x => f x * starRingEnd ℂ (f' x)) := by
    letI : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
    letI : Invertible (2 : mixedEmbedding.mixedSpace F) :=
      (Invertible.map (algebraMap ℝ (mixedEmbedding.mixedSpace F)) 2).copy 2 (map_ofNat _ 2).symm
    obtain ⟨ψ, hψ, A, hA⟩ := GlobalTheory.T.weil_eigen_continuous_inverse F E σ B n d X W M χX χW om r s r' s' hPair M₁ hM₁ e hE ei ev hei hev hpure
    exact GlobalTheory.T.archimedean_intertwiner_unique hP F (Fin n × Fin d) ψ hψ ei A hA
  exact GlobalTheory.T.restricted_tensor_schwartz F (Fin n × Fin d) e M.vac M₁.vac ei ev (fun v => (hPair.good.vac v).1) hPair.good.std hM₁.std
    (fun v => (hev v).1) hSB hpure hinf hfin μ hμ

end GlobalTheory.ModelTrUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuumConstantTrivialFinitePairs
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacTriv

theorem one_suppSplit {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro q _ _ i j k
  refine ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, ?_⟩
  simp

theorem one_suppInert {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.SuppInert D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro q _ _ i j k
  refine ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, ?_⟩
  simp

theorem one_intG {D : D7} {N : ℕ} : Formalism.MainNotions.StandardLatticesGL3.IntG D (1 : GL (Fin N) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  intro i j
  simp only [inv_one, Units.val_one, Matrix.one_apply]
  split_ifs
  · exact ⟨one_mem _, one_mem _⟩
  · exact ⟨zero_mem _, zero_mem _⟩

theorem vacuum_const_trivial : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
  GlobalTheory.NormSum.Inp D → ∀ t0 : ℂ, Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Even (a * d) → oddE0 D cc δ t0 a d e0 →
  HasFinPart χS W.chV W.ep → HasFinPart χT W.chV' (-W.ep') →
  ∀ f₀ : WO S T → ℂ, Reads ψ θ hS hT cc δ r e0 f₀ →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∃ c : ℂ, Reads ψ θ hS hT cc δ r (c • W.Om x y e0) (om (g, h) f₀)) →
  (∀ (x₁ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₁ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₁ : GA D S) (h₁ : GA D T)
    (x₂ : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y₂ : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g₂ : GA D S) (h₂ : GA D T) (c₁ c₂ : ℂ),
    IsFinPt S g₁ x₁ → IsFinPt T h₁ y₁ → IsFinPt S g₂ x₂ → IsFinPt T h₂ y₂ →
    Reads ψ θ hS hT cc δ r (c₁ • W.Om x₁ y₁ e0) (om (g₁, h₁) f₀) → Reads ψ θ hS hT cc δ r (c₂ • W.Om x₂ y₂ e0) (om (g₂, h₂) f₀) →
    Reads ψ θ hS hT cc δ r ((c₁ * c₂) • W.Om (x₁ * x₂) (y₁ * y₂) e0) (om (g₁ * g₂, h₁ * h₂) f₀)) →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppSplit D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀)) →
  (∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Formalism.MainNotions.StandardLatticesGL3.SuppInert D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.SuppInert D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Formalism.MainNotions.StandardLatticesGL3.IntG D (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) → Formalism.MainNotions.StandardLatticesGL3.IntG D (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀)) →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  Reads ψ θ hS hT cc δ r (W.Om x y e0) (om (g, h) f₀) := by
  intro D ψ θ S T a d hS hT cc δ r hset e0 W χS χT om hW hInp t0 ht0 hev hodd hχS hχT f₀ hf₀ hline hmul hsplit hinert
  subst hS
  subst hT
  have hnz : ∀ x y, W.Om x y e0 ≠ 0 := GlobalTheory.T.weilOperator_normalisingVector_ne_zero cc δ t0 e0 W hset.crv hodd
  have huniq : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T) (c c' : ℂ),
      Reads ψ θ rfl rfl cc δ r (c • W.Om x y e0) (om (g, h) f₀) →
      Reads ψ θ rfl rfl cc δ r (c' • W.Om x y e0) (om (g, h) f₀) → c = c' :=
    fun x y g h c c' h1 h2 => GlobalTheory.T.readsGaussian_smul_const_unique ψ θ S T rfl rfl cc δ r hset _ _ c c' (hnz x y) h1 h2
  have hone : ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T),
      Reads ψ θ rfl rfl cc δ r (W.Om x y e0) (om (g, h) f₀) →
      Reads ψ θ rfl rfl cc δ r ((1 : ℂ) • W.Om x y e0) (om (g, h) f₀) := fun x y g h hr => by rwa [one_smul]
  have p1S : IsFinPt S (1 : GA D S) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) := GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_one S rfl
  have p1T : IsFinPt T (1 : GA D T) (1 : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) := GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_one T rfl
  have exS : ∀ x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank, ∃ g, IsFinPt S g x :=
    fun x => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one S hset.gS x rfl
  have exT : ∀ y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank, ∃ h, IsFinPt T h y :=
    fun y => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one T hset.gT y rfl
  choose gx hgx using exS
  choose hy hhy using exT
  have gx1 : gx 1 = 1 := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same S _ _ 1 (hgx 1) p1S
  have hy1 : hy 1 = 1 := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same T _ _ 1 (hhy 1) p1T
  have gxm : ∀ x₁ x₂, gx x₁ * gx x₂ = gx (x₁ * x₂) :=
    fun x₁ x₂ => GlobalTheory.T.eq_of_isFiniteAdelicPoint_same S _ _ _ (GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_mul S _ _ _ _ (hgx x₁) (hgx x₂)) (hgx (x₁ * x₂))
  have hym : ∀ y₁ y₂, hy y₁ * hy y₂ = hy (y₁ * y₂) :=
    fun y₁ y₂ => GlobalTheory.T.eq_of_isFiniteAdelicPoint_same T _ _ _ (GlobalTheory.T.isFiniteAdelicPointOfUnitaryGroup_mul T _ _ _ _ (hhy y₁) (hhy y₂)) (hhy (y₁ * y₂))
  choose cS hcS using fun x => hline x 1 (gx x) 1 (hgx x) p1T
  choose cT hcT using fun y => hline 1 y 1 (hy y) p1S (hhy y)

  have cS1 : cS 1 = 1 := by
    have h1 := hcS 1
    rw [gx1] at h1
    exact huniq _ _ _ _ _ _ h1 (hone _ _ _ _ (hsplit 1 1 1 1 p1S p1T (by simpa using one_suppSplit) (by simpa using one_suppSplit)))
  have cSm : ∀ x₁ x₂, cS (x₁ * x₂) = cS x₁ * cS x₂ := by
    intro x₁ x₂
    have h1 := hmul x₁ 1 (gx x₁) 1 x₂ 1 (gx x₂) 1 (cS x₁) (cS x₂) (hgx _) p1T (hgx _) p1T (hcS x₁) (hcS x₂)
    rw [mul_one, mul_one, gxm] at h1
    exact huniq _ _ _ _ _ _ (hcS (x₁ * x₂)) h1
  have cT1 : cT 1 = 1 := by
    have h1 := hcT 1
    rw [hy1] at h1
    exact huniq _ _ _ _ _ _ h1 (hone _ _ _ _ (hsplit 1 1 1 1 p1S p1T (by simpa using one_suppSplit) (by simpa using one_suppSplit)))
  have cTm : ∀ y₁ y₂, cT (y₁ * y₂) = cT y₁ * cT y₂ := by
    intro y₁ y₂
    have h1 := hmul 1 y₁ 1 (hy y₁) 1 y₂ 1 (hy y₂) (cT y₁) (cT y₂) p1S (hhy _) p1S (hhy _) (hcT y₁) (hcT y₂)
    rw [mul_one, mul_one, hym] at h1
    exact huniq _ _ _ _ _ _ (hcT (y₁ * y₂)) h1
  let νS : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank →* ℂ := { toFun := cS, map_one' := cS1, map_mul' := cSm }
  let νT : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank →* ℂ := { toFun := cT, map_one' := cT1, map_mul' := cTm }
  have tS : ∀ x, cS x = 1 := by
    intro x
    have := GlobalTheory.T.unitaryAdelicCharacter_eq_one_split_inert S hset.gS νS.toHomUnits
      (fun k hk => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcS k) (hone _ _ _ _ (hsplit k 1 (gx k) 1 (hgx k) p1T hk (by simpa using one_suppSplit)))))
      (fun k hk hki => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcS k) (hone _ _ _ _ (hinert k 1 (gx k) 1 (hgx k) p1T hk (by simpa using one_suppInert)
          hki (by simpa using one_intG))))) x
    have := congrArg Units.val this
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this
  have tT : ∀ y, cT y = 1 := by
    intro y
    have := GlobalTheory.T.unitaryAdelicCharacter_eq_one_split_inert T hset.gT νT.toHomUnits
      (fun k hk => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcT k) (hone _ _ _ _ (hsplit 1 k 1 (hy k) p1S (hhy k) (by simpa using one_suppSplit) hk))))
      (fun k hk hki => Units.ext (by
        rw [MonoidHom.coe_toHomUnits, Units.val_one]
        exact huniq _ _ _ _ _ _ (hcT k) (hone _ _ _ _ (hinert 1 k 1 (hy k) p1S (hhy k) (by simpa using one_suppInert) hk
          (by simpa using one_intG) hki)))) y
    have := congrArg Units.val this
    rwa [MonoidHom.coe_toHomUnits, Units.val_one] at this
  intro x y g h hg hh
  have eg : g = gx x := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same S _ _ x hg (hgx x)
  have eh : h = hy y := GlobalTheory.T.eq_of_isFiniteAdelicPoint_same T _ _ y hh (hhy y)
  subst eg eh
  have h1 := hmul x 1 (gx x) 1 1 y 1 (hy y) (cS x) (cT y) (hgx x) p1T p1S (hhy y) (hcS x) (hcT y)
  rw [tS, tT] at h1
  simp only [mul_one, one_mul, one_smul] at h1
  exact h1

end GlobalTheory.VacTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNotMemPrimeAwayFromMu
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)

namespace GlobalTheory.ThmAUpper

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.ChiGrid in

theorem qn_not_mem : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ)
    (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → ∀ w : HeightOneSpectrum (𝓞 D.what₂.LL), p.R.mu w ≠ p.P.A3.A.μ0 →
      ((Qn d.G (p.R.mu w) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
  intro D L hT Gi Gl Kc Y cX ex Csz p CF d _ hfit w hw
  classical
  obtain ⟨htw, hxi⟩ := xiH_twisted p w hw
  have hl : D.ntw.l (ex.nch.twI (D.plEq.symm w)) = D.what₂.places.resChar (D.plEq.symm w) :=
    (hfit.1.setting.1 _ htw).1
  have hQ := hfit.1.cond _ htw
  have hlev := p.charW.base.lev
  have key : ∀ PP ∈ twPl d.G (p.R.mu w),
      ((D.what₂.places.resChar (D.plEq.symm w) : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro PP hPP hlP
    simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hPP
    obtain ⟨hloc, hW0⟩ := hPP
    have hQt : PP ∈ p.R.toRealDat.toLevCh.Q (p.R.mu w) := hloc.resolve_left hW0
    have hS1 : PP.under (𝓞 D.host.F) ∉ S1 D := fun h => hW0 (by
      rw [d.G.pl.w_Q _ PP hQt h]
      exact Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem h))
    have hram : ¬ (p.R.toRealDat.toLevCh.xiH (p.R.mu w)).UnrAt PP := (hlev.Q_ram _ PP).2 (Or.inl hQt)
    rw [hxi] at hram
    by_cases hd : (p.R.C.delAt (D.what₂.places.resChar (D.plEq.symm w))).UnrAt PP
    · have hψ : ¬ (p.Tp.psi (D.plEq.symm w)).UnrAt PP := fun h => hram (hd.mul h)
      have hmem : PP ∈ ex.nch.Q (D.plEq.symm w) := by
        by_contra hn
        exact hψ (((p.Tp.psi_is _ htw).ram PP).2 hn)
      have hS0 : PP ∈ D.ntw.S0 (ex.nch.twI (D.plEq.symm w)) := D.ntw.twistExcludedPlaces_contains_residueChar _ (by rw [hl]; exact hlP)
      exact Finset.disjoint_left.1 hQ.2.1 hmem hS0
    · have hover : ((D.host.pde : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∨ ((D.host.pde' : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
        unfold Formalism.L2.Host.CharFrame.delAt at hd
        split_ifs at hd
        · by_contra h
          exact hd (p.R.C.isDel'.unr PP fun h' => h (Or.inr h'))
        · by_contra h
          exact hd (p.R.C.isDel.unr PP fun h' => h (Or.inl h'))
      apply hS1
      rw [S1_mem_OmF]
      rcases hover with h | h
      · right; right; left
        show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
        simpa using h
      · right; right; right
        show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
        simpa using h
  intro hmem
  rw [Qn, Nat.cast_prod] at hmem
  obtain ⟨PP, hPP, hin⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hmem
  have : NeZero PP.asIdeal := ⟨PP.ne_bot⟩
  have hq : (Ideal.absNorm (PP.asIdeal.under ℤ)).Prime := Nat.absNorm_under_prime PP.asIdeal
  have : PP.asIdeal.LiesOver (Ideal.span {((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : ℤ)}) :=
    Int.liesOver_span_absNorm PP.asIdeal
  rw [Ideal.absNorm_eq_pow_inertiaDeg' PP.asIdeal hq, Nat.cast_pow] at hin
  have hqw := w.isPrime.mem_of_pow_mem _ hin
  have hqP : ((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have h : algebraMap ℤ (𝓞 D.host.E) ((Ideal.absNorm (PP.asIdeal.under ℤ) : ℕ) : ℤ) ∈ PP.asIdeal :=
      Ideal.absNorm_mem (PP.asIdeal.under ℤ)
    rw [eq_intCast, Int.cast_natCast] at h
    exact h
  have e := resChar_eq (D.plEq.symm w) hq (by rw [Equiv.apply_symm_apply]; exact hqw)
  exact key PP hPP (e ▸ hqP)

end GlobalTheory.ThmAUpper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitInterpolationDetWeightFreeBallIndefinite
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.OrbitInterpWeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem blockConst_deMul {r : ℕ} (X : Data E r) (s : ℕ) : GlobalTheory.Up.BlockConst X (deMul X.Ψ r X.p0 s) :=
  fun _ _ _ h => if_congr h rfl rfl

theorem gapsPairing_deMul {r : ℕ} (X : Data E r) (h0 : 0 < X.p0) (h1 : X.p0 < r) {s : ℕ} (hs : Even s) :
    GlobalTheory.IndefiniteRowSideFullHecke.SpanSubtraction.GapsPairing X (deMul X.Ψ r X.p0 s - kapW X) ((s : ℝ) - 2 * r + 2) := by
  obtain ⟨k, rfl⟩ := hs
  have hk : (k + k) / 2 = k := by omega
  intro τ
  refine ⟨fun i j hj hp => ?_, fun i0 i1 h0' h1' => ?_⟩
  · have e : ((j : ℕ) < X.p0 ↔ (i : ℕ) < X.p0) := by omega
    have hj' : ((j : ℕ) : ℤ) = (i : ℕ) + 1 := by exact_mod_cast hj
    simp only [Pi.sub_apply, deMul, kapW, hj']
    by_cases hi : (i : ℕ) < X.p0
    · rw [if_pos (e.2 hi), if_pos hi]; omega
    · rw [if_neg (mt e.1 hi), if_neg hi]; omega
  · simp only [Pi.sub_apply, deMul, kapW, h0', h1', hk]
    rw [if_pos h0, if_neg (by omega)]
    have hr : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by omega
    rw [hr]
    push_cast
    linarith

theorem large : ∀ (r : ℕ) (X : Data E r) (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r), IsOrth X x0 →
    GlobalTheory.Up.FreeBall X G x0 (1 / (49 * (r : ℝ) ^ 2)) → 0 < X.p0 → X.p0 < r → 4 ≤ X.p0 * (r - X.p0) →
    ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * (X.Ψ.card * (X.p0 * (r - X.p0))) + 1 ≤ s →
    ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x0 ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → P (lact γ x0) = 0 := by
  intro r X G x0 hx0 hFB h0 h1 hq s hs hsb
  have hd : 1 ≤ GlobalTheory.Up.dimX X := (GlobalTheory.Up.one_le_dimX_iff X).2 ⟨h0, h1⟩
  have hD : GlobalTheory.Up.dimX X = X.Ψ.card * (X.p0 * (r - X.p0)) := rfl
  have hOI := GlobalTheory.Up.OrbitInterpolation.orbitInterp (E := E) ⟨normFactor_rightBorel_holds, normFactor_leftAction_holds, pointwiseNorm_invariance_holds⟩
    poin_holds extFStatement_holds measInv_holds
    GlobalTheory.PoleExistence.poleEx_holds (GlobalTheory.PoleDbar.poleSolve measInv_holds)
    GlobalTheory.Up.polePoint_holds
  have hc : 0 < X.Ψ.card := by
    rcases Nat.eq_zero_or_pos X.Ψ.card with h | h
    · rw [hD, h, zero_mul] at hd; omega
    · exact h
  obtain ⟨τ, hτ⟩ := Finset.card_pos.1 hc
  have hr : (0 : ℝ) < r := by exact_mod_cast (h0.trans h1)
  have hρ : (0 : ℝ) < 1 / (49 * (r : ℝ) ^ 2) := by positivity
  have hDq : (4 : ℝ) * X.Ψ.card ≤ GlobalTheory.Up.dimX X := by
    rw [hD, Nat.cast_mul]
    have : (4 : ℝ) ≤ ((X.p0 * (r - X.p0) : ℕ) : ℝ) := by exact_mod_cast hq
    nlinarith [(Nat.cast_nonneg (α := ℝ) X.Ψ.card)]
  have hsR : 2 * (r : ℝ) + 50 * (r : ℝ) ^ 2 * (GlobalTheory.Up.dimX X : ℝ) + 1 ≤ s := by
    rw [hD]; exact_mod_cast hsb
  have hq1 : (GlobalTheory.Up.dimX X : ℝ) / (1 / (49 * (r : ℝ) ^ 2)) = 49 * (r : ℝ) ^ 2 * GlobalTheory.Up.dimX X := by
    field_simp
  have hcurv := (GlobalTheory.DivisionVolume.margin_iff h0 h1 (deMul X.Ψ r X.p0 s) ((s : ℝ) - 2 * r + 2)).2
    (gapsPairing_deMul X h0 h1 hs) x0 hx0
  have hs2 : 1 ≤ s / 2 := by obtain ⟨k, rfl⟩ := hs; omega
  refine hOI r X G x0 _ _ (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) ((s : ℝ) - 2 * r + 2)
    (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X) hx0 hd hρ hFB (blockConst_deMul X s) (by linarith)
    (by rw [hq1]; nlinarith [sq_nonneg (r : ℝ)]) hcurv ?_
  refine cuspStatement_holds r X _ ⟨τ, hτ⟩ h0 h1 (fun i j hj hp => ?_) (fun i0 i1 h0' h1' => ?_)
  · have e : ((j : ℕ) < X.p0 ↔ (i : ℕ) < X.p0) := by omega
    simp only [deMul]
    by_cases hi : (i : ℕ) < X.p0
    · rw [if_pos (e.2 hi), if_pos hi]
    · rw [if_neg (mt e.1 hi), if_neg hi]
  · simp only [deMul]
    rw [if_pos (by omega), if_neg (by omega)]
    omega

theorem orbit_interp_deMul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ la, ∀ γ ∈ X.Γ, X.χ la γ = 1) → ∀ (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r), IsOrth X x0 →
    GlobalTheory.Up.FreeBall X G x0 (1 / (49 * (r : ℝ) ^ 2)) → 0 < X.p0 → X.p0 < r → ∀ s : ℕ, Even s →
    2 * r + 50 * r ^ 2 * (X.Ψ.card * (X.p0 * (r - X.p0))) + 1 ≤ s →
    ∃ P ∈ X.SS (deMul X.Ψ r X.p0 s), P x0 ≠ 0 ∧ ∀ γ ∈ G, γ ∉ X.Γ → P (lact γ x0) = 0 := by
  intro E _ _ _ r X hχ G x0 hx0 hFB h0 h1 s hs hsb
  by_cases hq : 4 ≤ X.p0 * (r - X.p0)
  · exact large r X G x0 hx0 hFB h0 h1 hq s hs hsb
  · exact GlobalTheory.T.freeBallCentre_interpolation_detWeight_smallSignature E r X hχ G x0 hx0 hFB h0 h1 (by omega) s hs hsb

end GlobalTheory.OrbitInterpWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OwnPrimeIsUnitAtPlace
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.BigOn.Exp.SerBase

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem natPrime_notMem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q.Prime)
    (hne : q ≠ Formalism.EigenvalueLevelCeiling.plc v) : (q : 𝓞 K) ∉ v.asIdeal := by
  intro hmem
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hmem
  have hdvd : Formalism.EigenvalueLevelCeiling.plc v ∣ q := (ringChar.spec (𝓞 K ⧸ v.asIdeal) q).1 hmem
  exact hne ((Nat.prime_dvd_prime_iff_eq (Formalism.L2.DIV.plc_prime' v) hq).1 hdvd).symm

theorem ownAt_prime_ne (D : D7) (w : D.what₂.places.Pl) :
    (ownAt D (D.plEq w)).Prime ∧ ownAt D (D.plEq w) ≠ Formalism.EigenvalueLevelCeiling.plc (D.plEq w) := by
  unfold ownAt
  split_ifs with h
  · exact ⟨D.host.pde'_prime, fun e => D.host.pde_ne (h.symm.trans e.symm)⟩
  · exact ⟨D.host.pde_prime, fun e => h e.symm⟩

theorem ownUnit : OwnUnit := by
  intro D c w
  obtain ⟨hq, hne⟩ := ownAt_prime_ne D w
  set q := ownAt D (D.plEq w) with hqdef
  have hnot := natPrime_notMem (D.plEq w) hq hne
  have hv : (D.plEq w).valuation D.what₂.LL (q : D.what₂.LL) = 1 := by
    have := ((D.plEq w).valuation_eq_one_iff_notMem (K := D.what₂.LL)).2 hnot
    simpa using this
  have hq0 : (q : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hnn : (0 : WithTop ℤ) ≤ D.what₂.places.val w (q : D.what₂.LL)⁻¹ :=
    (D.val_nonneg_iff w _).2 (by rw [map_inv₀, hv, inv_one])
  obtain ⟨y, hy⟩ := (c.embW_w w _).1 hnn
  rw [map_inv₀, map_natCast] at hy
  have hqF : ((q : ℕ) : FractionRing (c.Oe w)) ≠ 0 := by
    have := (map_ne_zero (c.embW w)).2 hq0
    rwa [map_natCast] at this
  have h1 : algebraMap (c.Oe w) (FractionRing (c.Oe w)) (y * (q : c.Oe w)) = 1 := by
    rw [map_mul, hy, map_natCast]
    exact inv_mul_cancel₀ hqF
  have h2 : y * (q : c.Oe w) = 1 := by
    apply IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w))
    rw [h1, map_one]
  exact (Units.mkOfMulEqOne (q : c.Oe w) y (by rw [mul_comm]; exact h2)).isUnit

end GlobalTheory.BigOn.Exp.SerBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterHypothesisAllPointsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_hypothesis_all_points : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, (GlobalTheory.ExpTie.parOf (Fm.L x i) j).Hyp := by
  first | exact @GlobalTheory.ExpTie.parOf_hyp | exact GlobalTheory.ExpTie.parOf_hyp | (intros; apply GlobalTheory.ExpTie.parOf_hyp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterLargeAllPointsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parameter_large_all_points : GlobalTheory.BigOn.AtPts fun Fm x _ i _ => ∀ j : Fin (Fm.D x i).R.m, ∃ X' A : ℝ, Formalism.CohomologicalDescent.LargeParameterEstimates.Rows (GlobalTheory.ExpTie.parOf (Fm.L x i) j) X' A ∧ Formalism.CohomologicalDescent.LargeParameterEstimates.Big (GlobalTheory.ExpTie.parOf (Fm.L x i) j).L (GlobalTheory.ExpTie.parOf (Fm.L x i) j).x X' A := by
  first | exact @GlobalTheory.ExpTie.rows_big | exact GlobalTheory.ExpTie.rows_big | (intros; apply GlobalTheory.ExpTie.rows_big <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialCHolInvariantMemNonZeroDivisorsStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomialC_holInvariant_mem_nonZeroDivisors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (D : HA M), (∀ c, ∃ x : M.dom, (D : C → M.dom → ℂ) c x ≠ 0) → Polynomial.C D ∈ nonZeroDivisors (Polynomial (HA M)) := by
  first | exact @GlobalTheory.CuspEmb.C_mem_nonZeroDivisors | exact GlobalTheory.CuspEmb.C_mem_nonZeroDivisors | (intros; apply GlobalTheory.CuspEmb.C_mem_nonZeroDivisors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeOverTypePrimeFixedPlaceOrConjStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_over_typePrime_fixedPlace_or_conj : ∀ (D : D7) (k : Fin 2) (P : Ideal (𝓞 D.host.E)), P.IsPrime → ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P →
    ∃ v : D.nd.PlG k, P = (D.naut.plGw k v).asIdeal ∨
      P = (D.naut.plGw k v).asIdeal.map
        ((RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E) :
          𝓞 D.host.E →+* 𝓞 D.host.E) := by
  first | exact @GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj | exact GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj | (intros; apply GlobalTheory.TypePrimesOnto.prime_eq_plGw_or_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadInjectiveStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ReadInjective : GlobalTheory.BigOn.Exp.ReadInj := by
  first | exact @GlobalTheory.BigOn.Exp.readInj | exact GlobalTheory.BigOn.Exp.readInj | (intros; apply GlobalTheory.BigOn.Exp.readInj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetAtOfSizeAtStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.set_at_of_size_at : GlobalTheory.BigTop.Fun.SizeAt → GlobalTheory.BigTop.Fun.SetAt := by
  first | exact @GlobalTheory.BigTop.Fun.setAt_of_sizeAt | exact GlobalTheory.BigTop.Fun.setAt_of_sizeAt | (intros; apply GlobalTheory.BigTop.Fun.setAt_of_sizeAt <;> assumption)
end

