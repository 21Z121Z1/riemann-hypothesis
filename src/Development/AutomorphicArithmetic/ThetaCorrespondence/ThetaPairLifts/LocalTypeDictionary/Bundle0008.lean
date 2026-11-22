import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0573
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0670
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0683
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0561
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsLinearFunctionalAtSplitPlace
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny
open GlobalTheory.ThK GlobalTheory.KSplit
noncomputable section
namespace GlobalTheory.LinWSplit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.LinWSplit
namespace GlobalTheory.LinWSplit
theorem exists_linearFunctional_at_split_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∃ ι, M.IsLinW B.ψ t b c ι := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c
  have hcm : IsCMExt F E σ := hP.base.cm
  have hstd := hP.base.std
  have hX := hP.herm.herm
  have hY := hP.skew.skew
  obtain ⟨w0⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdX : X.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.herm.sig w0)
    have e : (X.J.map (B.emb w0).1).det = (B.emb w0).1 X.J.det := (RingHom.map_det _ _).symm
    rw [e, h0, map_zero]
  have hdW : W.J.det ≠ 0 := by
    intro h0
    apply GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (hP.skew.sig w0)
    have e : (W.J.map (B.emb w0).1).det = (B.emb w0).1 W.J.det := (RingHom.map_det _ _).symm
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero]
  have hA : IsUnit (X.J.map t).det := by
    rw [show (X.J.map t).det = (t : E →+* Fv F v) X.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdX ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB : IsUnit (W.J.map t)ᵀ.det := by
    rw [Matrix.det_transpose, show (W.J.map t).det = (t : E →+* Fv F v) W.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdW ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  choose U hUat hU0 hU1 using fun (P₀ P₁ : Matrix (Fin n) (Fin d) (Fv F v)) => GlobalTheory.T.exists_splitPlace_adelicMatrix_given_components hcm v t P₀ P₁
  have hat_add : ∀ x y : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x → At (evFin F v) y →
      At (evFin F v) (x + y) := fun x y hx hy r hr => by rw [smul_add, hx r hr, hy r hr, add_zero]
  have heq := fun (u u' : Matrix (Fin n) (Fin d) (AE F E)) => locCo_eq_of hcm X W hX hY M t u u'
  let P0 : Matrix (Fin n) (Fin d) (Fv F v) → Matrix (Fin n) (Fin d) (Fv F v) := fun Y => b.1 * Y * c.1ᵀ
  let Q : Matrix (Fin n) (Fin d) (Fv F v) → Matrix (Fin n) (Fin d) (Fv F v) :=
    fun z => -((X.J.map t)⁻¹ * (b⁻¹).1ᵀ * z * (c⁻¹).1 * ((W.J.map t)ᵀ)⁻¹)
  have hP0 : ∀ P, P0 ((b⁻¹).1 * P * (c⁻¹).1ᵀ) = P := by
    intro P
    simp only [P0, ← Matrix.mul_assoc]
    rw [show b.1 * (b⁻¹).1 = 1 by simp, Matrix.one_mul, Matrix.mul_assoc,
      show (c⁻¹).1ᵀ * c.1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.mul_one]
  have hQ : ∀ P, Q (-(b.1ᵀ * X.J.map t * P * (W.J.map t)ᵀ * c.1)) = P := by
    intro P
    simp only [Q, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((b⁻¹).1ᵀ), show (b⁻¹).1ᵀ * b.1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp,
      Matrix.one_mul, ← Matrix.mul_assoc (c.1), show c.1 * (c⁻¹).1 = 1 by simp, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hB, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hA]
  have hcoX0 : ∀ Y, GlobalTheory.FlipMatch.coX t b c (U (P0 Y) 0) = Y := by
    intro Y
    simp only [GlobalTheory.FlipMatch.coX, hU0, P0, ← Matrix.mul_assoc]
    rw [show (b⁻¹).1 * b.1 = 1 by simp, Matrix.one_mul, Matrix.mul_assoc,
      show c.1ᵀ * (c⁻¹).1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.mul_one]
  have hcoY1 : ∀ z, GlobalTheory.FlipMatch.coY σ X W t b c (U 0 (Q z)) = z := by
    intro z
    simp only [GlobalTheory.FlipMatch.coY, hU1, Q, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA, Matrix.nonsing_inv_mul_cancel_left _ _ hB,
      ← Matrix.mul_assoc (b.1ᵀ), show b.1ᵀ * (b⁻¹).1ᵀ = 1 by rw [← Matrix.transpose_mul]; simp, Matrix.one_mul,
      show (c⁻¹).1 * c.1 = 1 by simp, Matrix.mul_one]
  have hcoY0 : ∀ P, GlobalTheory.FlipMatch.coY σ X W t b c (U P 0) = 0 := by
    intro P; simp [GlobalTheory.FlipMatch.coY, hU1]
  have hcoX1 : ∀ P, GlobalTheory.FlipMatch.coX t b c (U 0 P) = 0 := by
    intro P; simp [GlobalTheory.FlipMatch.coX, hU0]
  have hU00 : GlobalTheory.LatVac.locCo M.co v (U 0 0) = 0 :=
    locCo_eq_zero hcm X W hX hY M t _ (hUat 0 0) (hU0 0 0) (hU1 0 0)
  have hadd0 : ∀ P P', GlobalTheory.LatVac.locCo M.co v (U (P + P') 0) =
      GlobalTheory.LatVac.locCo M.co v (U P 0) + GlobalTheory.LatVac.locCo M.co v (U P' 0) := by
    intro P P'
    rw [← map_add]
    apply heq _ _ (hUat _ _) (hat_add _ _ (hUat _ _) (hUat _ _))
    · rw [Matrix.map_add _ (map_add _), hU0, hU0, hU0]
    · rw [Matrix.map_add _ (map_add _), hU1, hU1, hU1, add_zero]
  have hadd1 : ∀ P P', GlobalTheory.LatVac.locCo M.co v (U 0 (P + P')) =
      GlobalTheory.LatVac.locCo M.co v (U 0 P) + GlobalTheory.LatVac.locCo M.co v (U 0 P') := by
    intro P P'
    rw [← map_add]
    apply heq _ _ (hUat _ _) (hat_add _ _ (hUat _ _) (hUat _ _))
    · rw [Matrix.map_add _ (map_add _), hU0, hU0, hU0, add_zero]
    · rw [Matrix.map_add _ (map_add _), hU1, hU1, hU1]
  let wT : Matrix (Fin n) (Fin d) (Fv F v) →+ (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun Y => GlobalTheory.LatVac.locCo M.co v (U (P0 Y) 0)
      map_zero' := by
        show GlobalTheory.LatVac.locCo M.co v (U (b.1 * 0 * c.1ᵀ) 0) = 0
        rw [Matrix.mul_zero, Matrix.zero_mul]; exact hU00
      map_add' := fun Y Y' => by
        show GlobalTheory.LatVac.locCo M.co v (U (b.1 * (Y + Y') * c.1ᵀ) 0) = _
        rw [Matrix.mul_add, Matrix.add_mul]; exact hadd0 _ _ }
  let wM : Matrix (Fin n) (Fin d) (Fv F v) →+ (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun z => GlobalTheory.LatVac.locCo M.co v (U 0 (Q z))
      map_zero' := by
        show GlobalTheory.LatVac.locCo M.co v (U 0 (Q 0)) = 0
        have : Q 0 = 0 := by simp [Q]
        rw [this]; exact hU00
      map_add' := fun z z' => by
        show GlobalTheory.LatVac.locCo M.co v (U 0 (Q (z + z'))) = _
        have : Q (z + z') = Q z + Q z' := by simp only [Q, Matrix.mul_add, Matrix.add_mul, neg_add]
        rw [this]; exact hadd1 _ _ }
  have hwT : ∀ Y, wT Y = GlobalTheory.LatVac.locCo M.co v (U (P0 Y) 0) := fun _ => rfl
  have hwM : ∀ z, wM z = GlobalTheory.LatVac.locCo M.co v (U 0 (Q z)) := fun _ => rfl
  have hform := fun (x u : Matrix (Fin n) (Fin d) (AE F E)) (hx : At (evFin F v) x) =>
    (locCo_form M.co v x u).trans (evFin_symp hcm X W hX hY t b c x u hx)
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F _).injective
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hstd.1 v
  have hψne : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hstd v
  obtain ⟨ι, hbij, htr, hmu⟩ := GlobalTheory.T.stoneVonNeumann_schwartzBruhat_anyCharacter (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψne wT wM
    (fun Y Y' => by
      rw [hwT, hwT, hform _ _ (hUat _ _), hcoX0, hcoX0, hcoY0, hcoY0]
      simp [GlobalTheory.FlipMatch.pairM])
    (fun z z' => by
      rw [hwM, hwM, hform _ _ (hUat _ _), hcoX1, hcoX1, hcoY1, hcoY1]
      simp [GlobalTheory.FlipMatch.pairM])
    (fun Y z => by
      rw [hwT, hwM, hform _ _ (hUat _ _), hcoX0, hcoX1, hcoY0, hcoY1]
      simp [GlobalTheory.FlipMatch.pairM])
    (fun w => by
      obtain ⟨u, hu, rfl⟩ := locCo_surj M.co v w
      refine ⟨GlobalTheory.FlipMatch.coX t b c u, GlobalTheory.FlipMatch.coY σ X W t b c u, ?_⟩
      rw [hwT, hwM, ← map_add]
      apply heq _ _ (hat_add _ _ (hUat _ _) (hUat _ _)) hu
      · rw [Matrix.map_add _ (map_add _), hU0, hU0, add_zero]
        exact hP0 _
      · rw [Matrix.map_add _ (map_add _), hU1, hU1, zero_add]
        exact hQ _)
  have hφ₁ : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) u →
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ₁, Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ →
        φ₁ = GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v u) φ :=
    fun u hu φ hφ φ₁ hact => GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr =>
      (hact r hr).symm.trans (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ r hr)
  refine ⟨ι, hbij, ?_, ?_⟩
  · intro u hu hu0 φ hφ φ₁ _ hact Y
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    have e2 : GlobalTheory.LatVac.locCo M.co v u = wT (GlobalTheory.FlipMatch.coX t b c u) := by
      rw [hwT]
      apply heq _ _ hu (hUat _ _)
      · rw [hU0]; exact (hP0 _).symm
      · rw [hU1]; exact hu0
    rw [e1, e2]
    exact congrFun (htr _ φ hφ) Y
  · intro u hu hu1 φ hφ φ₁ _ hact x hx hx0
    have e1 := hφ₁ u hu φ hφ φ₁ hact
    have e2 : GlobalTheory.LatVac.locCo M.co v u = wM (GlobalTheory.FlipMatch.coY σ X W t b c u) := by
      rw [hwM]
      apply heq _ _ hu (hUat _ _)
      · rw [hU0]; exact hu1
      · rw [hU1]; exact (hQ _).symm
    have hcx : GlobalTheory.FlipMatch.coY σ X W t b c x = 0 := by simp [GlobalTheory.FlipMatch.coY, hx0]
    rw [e1, e2, congrFun (hmu _ φ hφ), GlobalTheory.VacIndic.psi_of_at B.ψ (at_symp σ _ _ x u hx),
      evFin_symp hcm X W hX hY t b c x u hx, hcx, ← GlobalTheory.LatVac.psiAt_apply]
    simp [GlobalTheory.FlipMatch.pairM, GlobalTheory.FlipMatch.coX]
end GlobalTheory.LinWSplit
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_linearFunctional_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∃ ι, M.IsLinW B.ψ t b c ι := by
  first | exact @_root_.GlobalTheory.LinWSplit.exists_linearFunctional_at_split_place | exact _root_.GlobalTheory.LinWSplit.exists_linearFunctional_at_split_place | (intros; apply _root_.GlobalTheory.LinWSplit.exists_linearFunctional_at_split_place <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsRealCharacterOfBottom
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
open scoped ComplexOrder Kronecker Matrix
namespace GlobalTheory.BottomRealChar
open GlobalTheory.Grid (neg sgn ofSgn)
theorem exists_real_character_of_bottom : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ → IsBottomTri W i j X → ∃ χ : GinfC A →* ℂ, Continuous χ ∧ (∀ (t : T) (g : GinfC A), (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g.1, 1) (X.f t) = χ g • X.f t) ∧ ∀ g : GinfC A, (∀ τ a b, IsAlgebraic ℚ (compAt W.θ τ (Formalism.L2.Theta.mt A g.1) a b)) → IsAlgebraic ℚ (χ g) := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ hL hX
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hW := fun t => hI.weil t
  have hxi : ∀ t τ, HasInfExp D (L.xi t) τ 0 := fun t τ => by
    obtain ⟨n, hn, ho⟩ := hL.xi_fin t
    exact GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ (hL.xi t) hn ho τ
  choose b hb using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D W.θ _ WW.rank τ hθ (hW μ₀).hecT (hW μ₀).resT
  have hbt : ∀ t τ, HasInfExp D ((G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2))) τ (b τ) := by
    intro t τ
    have hrel : (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) / (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) =
        (G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) / (L.mu μ₀ (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2)) *
          (L.xi μ₀ * (L.xi t)⁻¹) := by
      simp only [LevCh.mu, Lift.tup]
      exact commGroup_div_eq_div_mul_ratio _ _ _ _ _
    rw [hrel]
    have := GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hb τ)
      (GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hxi μ₀ τ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hxi t τ)))
    simpa using this
  choose k hk using fun τ => GlobalTheory.SplitParity.exists_int_add_half D _ WW.rank τ (b τ) (hW μ₀).hecT (hW μ₀).resT (hb τ)
  refine ⟨detChar W.θ A fun τ => -(k τ - WW.rank), continuous_detChar hθ _ _, fun t g => ?_,
    fun g hg => isAlgebraic_detChar _ _ _ g hg⟩
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hf : IsThetaFunO W.ψ (neg A) WW (X.f t) := by
    have hne : X.ideal (locPl G) t ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
    obtain ⟨f, h1, h2⟩ := GlobalTheory.Adopt.first_standard_pair_member_has_theta_function D W.ψ W.θ A WW X.rA X.rW _ _ _ _ _ hI.rigA hI.rigW (hI.weil' t).hecT
      (hI.idem t) hne hI.isVac
    obtain ⟨Tm, hT⟩ := h1.1
    exact ((hI.fst t).2 Tm hT).trans (h1.2 Tm hT).symm ▸ h2
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hfock : ∀ τ, IsFockVacAt (heisO W.ψ (neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst t)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  have cS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hdet : ∀ τ, (gramAt D (neg A) τ).det ≠ 0 := fun τ h0 => by
    have := (cS τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  have hg' : (ofSgn true A).symm g.1 ∈ GinfC (neg A) :=
    (GlobalTheory.SgnIdent.mem_GinfC_sgn true A _).2 (by rw [MulEquiv.apply_symm_apply]; exact g.2)
  have hmt : Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm g.1) = Formalism.L2.Theta.mt A g.1 := by
    rw [← GlobalTheory.Grid.mt_ofSgn, MulEquiv.apply_symm_apply]
  obtain ⟨x, hx, hxv⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (neg A) hdet _ hg'
  have hy1 : IsDetRoot WW 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.StdUnn.CartanMove.compAt_mt_one W.θ τ WW
  rw [GlobalTheory.WeilVacChar.vacuum_character D W.ψ hψ (neg A) WW W.θ hθ _ _ _ η hη (hW t) (fun τ => -X.rA.s τ) X.rW.s cS cT
      _ hg' 1 (one_mem _) (fun τ => by rw [hsA, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy1 (X.f t) hf hfock]
  congr 1
  have hx' : ∀ τ, HasInfExp D (((G.ch.chi (D.R.m - ↑i) * L.eta ^ (rankV D ↑i ↑j % 2)) /
      (L.mu t (↑j + 1) * L.eta ^ (rankV D ↑i ↑j % 2))) * (η ^ WW.rank)⁻¹) τ ((k τ - WW.rank : ℤ) : ℚ) := fun τ => by
    have e : ((k τ - WW.rank : ℤ) : ℚ) = b τ - (WW.rank : ℚ) / 2 := by push_cast; rw [hk]; ring
    rw [e]; exact GlobalTheory.VacuumCharacter.hasInfExp_twist (hbt t τ) (hη.2.2.2 τ) _
  simp only [hsA, hsW, detPlus_neg_one_one, Finset.prod_const_one, mul_one, map_one]
  rw [Circle.coe_inv, hxv _ (fun τ => k τ - WW.rank) hx', ← Finset.prod_inv_distrib, detChar_apply, hmt]
  exact Finset.prod_congr rfl fun τ _ => (_root_.zpow_neg _ _).symm
end GlobalTheory.BottomRealChar
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_real_character_twist : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ → IsBottomTri W i j X → ∃ χ : GinfC A →* ℂ, Continuous χ ∧ (∀ (t : T) (g : GinfC A), (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g.1, 1) (X.f t) = χ g • X.f t) ∧ ∀ g : GinfC A, (∀ τ a b, IsAlgebraic ℚ (compAt W.θ τ (Formalism.L2.Theta.mt A g.1) a b)) → IsAlgebraic ℚ (χ g) := by
  first | exact @_root_.GlobalTheory.BottomRealChar.exists_real_character_of_bottom | exact _root_.GlobalTheory.BottomRealChar.exists_real_character_of_bottom | (intros; apply _root_.GlobalTheory.BottomRealChar.exists_real_character_of_bottom <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsRowLiftMatching
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowLift
theorem exists_row_lift_matching : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.IsBase → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b →
    ∃ G' : GlobalTheory.Grid.GridPre R, G'.Is ∧ GlobalTheory.RowLift.RowMatchS ch G' := by
  intro hP D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hb CF hs
  have hsc : ch.sc.cGap = 1 := by rw [hs]
  obtain ⟨G, hG, hsp, harr⟩ := GlobalTheory.GridJoin.exists_gridPre hP.discreteSeriesUpqExists hP.discreteSeriesCover
    hP.harishChandraModules hS.host hS.size hS.core hsc ch.W hb.weil
  have hfr : ∀ i, i ≤ D.R.m → Formalism.L2.DIV.IsFrame (G.V i 0).β (G.V i 0).Λ := by
    rintro (_ | i) hi
    · obtain ⟨c, h⟩ := hS.core.lev.βY 0 (by have := D.R.two_le_m; omega)
      exact h.1
    · obtain ⟨c, h⟩ := (hG.spaces.vert i 0 hi (Nat.zero_le _)).frame
      exact h.1
  obtain ⟨m00, mV, hm, hν, hfd⟩ := GlobalTheory.ColMeas.measCol_of_choice ch G hG.meas hsp hfr hb.vol
  refine ⟨GlobalTheory.GridJoin.withMeas G m00 mV G.mP G.mX, ⟨GlobalTheory.GridJoin.isSpaces_withMeas hG.spaces,
    GlobalTheory.GridJoin.isChars_withMeas hG.chars, GlobalTheory.GridJoin.isArrows_withMeas hG.arrows, hm,
    GlobalTheory.GridJoin.isData_withMeas hG.data⟩, ⟨fun i hi => (hsp.vert i 0 hi (Nat.zero_le _)).sp, hν, hfd,
    GlobalTheory.RowKer.kernel_row ch (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _
      (hS.core.lev.βY 0 (by have := D.R.two_le_m; omega))) hb.weil G hG ⟨hsp, harr⟩⟩⟩
end GlobalTheory.RowLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_row_lift_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (large₂ : SizeData₂ D)
    {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A},
    HidaSetting large₂ R F → ∀ (ch : Choice R), ch.IsBase → ∀ (CF : ℝ), ch.AtScale CF large₂.sc.b →
    ∃ G' : GlobalTheory.Grid.GridPre R, G'.Is ∧ GlobalTheory.RowLift.RowMatchS ch G' := by
  first | exact @_root_.GlobalTheory.RowLift.exists_row_lift_matching | exact _root_.GlobalTheory.RowLift.exists_row_lift_matching | (intros; apply _root_.GlobalTheory.RowLift.exists_row_lift_matching <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsSeesawPairOfThetaData
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.PairIt
open GlobalTheory.Chain GlobalTheory.Chain.RealIt
theorem exists_seesaw_pair : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx := by
  intro hPr D S S' aS aT hP V W M M' θ ψ hθ
  have hD := hPr.discreteSeriesCover
  have hH := hPr.harishChandraModules
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have hB := GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ =>
    exists_locIt_pair hX h1 h2 hB M M' τ (hP τ)
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
  refine ⟨It, fun ω ⟨χS, χT, hω, he⟩ f hf => ?_⟩
  have hc := fun τ => GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI hr (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2
    (fun τ => (hc τ).2.1) fun τ => (hc τ).2.2
end GlobalTheory.PairIt
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_seesaw_pair_of_theta_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx := by
  first | exact @_root_.GlobalTheory.PairIt.exists_seesaw_pair | exact _root_.GlobalTheory.PairIt.exists_seesaw_pair | (intros; apply _root_.GlobalTheory.PairIt.exists_seesaw_pair <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsSmallTripleOfWeilVacuum
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SmallTriple
open GlobalTheory.Grid MeasureTheory
variable {D : D7}
private theorem eta_sq_eq_one_alt {η : (AF D.host.F)ˣ →* Circle} (h : IsEta D η) (a : (AF D.host.F)ˣ) : η a ^ 2 = 1 := by
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have e := h.2.2.1 (idF D a)
  have e2 : Units.map (Algebra.norm (AF D.host.F) : AE D →* AF D.host.F) (idF D a) = a ^ 2 := by
    ext1
    show Algebra.norm (AF D.host.F) (algebraMap (AF D.host.F) (AE D) (a : AF D.host.F)) = ((a ^ 2 : (AF D.host.F)ˣ) : AF D.host.F)
    let b := (Module.finBasis D.host.F D.host.E).baseChange (AF D.host.F)
    rw [Algebra.norm_algebraMap_of_basis b, Fintype.card_fin, h2, Units.val_pow_eq_pow_val]
  rwa [e2, map_pow] at e
private theorem restriction_eta_add_two {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ (n + 2)) : ResEta D χ n :=
  ⟨h.1, fun η hη a => by rw [h.2 η hη a, pow_add, eta_sq_eq_one_alt hη, mul_one]⟩
private theorem exists_weil_representation (hP : GlobalTheory.Published.WeilRepresentationUnitaryPair) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (ε : Bool) (S W : HSp D) {χS χW : (AE D)ˣ →* Circle} (h1 : IsHeckeChar D χS) (h2 : IsHeckeChar D χW)
    (h3 : ResEta D χS S.rank) (h4 : ResEta D χW W.rank) : ∃ ω : WRep S W, IsWeil ψ ε S W χS χW ω := by
  obtain ⟨om, h⟩ := hP D ψ (sgn ε S) W χS χW hψ h1 h2 h3 h4
  exact ⟨om.comp ((ofSgn ε S).symm.toMonoidHom.prodMap (MonoidHom.id _)), h⟩
private theorem exists_vacuum_vector (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT) : ∃ f, IsVacO ψ θ S T sS sT ΛS ΛT f := by
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T sS sT hS hT ΛS ΛT dS dT
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  let _ : MeasurableSpace (WO S T) := measMx _ _
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have h1 := (hf 1).1
  simp only [one_mul] at h1
  obtain ⟨⟨μ, 𝓕, hμ⟩, c, hc⟩ := GlobalTheory.T.exists_normalise_meanSquare_of_cocompact' (WO S T) (ratL T S) K hK hcov f h1.cont f0 (by
    rintro _ ⟨g, rfl⟩ w
    have e := h1.quasi g w
    have e' := congrArg norm e
    rw [norm_mul, hψ.1.2.1, one_mul] at e'
    exact e')
  exact ⟨fun w => c * f w, hψ, hθ, (hf c).1, (hf c).2.1, (hf c).2.2, ⟨(μ, 𝓕), hμ⟩,
    fun p hp => hc p.1 p.2 hp.1 hp.2.1 hp.2.2⟩
theorem exists_small_triple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (T : Type) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E)
    (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)) (rB : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig B') (rW : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig WW₁),
    IsInfFam θ → X.Is ψ θ α β νH S → rB.Is → rW.Is → B'.rank + 2 = A'.rank → WW₁.rank + 2 = WW.rank →
    ∃ Y : Tri T A B' WW₁, Y.rA = X.rA ∧ Y.rA' = rB ∧ Y.rW = rW ∧ Y.Is ψ θ α β νH S := by
  intro hP D T A A' WW B' WW₁ X ψ θ α β νH S rB rW hθ hX hB hW eB eW
  have hψ : IsStdChar D ψ (-1) := hX.isVac.1
  have hA := hX.rigA
  choose ω hω using fun t => exists_weil_representation hP.weilRepresentationUnitaryPair hψ true A WW₁ (hX.weil t).hecS (hX.weil t).hecT
    (hX.weil t).resS (restriction_eta_add_two (eW ▸ (hX.weil t).resT))
  choose ω' hω' using fun t => exists_weil_representation hP.weilRepresentationUnitaryPair hψ false B' WW₁ (hX.weil' t).hecS (hX.weil' t).hecT
    (restriction_eta_add_two (eB ▸ (show ResEta D (α t) A'.rank from (hX.weil' t).resS))) (restriction_eta_add_two (eW ▸ (hX.weil' t).resT))
  have hneg : IsSelfDualC (neg A) X.rA.Λ := by
    refine ⟨hA.1.1, fun y => (hA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  obtain ⟨vac, hv⟩ := exists_vacuum_vector ψ θ hψ hθ (neg A) WW₁ (fun τ => -X.rA.s τ) rW.s
    (fun τ => isCartanInv_sgn true _ τ (hA.2.2 τ).1) (fun τ => (hW.2.2 τ).1) X.rA.Λ rW.Λ hneg hW.1
  obtain ⟨vac', hv'⟩ := exists_vacuum_vector ψ θ hψ hθ B' WW₁ rB.s rW.s
    (fun τ => (hB.2.2 τ).1) (fun τ => (hW.2.2 τ).1) rB.Λ rW.Λ hB.1 hW.1
  have hν : ∀ t, IsHeckeChar D (α t / β t) := fun t => (hX.weil' t).hecT
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D ψ θ A WW₁ X.rA rW _ _ _ _ _ hA hW (hν t) (hX.idem t)
    (GlobalTheory.ConstRatio.ideal_ne_bot X S t) hv
  choose f' hf' _ using fun t => GlobalTheory.T.exists_thetaFunction_standardPairSecond D ψ θ B' WW₁ rB rW _ _ _ _ A.rank _ hB hW (hν t) (hX.idem t)
    (GlobalTheory.ConstRatio.ideal_ne_bot X S t) hv'
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas B'
  have hr := hX.rank
  exact ⟨⟨X.rA, rB, rW, ω, ω', vac, vac', X.e, X.c, f, f', X.m, X.fd, m', fd'⟩, rfl, rfl, rfl,
    ⟨by omega, hA, hB, hW, hω, hω', hv, hv', hX.idem, hX.expo, hf, hf', hX.meas, hm'⟩⟩
end GlobalTheory.SmallTriple
end
theorem _root_.GlobalTheory.T.exists_small_triple_of_weil_vacuum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (T : Type) (A A' WW B' WW₁ : HSp D) (X : Tri T A A' WW)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E)
    (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)) (rB : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig B') (rW : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig WW₁),
    IsInfFam θ → X.Is ψ θ α β νH S → rB.Is → rW.Is → B'.rank + 2 = A'.rank → WW₁.rank + 2 = WW.rank →
    ∃ Y : Tri T A B' WW₁, Y.rA = X.rA ∧ Y.rA' = rB ∧ Y.rW = rW ∧ Y.Is ψ θ α β νH S := _root_.GlobalTheory.SmallTriple.exists_small_triple
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FlipSequenceStartColumn
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.FlipStart.Col
variable {D : D7}
variable {T : Type} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
end GlobalTheory.FlipStart.Col
open GlobalTheory.FlipStart GlobalTheory.FlipStart.Col in
theorem GlobalTheory.FlipStart.flipSequence_start_column : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank), GlobalTheory.FlipStart.ChainVecs ch t f → GlobalTheory.FlipStart.ChainPols ch q → ∀ M : Vol ch.G, M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) ∧ liftP ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) = ch.cv.lift t y := by
  intro _ _
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t f q hf hq M hM y
  have h := col_top hch.weil s.core.chain s.core.models hq hM y D.R.m rfl (fun j => ch.W.fock (.mu t 0 j) (f j) (q j))
    (fun j => ⟨fun h => ⟨f j, (hf j).1 h, rfl⟩, fun h => ⟨f j, (hf j).2 h, rfl⟩⟩) (formTop ch t y)
    (by unfold formTop; exact cast_fun_heq _ _)
  exact ⟨h.1, eq_of_heq h.2⟩
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipSequence_column_succ : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank), GlobalTheory.FlipStart.ChainVecs ch t f → GlobalTheory.FlipStart.ChainPols ch q → ∀ M : Vol ch.G, M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) ∧ liftP ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) = ch.cv.lift t y := by
  first | exact @_root_.GlobalTheory.FlipStart.flipSequence_start_column | exact _root_.GlobalTheory.FlipStart.flipSequence_start_column | (intros; apply _root_.GlobalTheory.FlipStart.flipSequence_start_column <;> assumption)
end
end

