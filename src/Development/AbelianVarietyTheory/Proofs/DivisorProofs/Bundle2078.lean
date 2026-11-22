import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuesMemOfLocal
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0564
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeEqualityOfEvaluationVector
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option autoImplicit false

noncomputable section

open Classical

namespace GlobalTheory.EvalLowType

theorem zero_of_span {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ j, AddCommGroup (L j)] [∀ j, Module ℂ (L j)]
    {X : Type} [AddCommGroup X] [Module ℂ X] (F : MultilinearMap ℂ L X) (v₀ : ∀ j, L j) (P : ∀ j, L j → Prop)
    (hspan : ∀ j, Submodule.span ℂ {u | P j u} = ⊤)
    (hstep : ∀ (v : ∀ j, L j) (j : ι) (u : L j), v j = v₀ j → P j u → F v = 0 → F (Function.update v j u) = 0)
    (h0 : F v₀ = 0) : ∀ v, F v = 0 := by
  have key : ∀ s : Finset ι, ∀ v : ∀ j, L j, (∀ j ∉ s, v j = v₀ j) → F v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      have : v = v₀ := funext fun j => hv j (Finset.notMem_empty j)
      rw [this]; exact h0
    | insert a s ha ih =>
      intro v hv
      have h1 : F (Function.update v a (v₀ a)) = 0 := ih _ fun j hj => by
        by_cases hja : j = a
        · subst hja; simp
        · rw [Function.update_of_ne hja]; exact hv j (by simp [hja, hj])
      have hmem : v a ∈ Submodule.span ℂ {u | P a u} := by rw [hspan a]; trivial
      have hall : ∀ u ∈ Submodule.span ℂ {u | P a u},
          F (Function.update (Function.update v a (v₀ a)) a u) = 0 := by
        intro u hu
        induction hu using Submodule.span_induction with
        | mem u hu => exact hstep _ a u (by simp) hu h1
        | zero => exact F.map_update_zero _ _
        | add x y _ _ hx hy => rw [F.map_update_add, hx, hy, add_zero]
        | smul c x _ hx => rw [F.map_update_smul, hx, smul_zero]
      have e : Function.update (Function.update v a (v₀ a)) a (v a) = v := by simp
      rw [← e]; exact hall _ hmem
  exact fun v => key Finset.univ v (fun j hj => absurd (Finset.mem_univ j) hj)

theorem adForm_lowT_equiv : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.models_HW → ∀ (i : Fin D.R.m) (x : Fin (R.nW i) → D.what₂.LL) (τ : D.what₂.Tau) (k : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (u : lowT (R.MW i (sg0 D A)) τ), ((u : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) = (R.MW i (sg0 D A)).σ τ k ((v τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) → adForm R i x (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) = Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)) (adForm R i x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hHW i x τ k hk v u hu
  have hmem : adForm R i x ∈ R.Wall i (sg0 D A) := by
    rw [← (hHW i (sg0 D A)).2.1]
    exact LinearMap.mem_range_self _ _
  have hfr : IsUnit ((R.MW i (sg0 D A)).fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ)
  have e1 : (R.MW i (sg0 D A)).fr τ * ((R.MW i (sg0 D A)).fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hfr
  have e2 : ((R.MW i (sg0 D A)).fr τ)⁻¹ * (R.MW i (sg0 D A)).fr τ = 1 := Matrix.nonsing_inv_mul _ hfr
  have hkJ : kᴴ * Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) * k = Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) := by
    have hu1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  have hg : ((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ) := by
    show _ = _
    rw [← (R.MW i (sg0 D A)).fr_gram τ]
    have e3 : (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ * ((R.MW i (sg0 D A)).fr τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ, e3, Matrix.one_mul,
      ← Matrix.mul_assoc ((R.MW i (sg0 D A)).fr τ) (((R.MW i (sg0 D A)).fr τ)⁻¹), e1, Matrix.one_mul]
    rw [← Matrix.mul_assoc kᴴ, ← Matrix.mul_assoc (kᴴ * _), hkJ]
  have hrep : (R.MW i (sg0 D A)).rep τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ) =
      (R.MW i (sg0 D A)).σ τ k := by
    unfold Formalism.IndefR.Mult.DSModel.rep
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, e1, Matrix.mul_one]
  have hupd : (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) =
      Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ) := by
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  rw [hupd]
  suffices H : ∀ T ∈ R.Wall i (sg0 D A), T (Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ)) =
      Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))
        (T (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) from H _ hmem
  intro T0 hT0
  induction hT0 using Submodule.span_induction with
  | mem T hT =>
    exact hT.equiv τ _ hg _ _ (by rw [hrep]; exact hu)
  | zero => rfl
  | add S T _ _ hS hT =>
    simp only [MultilinearMap.add_apply, hS, hT]
    rfl
  | smul a T _ hT =>
    simp only [MultilinearMap.smul_apply, hT]
    rfl

end GlobalTheory.EvalLowType

theorem GlobalTheory.EvalLowType.lowType_of_eval : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G) χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ u : U, (∀ w₀ : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w₀ ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w₀ ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w₀)) → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hcore i _ _ _ _ _ _ v _ _ _ _ _ _ _ _ ℓ _ _ U χ ξR ω φ hker Λ h _ _ N x₀ P x f y _ _ _ _ _ _ _ _ y₀ c _ φ' hvec u hu
  have hext : IsExtVec (R.MW i (sg0 D A)) (v₀ i (sg0 D A)) := (fw.hv₀ i (sg0 D A)).1
  have hs0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hσ : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK (sg0 D A) :=
    fun x _ => congrArg (fun s : D.what₂.LL →+* ℂ => s (D.embE x)) hs0
  let w₀ : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ := fun ρ => ⟨v₀ i (sg0 D A) ρ, (hext ρ).2.1⟩
  let Lin : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    { toFun := fun t g => Datum.thetaKO ω h g (Datum.pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
        (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ' (R.ioP i t ((O i).c0' y)))
      map_add' := fun a b => by funext g; simp [Datum.thetaKO, map_add]
      map_smul' := fun a b => by funext g; simp [Datum.thetaKO, map_smul] }
  let act := Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹))
  let Rt : MultilinearMap ℂ (fun ρ => lowT (R.MW i (sg0 D A)) ρ) (GA D (Wc D i) → ℂ) :=
    (D.what₂.embLL c • (act ∘ₗ Lin)).compMultilinearMap (PiTensorProduct.tprod ℂ)
  let Lf : MultilinearMap ℂ (fun ρ => lowT (R.MW i (sg0 D A)) ρ) (GA D (Wc D i) → ℂ) :=
    (adForm R i (cuspTo hT.p fw i (f u))).compLinearMap fun ρ => (lowT (R.MW i (sg0 D A)) ρ).subtype
  have hRt : ∀ w, Rt w = D.what₂.embLL c • act (singleSeries R i ω φ' h ((O i).c0' y) w) := fun w => rfl
  have hLf : ∀ w, Lf w = adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => (w ρ : (R.MW i (sg0 D A)).sm ρ)) := fun w => rfl
  have hrs : ∀ (g : GA D (Wc D i)) (a b : GA D (Wc D i) → ℂ) (s : ℂ),
      Formalism.L2.Theta.rTr (Wc D i) g a - s • Formalism.L2.Theta.rTr (Wc D i) g b = Formalism.L2.Theta.rTr (Wc D i) g (a - s • b) :=
    fun _ _ _ _ => rfl
  have key := GlobalTheory.EvalLowType.zero_of_span (Lf - Rt) w₀
    (fun ρ z => ∃ k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ),
      ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((v₀ i (sg0 D A) ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ))
    (fun ρ => GlobalTheory.LowSpan.span_translates_eq_top _ _ hext ρ
      ((GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hσ)).2 ρ))
    (fun w ρ z hw ⟨k, hk, hu'⟩ h0 => by
      have hu2 : ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((w ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) := by
        rw [hu', hw]
      have e1 := GlobalTheory.EvalLowType.adForm_lowT_equiv R hcore.models.HW i (cuspTo hT.p fw i (f u)) ρ k hk w z hu2
      have e2 := GlobalTheory.T.singleThetaSeries_K_equivariant_lowest_type R F hcore i _ χ ξR _ ω φ hker _ _ φ' hvec h ((O i).c0' y) ((u : G)⁻¹) ρ k hk w z hu2
      rw [MultilinearMap.sub_apply, hLf, hRt, e1, e2]
      change Formalism.L2.Theta.rTr (Wc D i) _ (Lf w) - D.what₂.embLL c • Formalism.L2.Theta.rTr (Wc D i) _ (act _) = 0
      rw [hrs, ← hRt, ← MultilinearMap.sub_apply, h0]
      rfl)
    (by
      rw [MultilinearMap.sub_apply, sub_eq_zero, hLf, hRt]
      exact hu w₀ fun ρ => rfl)
  intro w
  have := key w
  rw [MultilinearMap.sub_apply, sub_eq_zero, hLf, hRt] at this
  exact this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalIdealsMeetingSubspaceCover
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.ExpCover

private theorem latD_of {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (F : Frame l ι N)
    (lam : ι → ℕ → ℕ) (y : NablaT (PadicAlgCl l) N lam)
    (h : ∃ x ∈ tensSub (deltaIn F.O N lam), GlobalTheory.LatBC.bc F.emb N lam x = y) : y ∈ F.latD lam := by
  obtain ⟨x, ⟨z, rfl⟩, rfl⟩ := h
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    rw [LinearMap.map_smul, PiTensorProduct.map_tprod, LinearMap.map_smulₛₗ, GlobalTheory.LatBC.bc_tprod]
    exact AddSubgroup.subset_closure ⟨r, fun τ => GlobalTheory.LatBC.dwMap F.emb N _ (m τ),
      fun τ => ⟨((m τ : Formalism.GradedWeylDivisibility.dualWeyl F.O N N (res N (lam τ))) : MvPolynomial (Fin N × Fin N) F.O), (m τ).2, rfl⟩, rfl⟩
  | add a b ha hb =>
    rw [map_add, map_add]
    exact add_mem ha hb

end GlobalTheory.ExpCover

namespace GlobalTheory.ExpCover

section Glue

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type}
  (B : BlockDat K G0 Pl0) (ℓ : Lvl K G0) (Z : Submodule K B.S.Forms)

private theorem toF_coe (z : Fin (B.dZ ℓ Z) → K) :
    ((B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) = B.S.I ((B.fE ℓ Z).mulVec z) := by
  simp [BlockDat.toF, BlockDat.fE, CSD.I, Matrix.mulVec_mulVec]

private theorem toF_mem (z : Fin (B.dZ ℓ Z) → K) : B.toF ℓ Z z ∈ Z := by
  have h1 : (B.zE ℓ Z).mulVec z ∈ B.Z0 ℓ Z := by
    rw [BlockDat.zE, subE_mulVec]; exact Submodule.coe_mem _
  have h2 : (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec z) ∈ B.coord Z := h1
  obtain ⟨f, hf, hfe⟩ := Submodule.mem_map.1 h2
  have : B.toF ℓ Z z = f := by
    simp only [BlockDat.toF, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply]
    rw [← hfe]; simp
  rw [this]; exact hf

private theorem mem_cutZ (z : Fin (B.dZ ℓ Z) → K) :
    z ∈ B.cutZ ℓ Z ↔ ∀ c, ((B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) c ∈ B.S.Nab c := by
  rw [toF_coe]
  simp [BlockDat.cutZ, Formalism.DivisionValues.cutLat, CSD.nabLat, Formalism.DivisionValues.valLatF, Submodule.mem_pi]

private theorem mem_delZ (z : Fin (B.dZ ℓ Z) → K) :
    z ∈ B.delZ ℓ Z ↔ ∀ c, ((B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) c ∈ B.S.Del c := by
  rw [toF_coe]
  simp [BlockDat.delZ, Formalism.DivisionValues.cutLat, CSD.delLat, Formalism.DivisionValues.valLatF, Submodule.mem_pi]

private theorem final_step (w : HeightOneSpectrum (𝓞 K)) (L : 𝓞 K) (z : Fin (B.dZ ℓ Z) → K)
    (h : ∃ s : 𝓞 K, s ∉ w.asIdeal ∧
      ∀ c, s • (((algebraMap (𝓞 K) K L) • B.toF ℓ Z z : B.S.Forms) : B.S.Cl → B.S.V) c ∈ B.S.Del c) :
    L • z ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (B.delZ ℓ Z) := by
  obtain ⟨s, hs, hc⟩ := h
  refine ⟨s, hs, ?_⟩
  rw [mem_delZ]
  intro c
  have e : B.toF ℓ Z (s • L • z) = (algebraMap (𝓞 K) K s) • (algebraMap (𝓞 K) K L) • B.toF ℓ Z z := by
    rw [← map_smul, ← map_smul, algebraMap_smul, algebraMap_smul]
  rw [e]
  simpa [algebraMap_smul] using hc c

end Glue

end GlobalTheory.ExpCover

namespace GlobalTheory.ExpCover

private theorem isForm_of_span {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)
    (A : Set (F.G → NablaT (PadicAlgCl l) N lam)) (hA : ∀ f ∈ A, F.IsForm lam f) :
    ∀ f ∈ Submodule.span (PadicAlgCl l) A, F.IsForm lam f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf => exact hA f hf
  | zero => exact ⟨fun _ _ _ => rfl, fun κ g => by rw [Pi.zero_apply, Pi.zero_apply, map_zero, smul_zero]⟩
  | add f f' _ _ h h' =>
    refine ⟨fun γ hγ g => by rw [Pi.add_apply, Pi.add_apply, h.1 γ hγ, h'.1 γ hγ], fun κ g => ?_⟩
    rw [Pi.add_apply, Pi.add_apply, map_add, smul_add, h.2, h'.2]
  | smul a f _ h =>
    refine ⟨fun γ hγ g => by rw [Pi.smul_apply, Pi.smul_apply, h.1 γ hγ], fun κ g => ?_⟩
    rw [Pi.smul_apply, Pi.smul_apply, map_smul, smul_comm, h.2]

private theorem span_stable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} {F : Frame l ι N} {lam : ι → ℕ → ℕ}
    {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type} {B : BlockDat K G0 Pl0}
    {w : HeightOneSpectrum (𝓞 K)} (R : Reads F lam B w) (Z : Submodule K B.S.Forms) (hZ : ∀ i, Z ≤ Z.comap (B.op i)) (i : F.I) :
    ∀ u ∈ Submodule.span (PadicAlgCl l) (R.rd '' Z),
      transOp (F.emb (F.cst i)) (F.tr i) u ∈ Submodule.span (PadicAlgCl l) (R.rd '' Z) := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨f, hf, rfl⟩ := hu
    exact Submodule.subset_span ⟨B.op (R.ix i) f, hZ (R.ix i) hf, funext fun g => R.hecke i f g⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add _ _ _ _ h h' => rw [map_add]; exact Submodule.add_mem _ h h'
  | smul a _ _ h => rw [map_smul]; exact Submodule.smul_mem _ a h

private theorem forms_fin : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ)
    (jK : F.K →* alg F.O N lam), F.Ok → Module.Finite F.O (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam)) := by
  intro l _ ι _ _ N F lam jK hF
  haveI : Module.Finite F.O (NablaT F.O N lam) := GlobalTheory.NablaFin.nablaT_finite F.O N ι lam
  obtain ⟨S, hS⟩ := hF.classes
  haveI : Finite (Formalism.UG.ClassSet F.Γ F.K) := by
    refine Finite.of_surjective (fun s : S => (DoubleCoset.mk F.Γ F.K (s : F.G) : Formalism.UG.ClassSet F.Γ F.K)) ?_
    intro c
    obtain ⟨γ, hγ, s, hs, κ, hκ, e⟩ := hS (Quotient.out c)
    refine ⟨⟨s, hs⟩, ?_⟩
    show DoubleCoset.mk F.Γ F.K s = c
    rw [← DoubleCoset.out_eq' F.Γ F.K c]
    exact (DoubleCoset.eq F.Γ F.K s _).2 ⟨γ, hγ, κ, hκ, e⟩
  exact Formalism.UG.P.automorphic_forms_level_finite_holds F.G F.Γ F.K F.O (NablaT F.O N lam) _ ‹_›

private theorem emb_norm : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N), F.Ok →
    (∀ c, ‖F.emb c‖ ≤ 1) ∧ ∀ c, ‖F.emb c‖ = 1 → IsUnit c := by
  intro l _ ι N F hF
  obtain ⟨hinj, L, _, hL⟩ := hF.ring
  have hmem : ∀ c, F.emb c ∈ L ∧ ‖F.emb c‖ ≤ 1 := by
    intro c
    have : F.emb c ∈ Set.range F.emb := ⟨c, rfl⟩
    rw [hL] at this
    exact this
  refine ⟨fun c => (hmem c).2, fun c hc => ?_⟩
  have hne : F.emb c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hinvL : (F.emb c)⁻¹ ∈ L := inv_mem (hmem c).1
  have hinvn : ‖(F.emb c)⁻¹‖ ≤ 1 := by rw [norm_inv, hc, inv_one]
  have : (F.emb c)⁻¹ ∈ Set.range F.emb := by rw [hL]; exact ⟨hinvL, hinvn⟩
  obtain ⟨d, hd⟩ := this
  have hcd : c * d = 1 := hinj (by rw [map_mul, map_one, hd, mul_inv_cancel₀ hne])
  exact IsUnit.of_mul_eq_one d hcd

private theorem form_lift : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) (b : NablaT F.O N lam →ₛₗ[F.emb] NablaT (PadicAlgCl l) N lam), Function.Injective b → (∀ g x, b (grp F.O N lam g x) = grp (PadicAlgCl l) N lam (fun τ => Matrix.GeneralLinearGroup.map F.emb (g τ)) (b x)) → F.IsJ lam jK → ∀ f : F.G → NablaT (PadicAlgCl l) N lam, F.IsForm lam f → (∀ g, ∃ y, b y = f g) → ∃ x : Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam), ∀ g, b ((x : F.G → NablaT F.O N lam) g) = f g := by
  intro l _ ι _ _ N F lam jK b hb hgrp hJ f hf hex
  choose x hx using hex
  refine ⟨⟨x, ?_⟩, hx⟩
  intro γ g κ
  apply hb
  rw [hx]
  change f _ = b ((jK κ⁻¹ : alg F.O N lam) • x g)
  have e1 : (jK κ⁻¹ : alg F.O N lam) • x g = ((F.chi κ⁻¹ : F.Oˣ) : F.O) • grp F.O N lam (F.kap κ⁻¹) (x g) := by
    rw [hJ κ⁻¹, smul_assoc]
    rfl
  rw [e1, LinearMap.map_smulₛₗ, hgrp, hx]
  have h2 := hf.2 κ⁻¹ (g * κ)
  simp only [Subgroup.coe_inv, mul_inv_cancel_right] at h2
  rw [h2, mul_assoc, hf.1 γ γ.2]

end GlobalTheory.ExpCover

open GlobalTheory.ExpCover in
set_option maxHeartbeats 600000 in

theorem _root_.GlobalTheory.T.maximalIdeals_meeting_subspace_cover : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G0 : Type) [Group G0] [Fintype G0] (Pl0 : Type) (B : BlockDat K G0 Pl0) (w : HeightOneSpectrum (𝓞 K)) [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) ι N) (lam : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) [hm : Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))] [@IsScalarTower F.O F.T (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam)) _ hm.toSMul _], F.Ok → F.IsJ lam jK → F.IsHecke lam jK (NablaT F.O N lam) → ∀ (R : Reads F lam B w) (ℓ : Lvl K G0) (Z : Submodule K B.S.Forms), (∀ i, Z ≤ Z.comap (B.op i)) → Covers B ℓ Z w fun m : {m : MaximalSpectrum F.T // ∃ θ, R.Occurs Z θ ∧ F.Over θ m.asIdeal} => haveI := m.1.isMaximal.isPrime; F.setting lam jK m.1.asIdeal := by
  intro K _ _ _ G0 _ _ Pl0 B w _ ι _ _ N F lam jK hm hst hOk hJ hH R ℓ Z hZ J hInc z hz
  have hfZ : B.toF ℓ Z z ∈ Z := toF_mem B ℓ Z z
  have hfN := (mem_cutZ B ℓ Z z).1 hz
  apply final_step
  apply R.del
  obtain ⟨hbinj, hbli, -⟩ := GlobalTheory.LatBC.bc_props F.emb N lam hOk.ring.1
  have hnorm := emb_norm _ ι N F hOk
  obtain ⟨x, hx⟩ := form_lift _ ι N F lam jK (GlobalTheory.LatBC.bc F.emb N lam) hbinj (GlobalTheory.LatBC.bc_grp F.emb N lam) hJ
    (R.rd (B.toF ℓ Z z)) (R.form _) (fun g => (GlobalTheory.LatBC.latN_iff F lam _).1 (R.nab _ hfN g))
  have hfin := forms_fin _ ι N F lam jK hOk
  have hfinV : Module.Finite F.O (NablaT F.O N lam) := GlobalTheory.NablaFin.nablaT_finite F.O N ι lam
  have hxS : (fun g => GlobalTheory.LatBC.bc F.emb N lam ((x : F.G → NablaT F.O N lam) g)) ∈
      Submodule.span (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (R.rd '' Z) := by
    have e : (fun g => GlobalTheory.LatBC.bc F.emb N lam ((x : F.G → NablaT F.O N lam) g)) = R.rd (B.toF ℓ Z z) := funext hx
    rw [e]
    exact Submodule.subset_span (Set.mem_image_of_mem _ hfZ)
  have hloc : ∀ (m : Ideal (MvPolynomial F.I F.O)) (hmax : m.IsMaximal) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ i, ‖θ i‖ ≤ 1) →
      (∀ p, p ∈ m ↔ ‖MvPolynomial.eval₂ F.emb θ p‖ < 1) →
      (∃ v ∈ Submodule.span (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) (R.rd '' Z), v ≠ 0 ∧
        ∀ i g, F.emb (F.cst i) • ∑ s ∈ F.tr i, v (g * s) = θ i • v g) →
      (haveI := hmax.isPrime; F.setting lam jK m).Incl (Formalism.EigenvalueLevelCeiling.plc w) J := by
    rintro m hmax θ h1 h2 ⟨v, hvS, hv0, hv⟩
    have h5 := hInc ⟨⟨m, hmax⟩, θ,
      ⟨v, hvS, hv0, isForm_of_span F lam _ (by rintro _ ⟨f, -, rfl⟩; exact R.form f) v hvS, hv⟩, h1, h2⟩
    exact h5
  have k1 := @values_mem_of_local (Formalism.EigenvalueLevelCeiling.plc w) _ F.O F.I F.G (NablaT F.O N lam) (NablaT (PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)) N lam)
    _ _ _ _ _ _ hfinV _ _ (Forms F.O (A := alg F.O N lam) F.Γ jK (NablaT F.O N lam))
  have k1b := @k1 hm
  have k2 := @k1b hst hfin F.emb hOk.ring.1 hnorm.1 hnorm.2 (GlobalTheory.LatBC.bc F.emb N lam) hbinj hbli F.tr F.cst
  have k3 := k2 hH.2
  have k3b := k3 (tensSub (deltaIn F.O N lam)) (Submodule.span _ (R.rd '' Z)) (span_stable R Z hZ) x hxS ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : F.O) J
  have k4 := k3b {y | ∀ g, (y : F.G → NablaT F.O N lam) g ∈ tensSub (deltaIn F.O N lam)} (fun _ hy => hy)
  clear k1 k1b k2 k3 k3b
  have k5 := k4 (fun m hmax θ h1 h2 h3 y => by
    have h7 := hloc m hmax θ h1 h2 h3
    unfold HidaSetting.Incl TopIncl locSet at h7
    obtain ⟨x', hx', s, hs⟩ := h7 y
    exact ⟨x', fun g => (Submodule.mem_pi.1 (Submodule.mem_inf.1 hx').2) g (Set.mem_univ _), s, hs⟩)
  have key : ∀ g, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : F.O) ^ J • (x : F.G → NablaT F.O N lam) g ∈ tensSub (deltaIn F.O N lam) := by
    intro g
    have h7 := k5 g
    rw [Submodule.coe_smul, Pi.smul_apply] at h7
    exact h7
  intro g
  apply latD_of F lam
  refine ⟨_, key g, ?_⟩
  rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hx, Pi.smul_apply]
  simp only [map_pow, map_natCast]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedFiniteDatumNegHomEqStandardPairFirst
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
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

namespace GlobalTheory.BotMove.Fst

private theorem selfDual_neg {D : D7} {A : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} (hA : IsSelfDualC A Λ) :
    IsSelfDualC (GlobalTheory.Grid.neg A) Λ := by
  refine ⟨hA.1, fun y => (hA.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
  · simp [GlobalTheory.Grid.neg_gram, hc]
  · simp [GlobalTheory.Grid.neg_gram] at hc ⊢
    exact neg_eq_iff_eq_neg.2 hc

private theorem placeModel_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm) (c : ℂ) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • f₀) (c • Tm) := by
  have hs : ∀ x (F : WO S T → ℂ), heisO ψ S T x (c • F) = c • heisO ψ S T x F := fun x F => by
    funext w
    simp only [heisO, Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hs, h.trans Φ hΦ x hx]
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, hs, h.modul Φ hΦ y hy]
  · rw [LinearMap.smul_apply, h.vac]

private theorem thetaAt_smul {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {e : AE D} {Λ : AddSubgroup (WO S T)}
    {f₀ Φ f : WO S T → ℂ} {c : ℂ} (hc : c ≠ 0)
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • f₀) Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ (c⁻¹ • f) := by
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := h
  refine ⟨⟨c⁻¹ • T₀, ?_⟩, fun T' hT' => ?_⟩
  · have := placeModel_smul hT₀ c⁻¹
    rwa [inv_smul_smul₀ hc] at this
  · have e1 : f = (c • T') Φ := hall _ (placeModel_smul hT' c)
    show c⁻¹ • f = T' Φ
    rw [e1, LinearMap.smul_apply, inv_smul_smul₀ hc]

private theorem thetaAt_move {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T} (hΛ : IsSelfDualC S Λ) (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ')
    (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T} (hb : GlobalTheory.FinPl.Moves S b Λ M (fun _ => True))
    (hb' : GlobalTheory.FinPl.Moves T b' Λ' M' (fun _ => True)) {e : AE D} {Φ f₀ f : WO S T → ℂ} (hee : e * e = e)
    (hinf : infPart D e = 0) (hf₀ : IsThetaFunO ψ S T f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) 1 f₀ Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 (om (b, b') f₀)
      (fun x => Φ (actO S T b⁻¹ b'⁻¹ x)) (om (b, b') f) := by
  have key := GlobalTheory.VacMove.mem_latO_iff_actO hΛ hM hΛ' hM' hb hb'
  have key' := GlobalTheory.VacMove.mem_latO_iff_actO hM hΛ hM' hΛ' (GlobalTheory.VacMove.moves_inv hb) (GlobalTheory.VacMove.moves_inv hb')
  have omm : ∀ p q (X : WO S T → ℂ), om p (om q X) = om (p * q) X := fun p q X => by
    rw [map_mul]; rfl
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hf
  have th0 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T Λ Λ' hΛ hΛ' e hee hinf f₀ hf₀ T₀ hT₀
  refine ⟨⟨_, GlobalTheory.SplitMove.isPlaceModel_move₂ hW key hT₀ th0⟩, fun T' hT' => ?_⟩
  have th1 := GlobalTheory.SchrTheta.isTheta_placeModel D ψ hW.std S T M M' hM hM' e hee hinf _
    (hW.om_pres _ _ hf₀) T' hT'
  have pm := GlobalTheory.SplitMove.isPlaceModel_move₂ hW key' hT' th1
  have ev : om (b⁻¹, b'⁻¹) (om (b, b') f₀) = f₀ := by
    rw [omm, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one]; rfl
  rw [ev] at pm
  have hf' : f = om (b⁻¹, b'⁻¹) (T' fun t => Φ (actO S T b⁻¹ b'⁻¹ t)) := hall _ pm
  rw [hf', omm, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one]; rfl

private theorem frMapO_move {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (g : GA D S) (h : GA D T) (x : WO S T) :
    frMapO S T (Lev.finE S g * βS) (Lev.finE T h * βT) x = frMapO S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  have e1 : (Formalism.L2.Theta.mt T h⁻¹).map (toEAf D) = ((Lev.finE T h)⁻¹).val := by
    rw [← map_inv]; rfl
  have e2 : (Formalism.L2.Theta.mt S g).map (toEAf D) = (Lev.finE S g).val := rfl
  rw [frMapO, frMapO, actO, inv_inv, Matrix.map_mul, Matrix.map_mul, e1, e2, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [Matrix.mul_assoc]

private theorem stdFst_move {D : D7} (ν : (AE D)ˣ →* Circle) (e : AE D) (I : Ideal (𝓞 D.host.E)) (S T : HSp D)
    (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (h : GA D T) :
    stdFst ν e I S T (Lev.finE S g * βS) (Lev.finE T h * βT) = fun x => stdFst ν e I S T βS βT (actO S T g⁻¹ h⁻¹ x) := by
  funext x
  unfold stdFst
  rw [frMapO_move, GlobalTheory.SchrMove.isHalf_actO_iff g⁻¹ h⁻¹ x]

end GlobalTheory.BotMove.Fst

theorem _root_.GlobalTheory.T.movedFiniteDatum_negHom_eq_standardPair_first : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    ∀ t, IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) (latO (neg A) WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.Λ (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.Λ fun _ => True) 1 (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').vac
    (stdFst (α t / β t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').e t) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ideal S t) A WW (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rA.β (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').rW.β) ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').f t) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA _ hW g _ g' _ h _ mA _ mW t₀ r r' hr hv _ t
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hY.idem t)
  have mA' : GlobalTheory.FinPl.Moves (neg A) ((ofSgn true A).symm g) Y.rA.Λ ΛA (fun _ => True) := mA
  have h1 := GlobalTheory.BotMove.Fst.thetaAt_move (S := neg A) (hY.weil t) (GlobalTheory.BotMove.Fst.selfDual_neg hY.rigA.1)
    (GlobalTheory.BotMove.Fst.selfDual_neg hA) hY.rigW.1 hW mA' mW ho.idem ho.infPart_eq hY.isVac.2.theta (hY.fst t)
  have e1 : ∀ F, (Y.ω t).toSgn true ((ofSgn true A).symm g, h) F = Y.ω t (g, h) F := fun F => rfl
  rw [e1, e1, hv t] at h1
  have h2 := GlobalTheory.BotMove.Fst.thetaAt_smul (hr t).1 h1
  have e2 := GlobalTheory.BotMove.Fst.stdFst_move (α t / β t) (Y.e t) (Y.ideal S t) A WW Y.rA.β Y.rW.β g h
  show IsThetaAt ψ (symplO (neg A) WW) (heisO ψ (neg A) WW) (Y.e t) (latO (neg A) WW ΛA ΛW fun _ => True) 1 (Y.ω t₀ (g, h) Y.vac)
    (stdFst (α t / β t) (Y.e t) (Y.ideal S t) A WW (Lev.finE A g * Y.rA.β) (Lev.finE WW h * Y.rW.β))
    ((r t)⁻¹ • Y.ω t (g, h) (Y.f t))
  rw [e2]
  exact h2
end

