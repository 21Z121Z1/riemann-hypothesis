import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1884
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergDiagonalIntegralMemSchwartzBruhatStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDiagonalIntegral_mem_schwartzBruhat : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ Φ₀ ∈ SB (κ ⊕ κ → Fv F v), ∀ c : ℂ, c ≠ 0 → ∀ U : Set ((κ → Fv F v) × (κ → Fv F v)), IsOpen U → IsCompact U → 0 ∈ U →
      (∀ w, diagW ψ μ Φ₀ w = U.indicator (fun _ => c) w) →
    ∀ Φ ∈ SB (κ ⊕ κ → Fv F v), diagW ψ μ Φ ∈ SB ((κ → Fv F v) × (κ → Fv F v)) := by
  first | exact @GlobalTheory.DiagWSB.diagW_mem_SB | exact GlobalTheory.DiagWSB.diagW_mem_SB | (intros; apply GlobalTheory.DiagWSB.diagW_mem_SB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergFinitePointReadsClassicalTranslationStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergFinitePoint_reads_classicalTranslation : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ G f, Reads ψ θ hS hT cc δ r G f → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
    Reads ψ θ hS hT cc δ r (U D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G) (heisO ψ S T (finPt hS hT r z) f) := by
  first | exact @GlobalTheory.NormExact.heisO_finPt_reads | exact GlobalTheory.NormExact.heisO_finPt_reads | (intros; apply GlobalTheory.NormExact.heisO_finPt_reads <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergStableRelationOfVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.InductLagr

theorem schr_add_mem {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (N : Submodule ℂ ((κ → K) → ℂ)) (a b : (κ → K) × (κ → K))
    (ha : ∀ φ ∈ N, GlobalTheory.WeilM.schr ψ a φ ∈ N) (hb : ∀ φ ∈ N, GlobalTheory.WeilM.schr ψ b φ ∈ N) :
    ∀ φ ∈ N, GlobalTheory.WeilM.schr ψ (a + b) φ ∈ N := by
  intro φ hφ
  set c : K := ⅟(2 : K) * (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2) with hc
  have law : GlobalTheory.WeilM.schr ψ a (GlobalTheory.WeilM.schr ψ b φ) = ψ c • GlobalTheory.WeilM.schr ψ (a + b) φ := by
    funext x
    have key : (x ⬝ᵥ a.2 + ⅟(2 : K) * (a.1 ⬝ᵥ a.2)) + ((x + a.1) ⬝ᵥ b.2 + ⅟(2 : K) * (b.1 ⬝ᵥ b.2)) =
        c + (x ⬝ᵥ (a + b).2 + ⅟(2 : K) * ((a + b).1 ⬝ᵥ (a + b).2)) := by
      have h2 : ⅟(2 : K) * 2 = 1 := invOf_mul_self 2
      simp only [hc, Prod.fst_add, Prod.snd_add, dotProduct_add, add_dotProduct]
      linear_combination (-(a.1 ⬝ᵥ b.2)) * h2
    show ψ _ * (ψ _ * φ (x + a.1 + b.1)) = ψ c * (ψ _ * φ (x + (a + b).1))
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key, Prod.fst_add, add_assoc]
  have hne : ψ c ≠ 0 := by
    have h1 : ψ c * ψ (-c) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    exact left_ne_zero_of_mul_eq_one h1
  have e : GlobalTheory.WeilM.schr ψ (a + b) φ = (ψ c)⁻¹ • GlobalTheory.WeilM.schr ψ a (GlobalTheory.WeilM.schr ψ b φ) := by
    rw [law, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [e]
  exact N.smul_mem _ (ha _ (hb _ hφ))

theorem exists_at_locCo {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (p : (κ → Fv F v) × (κ → Fv F v)) :
    ∃ u : W, At (evFin F v) u ∧ GlobalTheory.LatVac.locCo co v u = p := by
  refine ⟨co.e.symm (fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k)), ?_, ?_⟩
  · intro r hr
    rw [← LinearEquiv.map_smul]
    have h0 : r • ((fun k => GlobalTheory.LatVac.liftV v (p.1 k), fun k => GlobalTheory.LatVac.liftV v (p.2 k)) :
        (κ → AF F) × (κ → AF F)) = 0 := by
      refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
      · exact GlobalTheory.LatVac.at_liftV v (p.1 k) r hr
      · exact GlobalTheory.LatVac.at_liftV v (p.2 k) r hr
    rw [h0, map_zero]
  · show ((fun k => evFin F v ((co.e _).1 k)), fun k => evFin F v ((co.e _).2 k)) = p
    rw [LinearEquiv.apply_symm_apply]
    exact Prod.ext (funext fun k => GlobalTheory.LatVac.evFin_liftV v _) (funext fun k => GlobalTheory.LatVac.evFin_liftV v _)

end GlobalTheory.InductLagr

namespace GlobalTheory.InductLagr

theorem rel_of_vac : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {Y : Spc F E d} (M : Model σ X Y) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsGood ψ →
    ∀ {ι : Type} (P : Finset ι) (pl : ι → HeightOneSpectrum (𝓞 F)), Set.InjOn pl P →
    ∀ (Z : ι → Type) [∀ w, TopologicalSpace (Z w)] [∀ w, Add (Z w)]
      (A A' : ι → Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)))
      (co : ∀ w, Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z w)
      (I : ∀ w, ((Fin n × Fin d → Fv F (pl w)) → ℂ) →ₗ[ℂ] (Z w → ℂ))
      (H : AddSubgroup (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)))
      (R : Submodule ℂ ((Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → ℂ) × ((Fin n × Fin d → AF F) → ℂ)))
      (f : SInf F (Fin n × Fin d)),
    (∀ w ∈ P, IsLagrModel M ψ (pl w) (A w) (A' w) (co w) (I w)) →
    (∀ w ∈ P, ∀ u ∈ A w, At (evFin F (pl w)) u ∧ u ∈ H) → (∀ w ∈ P, ∀ u ∈ A' w, At (evFin F (pl w)) u) →
    (∀ w ∈ P, ∀ u, At (evFin F (pl w)) u → ∃ x ∈ A w, ∃ y ∈ A' w, u = x + y) →
    (∀ w ∈ P, ∀ x ∈ A w, ∀ u, co w (u + x) = co w u + co w x) →
    (∀ w ∈ P, ∀ w' ∈ P, w' ≠ w → ∀ x ∈ A w, ∀ u, co w' (u + x) = co w' u) →
    (∀ w ∈ P, ∀ u, ∃ x ∈ A w, co w x = co w u ∧ ∀ y ∈ A' w,
      symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y =
      symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) x y) →
    (∀ w ∈ P, ∀ x ∈ A w, ∀ p ∈ R, (fun u => p.1 (u + x), M.co.rho ψ x p.2) ∈ R) →
    (∀ w ∈ P, ∀ y ∈ A' w, ∀ p ∈ R, (fun u => ψ (symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y) * p.1 u, M.co.rho ψ y p.2) ∈ R) →
    (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (M.vac (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) ∈ R →
    ∀ φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ v, (∀ w ∈ P, pl w ≠ v) → φ v = M.vac v) →
      (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (φ (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ R := by
  intro F E _ _ _ _ _ σ n d X Y M ψ hstd hM ι P pl hpl Z _ _ A A' co I H R f hL hA hA' hdec hadd hloc hrep hRA hRA' hvac
  classical
  suffices key : ∀ S : Finset ι, S ⊆ P → ∀ φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ,
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ v, (∀ w ∈ S, pl w ≠ v) → φ v = M.vac v) →
      (Set.indicator (H : Set _) fun u => ∏ w ∈ P, I w (φ (pl w)) (co w u), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ R by
    intro φ h1 h2
    exact key P subset_rfl φ h1 h2
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ φ _ h2
    have e : φ = M.vac := funext fun v => h2 v (by simp)
    subst e
    exact hvac
  | insert w S hwS ih =>
    intro hsub φ hφ1 hφ2
    have hwP : w ∈ P := hsub (Finset.mem_insert_self _ _)
    have hSP : S ⊆ P := (Finset.subset_insert _ _).trans hsub
    have hfam : GlobalTheory.BigNZ.Fam M φ := by
      refine ⟨hφ1, Filter.eventually_cofinite.2 (((insert w S).image pl).finite_toSet.subset fun v hv => ?_)⟩
      by_contra hc
      exact hv (hφ2 v fun w' hw' e => hc (Finset.mem_coe.2 (Finset.mem_image.2 ⟨w', hw', e⟩)))
    obtain ⟨r, -, er⟩ := GlobalTheory.PureFactor.exists_rest_factor (pl w) f φ (hfam.std hM)

    let C : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → ℂ := fun u => ∏ w' ∈ P.erase w, I w' (φ (pl w')) (co w' u)
    have hne : ∀ w' ∈ P.erase w, pl w' ≠ pl w := fun w' hw' e =>
      (Finset.mem_erase.1 hw').1 (hpl (Finset.mem_erase.1 hw').2 hwP e)
    have hprod : ∀ (χ : (Fin n × Fin d → Fv F (pl w)) → ℂ) u,
        ∏ w' ∈ P, I w' (Function.update φ (pl w) χ (pl w')) (co w' u) = I w χ (co w u) * C u := by
      intro χ u
      rw [← Finset.mul_prod_erase P _ hwP, Function.update_self]
      congr 1
      exact Finset.prod_congr rfl fun w' hw' => by rw [Function.update_of_ne (hne w' hw')]

    let L : ((Fin n × Fin d → Fv F (pl w)) → ℂ) →ₗ[ℂ]
        ((Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → ℂ) × ((Fin n × Fin d → AF F) → ℂ)) :=
      { toFun := fun χ => (Set.indicator (H : Set _) fun u => I w χ (co w u) * C u,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) χ r)
        map_add' := fun a b => Prod.ext (funext fun u => by
            by_cases hu : u ∈ (H : Set _)
            · simp only [Set.indicator_of_mem hu, map_add, Pi.add_apply, Prod.fst_add, add_mul]
            · simp only [Set.indicator_of_notMem hu, Prod.fst_add, Pi.add_apply, add_zero])
          (funext fun _ => add_mul _ _ _)
        map_smul' := fun c a => Prod.ext (funext fun u => by
            by_cases hu : u ∈ (H : Set _)
            · simp only [Set.indicator_of_mem hu, map_smul, Pi.smul_apply, Prod.smul_fst, smul_eq_mul,
                RingHom.id_apply, mul_assoc]
            · simp only [Set.indicator_of_notMem hu, Prod.smul_fst, Pi.smul_apply, smul_zero, RingHom.id_apply])
          (funext fun _ => mul_assoc _ _ _) }
    have hLe : ∀ χ, (Set.indicator (H : Set _) fun u => ∏ w' ∈ P, I w' (Function.update φ (pl w) χ (pl w')) (co w' u),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ (pl w) χ)) = L χ := fun χ =>
      Prod.ext (by simp only [hprod]; rfl) (er χ).symm
    let N : Submodule ℂ ((Fin n × Fin d → Fv F (pl w)) → ℂ) := GlobalTheory.WeilM.SB _ ⊓ R.comap L

    have hvacN : M.vac (pl w) ∈ N := by
      refine ⟨(hM.vac _).1, ?_⟩
      show L _ ∈ R
      rw [← hLe]
      refine ih hSP _ (fun v => ?_) (fun v hv => ?_)
      · by_cases e : v = pl w
        · subst e; rw [Function.update_self]; exact (hM.vac _).1
        · rw [Function.update_of_ne e]; exact hφ1 v
      · by_cases e : v = pl w
        · subst e; rw [Function.update_self]
        · rw [Function.update_of_ne e]
          refine hφ2 v fun w' hw' => ?_
          rcases Finset.mem_insert.1 hw' with h | h
          · subst h; exact fun e' => e e'.symm
          · exact hv w' h

    have hstA : ∀ x ∈ A w, ∀ χ ∈ N,
        GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ (pl w)) (GlobalTheory.LatVac.locCo M.co (pl w) x) χ ∈ N := by
      intro x hx χ hχ
      obtain ⟨hxat, hxH⟩ := hA w hwP x hx
      have hsb := GlobalTheory.SchrSB.schr_mem_SB ψ hstd.1 (pl w) (GlobalTheory.LatVac.locCo M.co (pl w) x) χ hχ.1
      have hact := GlobalTheory.VacBridge.rho_acts_locCo M.co ψ (pl w) x hxat χ
      refine ⟨hsb, ?_⟩
      show L _ ∈ R
      have hR := hRA w hwP x hx (L χ) hχ.2
      convert hR using 1
      refine Prod.ext (funext fun u => ?_) ?_
      · show Set.indicator (H : Set _) (fun u => I w _ (co w u) * C u) u =
          Set.indicator (H : Set _) (fun u => I w χ (co w u) * C u) (u + x)
        have hC : C (u + x) = C u := Finset.prod_congr rfl fun w' hw' => by
          rw [hloc w hwP w' (Finset.mem_of_mem_erase hw') (Finset.ne_of_mem_erase hw') x hx u]
        by_cases hu : u ∈ (H : Set _)
        · have hu' : u + x ∈ (H : Set _) := H.add_mem hu hxH
          rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu', hC, hadd w hwP x hx u,
            (hL w hwP).2.1 x hx χ hχ.1 _ hsb hact (co w u)]
        · have hu' : u + x ∉ (H : Set _) := fun h => hu (by simpa using H.sub_mem h hxH)
          rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu']
      · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) _ r = M.co.rho ψ x (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) χ r)
        rw [er, er, GlobalTheory.BigNZ.Fam.acts hM hfam f hχ.1 hact]

    have hstA' : ∀ y ∈ A' w, ∀ χ ∈ N,
        GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ (pl w)) (GlobalTheory.LatVac.locCo M.co (pl w) y) χ ∈ N := by
      intro y hy χ hχ
      have hyat := hA' w hwP y hy
      have hsb := GlobalTheory.SchrSB.schr_mem_SB ψ hstd.1 (pl w) (GlobalTheory.LatVac.locCo M.co (pl w) y) χ hχ.1
      have hact := GlobalTheory.VacBridge.rho_acts_locCo M.co ψ (pl w) y hyat χ
      refine ⟨hsb, ?_⟩
      show L _ ∈ R
      have hR := hRA' w hwP y hy (L χ) hχ.2
      convert hR using 1
      refine Prod.ext (funext fun u => ?_) ?_
      · show Set.indicator (H : Set _) (fun u => I w _ (co w u) * C u) u =
          ψ (symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) u y) *
            Set.indicator (H : Set _) (fun u => I w χ (co w u) * C u) u
        by_cases hu : u ∈ (H : Set _)
        · obtain ⟨x, hx, hcx, hsx⟩ := hrep w hwP u
          rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, ← hcx,
            (hL w hwP).2.2 y hy χ hχ.1 _ hsb hact x hx, hsx y hy, mul_assoc]
        · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]
      · show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) _ r = M.co.rho ψ y (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F (pl w)) χ r)
        rw [er, er, GlobalTheory.BigNZ.Fam.acts hM hfam f hχ.1 hact]

    have hst : ∀ p, ∀ χ ∈ N, GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ (pl w)) p χ ∈ N := by
      intro p χ hχ
      obtain ⟨u, hu, rfl⟩ := exists_at_locCo M.co (pl w) p
      obtain ⟨x, hx, y, hy, rfl⟩ := hdec w hwP u hu
      rw [map_add]
      exact schr_add_mem _ N _ _ (hstA x hx) (hstA' y hy) χ hχ
    have hN : N = GlobalTheory.WeilM.SB _ :=
      GlobalTheory.T.schroedinger_irreducible_finitePlaceCompletion (pl w) (GlobalTheory.LatVac.psiAt ψ (pl w)) (GlobalTheory.SchrSB.continuous_psiAt ψ hstd.1 _)
        (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hstd _) N inf_le_left hst (M.vac (pl w)) hvacN (hM.vac _).2.1
    have hmem : φ (pl w) ∈ N := hN ▸ hφ1 (pl w)
    have h2 : L (φ (pl w)) ∈ R := hmem.2
    rw [← hLe, Function.update_eq_self] at h2
    exact h2

end GlobalTheory.InductLagr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateFixesThetaDeepLevelStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergTranslate_fixes_theta_deepLevel : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    heisO ψ S T (actO S T g h (finPt hS hT r z) - finPt hS hT r z') F = F := by
  first | exact @GlobalTheory.LevelTr.level_translate | exact GlobalTheory.LevelTr.level_translate | (intros; apply GlobalTheory.LevelTr.level_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPairOfPair
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXUnip

theorem twist_heis_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (om₁ : Rep σ X₁ W) (r₁ s₁ : ℕ),
      H.IsAdapted σ B X X₁ j₀ j₁ → IsPair B M₁ χX χW om₁ r₁ s₁ r' s' →
      ∀ e, IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
      ∀ (g : UA σ X.J) (a : AE F E), mat g *ᵥ incV F H.x = a • incV F H.x →
      (∀ z : Fin n₁ → AE F E, ∃ b : AE F E, mat g *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + b • incV F H.x) →
      (∀ z, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) Φ)) =
        M₁.co.rho B.ψ z (e (om (g, 1) Φ))) ∧
      ∀ u ∈ {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z}, ∀ Φ ∈ schA F (Fin n × Fin d), e (om (g, 1) (M.co.rho B.ψ u Φ)) = e (om (g, 1) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ M₁ om₁ r₁ s₁ hH hP₁ e he g a hx hι
  have hs := IsUWeilPair.isUSplitting hP.weil
  have hstd : IsStd B.ψ := hP.base.std
  have hc : ∀ t : E, cA σ (inclR (F := F) (AF F) t) = inclR (F := F) (AF F) (σ t) := fun t => rfl
  have h1 : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := by simp [incM]
  have hact : ∀ w, actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) w = mat g * w := by
    intro w; simp [actAB, mat]
  have hcomp : ∀ w w' Φ, symp (cA σ) (-1) (incM F X.J) (incM F W.J) w w' = 0 →
      M.co.rho B.ψ w (M.co.rho B.ψ w' Φ) = M.co.rho B.ψ (w + w') Φ := by
    intro w w' Φ h0
    simp only [Darboux.rho]
    have hlaw : ∀ (v v' : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)) (φ : (Fin n × Fin d → AF F) → ℂ),
        schr B.ψ v (schr B.ψ v' φ) = B.ψ (⅟(2 : AF F) * (v.1 ⬝ᵥ v'.2 - v'.1 ⬝ᵥ v.2)) • schr B.ψ (v + v') φ := by
      intro v v' φ
      funext x
      simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add,
        add_assoc, add_dotProduct, dotProduct_add]
      congr 2
      linear_combination (-(v.1 ⬝ᵥ v'.2)) * invOf_mul_self (2 : AF F)
    rw [hlaw, ← M.co.form, h0, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add]
  have hcol : ∀ m, ∑ i, ∑ k, H.ι i m * (X.J i k * σ (H.x k)) = 0 := by
    intro m
    have h := (hH.orth (Pi.single m 1)).1
    simp only [form, Matrix.mulVec_single_one, dotProduct, Matrix.mulVec] at h
    simpa [Finset.mul_sum, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_mul] using h
  have hperp : ∀ (z : Matrix (Fin n₁) (Fin d) (AE F E)) (q : Fin d → AE F E),
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
    intro z q
    have hinner : ∀ j, ∑ i, ∑ k, (incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k) = 0 := by
      intro j
      have e1 : ∀ i k, (incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k) =
          ∑ m, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) := by
        intro i k
        rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [incM, incV, Matrix.map_apply, hc, map_mul]
        ring
      simp_rw [e1]
      calc _ = ∑ i, ∑ m, ∑ k, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ m, ∑ i, ∑ k, z m j * inclR (F := F) (AF F) (H.ι i m * (X.J i k * σ (H.x k))) := Finset.sum_comm
        _ = ∑ m, z m j * inclR (F := F) (AF F) (∑ i, ∑ k, H.ι i m * (X.J i k * σ (H.x k))) := by
            simp [map_sum, Finset.mul_sum]
        _ = 0 := Finset.sum_eq_zero fun m _ => by rw [hcol m, map_zero, mul_zero]
    have hT : hTens (cA σ) (incM F X.J) (incM F W.J) (incM F H.ι * z) (Matrix.vecMulVec (incV F H.x) q) = 0 := by
      unfold hTens
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have e2 : ∀ i k, ∑ l, (incM F H.ι * z) i j * incM F X.J i k * incM F W.J j l *
          cA σ (Matrix.vecMulVec (incV F H.x) q k l) =
          ((incM F H.ι * z) i j * incM F X.J i k * cA σ (incV F H.x k)) * ∑ l, incM F W.J j l * cA σ (q l) := by
        intro i k
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Matrix.vecMulVec_apply, map_mul]
        ring
      simp_rw [e2, ← Finset.sum_mul, hinner j, zero_mul]
    simp [symp, hT]
  choose β hβ using fun j : Fin n₁ => hι (Pi.single j 1)
  have hgι : mat g * incM F H.ι = incM F H.ι + Matrix.vecMulVec (incV F H.x) β := by
    ext i j
    have h := congrFun (hβ j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    simpa [Matrix.vecMulVec_apply, mul_comm] using h
  refine ⟨fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_⟩
  · have hΨ := hs.pres (g, 1) Φ hΦ
    rw [hs.impl (g, 1) _ Φ hΦ, hact]
    have hw : mat g * (incM F H.ι * z * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ) =
        incM F H.ι * z + Matrix.vecMulVec (incV F H.x) (β ᵥ* z) := by
      rw [h1, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, hgι, Matrix.add_mul]
      congr 1
      ext i j
      simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, mul_assoc]
    have hh := he.Heisenberg₂ z _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd (Matrix.vecMulVec (incV F H.x) (β ᵥ* z)) _ hΨ)
    rw [h1, Matrix.transpose_one, Matrix.mul_one] at hh
    rw [hw, ← hcomp _ _ _ (hperp z _), hh, he.inv _ ⟨_, rfl⟩ _ hΨ]
  · obtain ⟨q, rfl⟩ := hu
    have hΨ := hs.pres (g, 1) Φ hΦ
    rw [hs.impl (g, 1) _ Φ hΦ, hact, Matrix.mul_vecMulVec, hx]
    refine he.inv _ ⟨a • q, ?_⟩ _ hΨ
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring

end GlobalTheory.MixXUnip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.HTensSplitPair

theorem piW_cA_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ w) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem piW_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) (e : E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (inclR (F := F) (AF F) e) = τ e := by
  first
  | exact @_root_.GlobalTheory.ProjectionInclusion.proj_incl
  | exact _root_.GlobalTheory.ProjectionInclusion.proj_incl
  | (apply _root_.GlobalTheory.ProjectionInclusion.proj_incl <;> assumption)
  | (intros; apply _root_.GlobalTheory.ProjectionInclusion.proj_incl <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ProjectionInclusion.proj_incl <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ProjectionInclusion.proj_incl ..)

theorem hTens_split_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (τ : E →ₐ[F] Fv F v) {m n : ℕ} (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E), (∀ i j, σ (JA j i) = JA i j) → (∀ i j, σ (JB j i) = -JB i j) → ∀ (x u : Matrix (Fin m) (Fin n) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = 0 → u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) (GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JA) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JB) x u) = ∑ k, ∑ l, (-(JA.map τ * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) * (JB.map τ)ᵀ)) k l * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) k l := by
  first
  | exact @_root_.GlobalTheory.FourSumComposition.main
  | exact _root_.GlobalTheory.FourSumComposition.main
  | (apply _root_.GlobalTheory.FourSumComposition.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FourSumComposition.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FourSumComposition.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FourSumComposition.main ..)

end GlobalTheory.HTensSplitPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianWittIndexEqZeroDefiniteBottom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

namespace GlobalTheory.BottomWitt

theorem wittIndex_eq_zero :
    GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, wittIndex WW = 0 := by
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X h _
  exact GlobalTheory.Cusp.wittIndex_eq_zero_iff_isAniso.2 (GlobalTheory.Mem.ColAd.isAniso_of_gram h.stdW.1)

end GlobalTheory.BottomWitt
end

