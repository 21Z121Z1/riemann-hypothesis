import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0595
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0619
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0704
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0819
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0808
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0812
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0615
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0539
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0536
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicVectorsCorrespondSchrodingerThetaMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.SquareAgree

theorem isDatum_zero_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z) :
    IsDatum M ψ crd 0 0 := by
  refine ⟨zero_mem _, fun u => ?_⟩
  simp [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

theorem isDatum_smul_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ) {Z : Type} (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z)
    {Φ : (Fin n × Fin d → AF F) → ℂ} {f : Z → ℂ} (h : IsDatum M ψ crd Φ f) (c : ℂ) :
    IsDatum M ψ crd (c • Φ) (c • f) := by
  refine ⟨Submodule.smul_mem _ _ h.1, fun u => ?_⟩
  rw [Pi.smul_apply, ← h.2 u]
  simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun η => mul_left_comm _ _ _

theorem algVec_correspond : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      (∀ Φ ∈ algF ψ θ ε A B, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD Φ) ∧
      ∀ ΦD ∈ algD M Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ ε A B, IsDatum M ψ cS ΦD Φ := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hBs.std
  have hadd : ∀ {Φ Φ' : (Fin S.rank × Fin d → AF D.host.F) → ℂ} {f f' : WO S X → ℂ},
      IsDatum M ψ cS Φ f → IsDatum M ψ cS Φ' f' → IsDatum M ψ cS (Φ + Φ') (f + f') :=
    fun h h' => GlobalTheory.T.isSchrodingerThetaDatum_add_adelicSchwartz M ψ hstd cS _ _ _ _ h h'

  set Aop := aPlusAll (heisO ψ (sgn ε S) X) θ (fun τ => cplxO ((frSgn ε A).cart τ) (B.cart τ)) A.onb B.onb with hAop
  have hfock : ∀ f P, fockF ψ θ ε A B f P = pureTensorL Aop f P := fun f P => rfl
  have step : ∀ g : WO S X → ℂ, (∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD g) →
      ∀ k, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD (Aop k g) := by
    rintro g ⟨ΦD, hD, hd⟩ k
    obtain ⟨a, ha, h1⟩ := GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS ΦD hD g hd k.1
      (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2)
    obtain ⟨b, hb, h2⟩ := GlobalTheory.T.realPlaceHeisenbergDeriv_thetaTransform_algebraicDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS ΦD hD g hd k.1
      (cplxO ((frSgn ε A).cart k.1) (B.cart k.1) (unitMap (A.onb k.1) (B.onb k.1) k.2.1 k.2.2))
    refine ⟨((fockScale D k.1 : ℂ)⁻¹) • (a + (-Complex.I) • b),
      Submodule.smul_mem _ _ (add_mem ha (Submodule.smul_mem _ _ hb)), ?_⟩
    have e1 := isDatum_smul_smul M ψ cS (hadd h1 (isDatum_smul_smul M ψ cS h2 (-Complex.I))) ((fockScale D k.1 : ℂ)⁻¹)
    convert e1 using 1
    simp only [hAop, aPlusAll, aPlus, crea, sub_eq_add_neg, neg_smul]
  have gen : ∀ f, IsFinF ψ θ ε A B f → ∀ P, ∃ ΦD ∈ algD M Bs.ψ Bs.emb, IsDatum M ψ cS ΦD (fockF ψ θ ε A B f P) := by
    intro f hf P
    have h0 := GlobalTheory.T.exists_algebraicDatum_thetaTransform_eq D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS f hf
    have hl : ∀ l : List (FVar D X.rank S.rank), ∃ ΦD ∈ algD M Bs.ψ Bs.emb,
        IsDatum M ψ cS ΦD (l.foldr (fun i g => Aop i g) f) := by
      intro l
      induction l with
      | nil => exact h0
      | cons k l ih => exact step _ ih k
    rw [hfock]
    induction P using MvPolynomial.induction_on' with
    | monomial u a =>
      have em : MvPolynomial.monomial u a = a • MvPolynomial.basisMonomials (FVar D X.rank S.rank) ℂ u := by
        rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      obtain ⟨ΦD, hD, hd⟩ := hl (Multiset.toList (Finsupp.toMultiset u))
      refine ⟨a • ΦD, Submodule.smul_mem _ _ hD, ?_⟩
      rw [em, map_smul]
      unfold pureTensorL
      rw [Module.Basis.constr_basis]
      exact isDatum_smul_smul M ψ cS hd a
    | add p q hp hq =>
      obtain ⟨a, ha, h1⟩ := hp
      obtain ⟨b, hb, h2⟩ := hq
      exact ⟨a + b, add_mem ha hb, by rw [map_add]; exact hadd h1 h2⟩
  have fin_mem : ∀ f, IsFinF ψ θ ε A B f → f ∈ algF ψ θ ε A B := by
    intro f hf
    refine Submodule.subset_span ⟨f, 1, hf, ?_⟩
    have e1 : (1 : MvPolynomial (FVar D X.rank S.rank) ℂ) = MvPolynomial.basisMonomials (FVar D X.rank S.rank) ℂ 0 := by
      rw [MvPolynomial.coe_basisMonomials]; rfl
    rw [hfock, e1]
    unfold pureTensorL
    rw [Module.Basis.constr_basis]
    simp [opPow]
  refine ⟨fun Φ hΦ => ?_, fun ΦD hΦD => ?_⟩
  · induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact gen f hf P
    | zero => exact ⟨0, zero_mem _, isDatum_zero_zero M ψ cS⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, h1⟩ := hx
      obtain ⟨b, hb, h2⟩ := hy
      exact ⟨a + b, add_mem ha hb, hadd h1 h2⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, h1⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, isDatum_smul_smul M ψ cS h1 c⟩
  · have pure_add : ∀ (g g' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g + g') φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g' φ := by
      intro g g' φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
    have pure_smul : ∀ (c : ℂ) (g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • g) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
      intro c g φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
    have pure_zero : ∀ (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) φ = 0 := by
      intro φ; funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    let N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin S.rank × Fin d)) :=
      { carrier := {g | ∀ (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → v.adicCompletion D.host.F) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
          ∃ f ∈ algF ψ θ ε A B, IsDatum M ψ cS (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) f}
        zero_mem' := fun φ _ _ => ⟨0, zero_mem _, by rw [pure_zero]; exact isDatum_zero_zero M ψ cS⟩
        add_mem' := by
          intro g g' hg hg' φ h1 h2
          obtain ⟨a, ha, d1⟩ := hg φ h1 h2
          obtain ⟨b, hb, d2⟩ := hg' φ h1 h2
          exact ⟨a + b, add_mem ha hb, by rw [pure_add]; exact hadd d1 d2⟩
        smul_mem' := by
          intro c g hg φ h1 h2
          obtain ⟨a, ha, d1⟩ := hg φ h1 h2
          exact ⟨c • a, Submodule.smul_mem _ _ ha, by rw [pure_smul]; exact isDatum_smul_smul M ψ cS d1 c⟩ }
    have hPol : M.Pol Bs.ψ Bs.emb ≤ N := by
      refine sInf_le ⟨fun g₀ hg₀ φ h1 h2 => ?_, fun u hu g hg g₁ hg₁ φ h1 h2 => ?_⟩
      · obtain ⟨f, hf, hd⟩ := GlobalTheory.T.thetaTransform_gaussianVacuum_isFiniteDatum D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS g₀ φ hg₀ h1 h2
        exact ⟨f, fin_mem f hf, hd⟩
      · obtain ⟨f, hf, hd⟩ := hg φ h1 h2
        exact GlobalTheory.T.exists_algebraicVector_thetaTransform_heisenbergDerivative D ψ θ hθ ε S X A B e Bs hBs hψ Vs Ws r s r' s' hJ hJW hVs hWs hcart M hM cS hcS g φ h1 h2 f hf hd u hu g₁ hg₁
    induction hΦD using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, φ, hg, h1, h2, rfl⟩ := hx
      exact hPol hg φ h1 h2
    | zero => exact ⟨0, zero_mem _, isDatum_zero_zero M ψ cS⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, h1⟩ := hx
      obtain ⟨b, hb, h2⟩ := hy
      exact ⟨a + b, add_mem ha hb, hadd h1 h2⟩
    | smul c x _ hx =>
      obtain ⟨a, ha, h1⟩ := hx
      exact ⟨c • a, Submodule.smul_mem _ _ ha, isDatum_smul_smul M ψ cS h1 c⟩

end GlobalTheory.SquareAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlipOfWeilConvergenceAndTheta
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipRun

variable {D : D7} {T : Type}

theorem passesThrough_of_canFlip {x : ℕ × ℕ} {r : List (ℕ × ℕ)} :
    ∀ (l : List (ℕ × ℕ)) (γ : List GlobalTheory.SplitFlip.Edge), GlobalTheory.SplitFlip.CanFlip γ (l ++ x :: r) →
      GlobalTheory.SplitFlip.PassesThrough x.1 x.2 (l.foldl (fun γ y => GlobalTheory.SplitFlip.flipPath y.1 y.2 γ) γ)
  | [], γ, h => by cases h with | cons hp _ => exact hp
  | y :: l, γ, h => by
    cases h with
    | cons _ hc => exact passesThrough_of_canFlip l _ hc

theorem lt_of_mem_flipOrder {m : ℕ} {x : ℕ × ℕ} (h : x ∈ flipOrder m) : x.1 < m ∧ x.2 < m := by
  simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, j, hj, rfl⟩ := h
  exact ⟨hi, hj⟩

theorem prod_map_range {M : Type*} [CommMonoid M] (f : ℕ → M) : ∀ n, ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.prod_append, prod_map_range f n, Finset.prod_range_succ]; simp

theorem prod_flipOrder {M : Type*} [CommMonoid M] (m : ℕ) (f : ℕ × ℕ → M) :
    ((flipOrder m).map f).prod = ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m, f (i, j) := by
  have : ∀ l : List ℕ, ((l.flatMap fun i => (List.range m).map fun j => (i, j)).map f).prod =
      (l.map fun i => ((List.range m).map fun j => f (i, j)).prod).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih, List.map_map, Function.comp_def]
  rw [flipOrder, this, prod_map_range]
  exact Finset.prod_congr rfl fun i _ => prod_map_range _ _

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

set_option maxHeartbeats 4000000 in

theorem flipAt_of (hL : R.toLevCh.Is A.μ0) (ch : Choice R)
    (hA : ∀ (t : T) (i j : Fin D.R.m), CommutesWith ch.W ch.S.B ch.rm t i j (ch.c i j t))
    (hB : ∀ (t : T) (M : Vol ch.G), M.Is t → GlobalTheory.FlipRun.CuspStep ch.W M ch.rm t)
    (hC : ∀ (t : T) (y : (R.HX t).H), GlobalTheory.FlipRun.IsCuspListed ch.W.θ (.grid 0 D.R.m) (GlobalTheory.RowClaim.formTop ch t y))
    (hD : ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum,
        ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m),
          GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧
          ∀ M : Vol ch.G, M.Is t → ∀ y,
            TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧
            thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) =
              (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y))
    (hE : ∀ (t : T) (Φ : ch.G.Datum), ∀ w ∈ locPl ch.G t, ∀ k, k ≤ D.R.m ^ 2 →
      (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w)
        ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).path
        ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).tensor)
    (hK : ∀ i j (t : T), ch.c i j t ≠ 0) : FlipAt ch := by
  obtain ⟨Pg, hPg⟩ := hD
  choose z hz hPg using hPg
  refine ⟨(GlobalTheory.FlipRun.flipsPolE ch.rm (flipOrder D.R.m) Pg).mapDomain GlobalTheory.FlipRun.toOpp, z, fun t => ⟨hz t, fun Φ => ?_⟩⟩
  obtain ⟨τg, hRg, hg⟩ := hPg t Φ
  let c' : ℕ × ℕ → ℂ := fun x => if h : x.1 < D.R.m ∧ x.2 < D.R.m then ch.c ⟨x.1, h.1⟩ ⟨x.2, h.2⟩ t else 1
  let S : ℕ → ∀ w, (locGrid ch.G t w).PiLocalization₂ := fun k w =>
    (givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)
  have hlev : ∀ k w, (S k w).level = givenLevel ch.G t w := fun k w =>
    flips_level _ _ _ _ _ _ fun _ _ => rfl
  have hpath : ∀ k w, (S k w).path =
      ((flipOrder D.R.m).take k).foldl (fun γ x => GlobalTheory.SplitFlip.flipPath x.1 x.2 γ) (GlobalTheory.SplitFlip.givenPath D.R.m) := fun k w =>
    flips_path _ _ _ _ _ _
  have hlen : (flipOrder D.R.m).length = D.R.m ^ 2 := (canFlip_flipOrder D.R.m).2.1
  have key : ∀ k, k ≤ D.R.m ^ 2 → ∃ p : Path T (.grid 0 D.R.m) (.grid D.R.m 0), GlobalTheory.FlipRun.OnGrid D.R.m t p ∧
      GlobalTheory.FlipRun.edges p = ((flipOrder D.R.m).take k).foldl (fun γ x => GlobalTheory.SplitFlip.flipPath x.1 x.2 γ)
        (GlobalTheory.SplitFlip.givenPath D.R.m) ∧
      ∃ τ : TotT ch.G p, GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t p τ (fun w => (S k w).tensor) ∧
        ∀ M : Vol ch.G, M.Is t → ∀ y,
          TotConv ch.W M p (GlobalTheory.FlipRun.tensE ch.W p (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg) τ)
            (GlobalTheory.RowClaim.formTop ch t y) ∧
          thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = ((z t : ℂ) * (((flipOrder D.R.m).take k).map c').prod)⁻¹ •
            liftT ch.W M p (GlobalTheory.FlipRun.tensE ch.W p (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg) τ)
              (GlobalTheory.RowClaim.formTop ch t y) := by
    intro k
    induction k with
    | zero =>
      intro _
      obtain ⟨⟨h1, h2⟩, -, -⟩ := GlobalTheory.T.given_opposite_gridPaths_and_determined_by_edges D.R.m t
      refine ⟨GlobalTheory.FunObj.givenPath t D.R.m, h1, by simpa using h2, τg, hRg, fun M hM y => ?_⟩
      obtain ⟨a, b⟩ := hg M hM y
      refine ⟨a, ?_⟩
      simpa [GlobalTheory.FlipRun.flipsPolE] using b
    | succ k ih =>
      intro hk
      obtain ⟨p, hp, hedge, τ, hR, hI⟩ := ih (by omega)
      have hkl : k < (flipOrder D.R.m).length := by omega
      set x := (flipOrder D.R.m)[k] with hx
      have hxm : x ∈ flipOrder D.R.m := List.getElem_mem hkl
      obtain ⟨hi, hj⟩ := lt_of_mem_flipOrder hxm
      have htake : (flipOrder D.R.m).take (k + 1) = (flipOrder D.R.m).take k ++ [x] := List.take_succ_eq_append_getElem hkl
      have hpass : GlobalTheory.SplitFlip.PassesThrough x.1 x.2 (GlobalTheory.FlipRun.edges p) := by
        rw [hedge]
        have hc := (canFlip_flipOrder D.R.m).1
        rw [← List.take_append_drop k (flipOrder D.R.m), List.drop_eq_getElem_cons hkl] at hc
        exact passesThrough_of_canFlip _ _ hc
      obtain ⟨A, Bp, rfl, hA', hB', hN, hNe⟩ := GlobalTheory.T.gridPath_cut_at_square_swap_route D.R.m t x.1 x.2 hi hj p hp hpass
      have hT : ∀ w ∈ locPl ch.G t, (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w)
          (GlobalTheory.FlipRun.edges ((A.comp (routeSmall t x.1 x.2)).comp Bp)) (S k w).tensor := fun w hw => by
        have := hE t Φ w hw k (by omega)
        rwa [hpath, ← hedge] at this
      have hS : ∀ w, (S (k + 1) w).tensor = (locGrid ch.G t w).flipTensor .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w)
          x.1 x.2 (givenLevel ch.G t w) (S k w).tensor := fun w => by
        rw [← hlev k w]
        show ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take (k + 1))).tensor = _
        rw [htake]
        simp only [GlobalTheory.SplitFlip.Grid.PiLocalization₂.flips, List.foldl_append, List.foldl_cons, List.foldl_nil]
        rfl
      have hTb : ∀ w ∈ locPl ch.G t, (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w)
          (GlobalTheory.FlipRun.edges ((A.comp (routeBig t x.1 x.2)).comp Bp))
          ((locGrid ch.G t w).flipTensor .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) x.1 x.2 (givenLevel ch.G t w)
            (S k w).tensor) := fun w hw => by
        have := hE t Φ w hw (k + 1) hk
        rw [← hS w, hNe, hedge]
        have e2 := hpath (k + 1) w
        rw [htake, List.foldl_append] at e2
        have e3 : (S (k + 1) w).path = GlobalTheory.SplitFlip.flipPath x.1 x.2
            (((flipOrder D.R.m).take k).foldl (fun γ x => GlobalTheory.SplitFlip.flipPath x.1 x.2 γ) (GlobalTheory.SplitFlip.givenPath D.R.m)) := e2
        rw [← e3]
        exact this
      obtain ⟨τ', hR', hF⟩ := GlobalTheory.T.gridSquareFlip_smallRoute_eq_inv_smul_bigRoute hL ch.W ch.S.B ch.rm t x.1 x.2 hi hj _ (hK _ _ t) (hA t ⟨x.1, hi⟩ ⟨x.2, hj⟩)
        A Bp hA' hB' (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg) τ (fun w => (S k w).tensor) hT hTb hR
      refine ⟨(A.comp (routeBig t x.1 x.2)).comp Bp, hN, ?_, τ', ?_, fun M hM y => ?_⟩
      · rw [hNe, hedge, htake, List.foldl_append]; rfl
      · have e : (fun w => (S (k + 1) w).tensor) = fun w => (locGrid ch.G t w).flipTensor .one (psiAt ch.W w) (unifAt w)
            (depthAt ch.G w) x.1 x.2 (givenLevel ch.G t w) (S k w).tensor := funext hS
        rw [e]; exact hR'
      · obtain ⟨hc1, hc2⟩ := hI M hM y
        obtain ⟨hn1, hn2⟩ := hF M hM (hB t M hM) _ (hC t y) hc1
        have ep : GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take (k + 1)) Pg =
            GlobalTheory.FlipRun.flipPolE ch.rm x.1 x.2 (GlobalTheory.FlipRun.flipsPolE ch.rm ((flipOrder D.R.m).take k) Pg) := by
          rw [htake, GlobalTheory.FlipRun.flipsPolE, GlobalTheory.FlipRun.flipsPolE, List.foldl_append]; rfl
        have ec : c' x = ch.c ⟨x.1, hi⟩ ⟨x.2, hj⟩ t := dif_pos ⟨hi, hj⟩
        rw [ep]
        refine ⟨hn1, ?_⟩
        rw [hc2, hn2, smul_smul, htake, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton, ec]
        congr 1
        exact (mul_inv _ _).symm.trans (by rw [mul_assoc])
  obtain ⟨p, hp, hedge, τ, hR, hI⟩ := key (D.R.m ^ 2) le_rfl
  have htk : (flipOrder D.R.m).take (D.R.m ^ 2) = flipOrder D.R.m := List.take_of_length_le (by rw [hlen])
  obtain ⟨-, ⟨h1, h2⟩, h3⟩ := GlobalTheory.T.given_opposite_gridPaths_and_determined_by_edges D.R.m t
  have hp' : p = oppPath t D.R.m := h3 p _ hp h1 (by rw [hedge, h2, htk]; exact (canFlip_flipOrder D.R.m).2.2)
  subst hp'
  have hTf : (fun w => (S (D.R.m ^ 2) w).tensor) = Tflip ch.W ch.S.B t Φ := by
    funext w
    show ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take (D.R.m ^ 2))).tensor = _
    rw [htk]; rfl
  rw [hTf] at hR
  obtain ⟨τ', hτ', heq⟩ := GlobalTheory.T.flippedFiniteTensor_of_representing_oppositePath ch.W ch.S.B ch.rm t Φ (GlobalTheory.FlipRun.flipsPolE ch.rm (flipOrder D.R.m) Pg) τ hR
  have hprod : ((flipOrder D.R.m).map c').prod = cTot ch t := by
    rw [prod_flipOrder, cTot, Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_range]
    exact Finset.prod_congr rfl fun j _ => dif_pos ⟨i.2, j.2⟩
  refine ⟨τ', hτ', fun M hM y => ?_⟩
  obtain ⟨hc1, hc2⟩ := hI M hM y
  rw [htk, heq] at hc1 hc2
  rw [hprod] at hc2
  exact ⟨hc1, hc2⟩

end GlobalTheory.FlipRun

open GlobalTheory.RowClaim in

theorem GlobalTheory.FlipRun.stepFlip_of : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.SquareSt.WeilConvergence →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → ConstK → StepFlip := by
  intro hP hLC hWC hTI hCK
  obtain ⟨C0, H⟩ := (((((GlobalTheory.T.weil_action_commutes_on_grid hP hWC hTI).and (GlobalTheory.T.cuspidal_flip_on_volumes hLC hP)).and
    (GlobalTheory.T.cuspidal_listed_top_forms hP)).and (GlobalTheory.T.given_path_representation_finite hP hLC)).and GlobalTheory.T.localFlipStage_isTensor_placeDepth).and hCK
  refine ⟨C0, fun ε CF h => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF h
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j => ?_⟩
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩, g⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  exact GlobalTheory.FlipRun.flipAt_of s.core.lev ch a b c d f (fun i j t => (g i j t).2)

end
end

