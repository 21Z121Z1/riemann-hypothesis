import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0811
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0069
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0812
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0039
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0070
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0028
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0810
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0008
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.HoweDualityUnramifiedAllPlaces
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0066
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0049
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0011
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0052

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.AdelicStabilizerFiniteOfThetaSubgroup
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.StabFinAdelic
theorem stabilizer_kappa_of_isThetaSubgroup : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (X : HSp D) (a a' : ℕ) (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ)
    (N' : Submodule ℂ ((Fin a' × Fin (a + a') → AF D.host.F) → ℂ)),
    IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → ∀ g ∈ GfC X, ∀ Φ ∈ N', om' (1, kapX X e hJ g) Φ ∈ N' := by
  classical
  intro hP D X a a' e Bs Γ Xc om om' hT hJ N' hN g hg Φ hΦ
  have hinf := GlobalTheory.InfKill.smul_mat_kapX_sub_one D X e hJ g hg
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.T.spherical_vector_fixes_vacua hP _ _ _ Bs _ _ Γ Xc om om' hT
  have hfix : ∀ Ψ ∈ algD Γ.M' Bs.ψ Bs.emb, ∃ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F), ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F),
      T ⊆ S → S₀ ⊆ S → ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J,
      (∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
      (∀ w ∈ S, ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin D.host.F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V Γ.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V Γ.W w) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V' Γ.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V' Γ.W w) →
      om' (1, k) Ψ = Ψ := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, φ, -, hφ, hcof, rfl⟩ := hx
      refine ⟨hcof.toFinset, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => ?_⟩
      refine (hS₀ S hS₀S k hk1 hk2 hk3 hk4).2 f φ hφ fun w hw => ?_
      by_contra hne
      exact hw (hTS (Set.Finite.mem_toFinset _ |>.2 hne))
    | zero => exact ⟨∅, fun _ _ _ k _ _ _ _ => map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨T₁, h₁⟩ := hx
      obtain ⟨T₂, h₂⟩ := hy
      refine ⟨T₁ ∪ T₂, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => ?_⟩
      rw [map_add, h₁ S (Finset.union_subset_left hTS) hS₀S k hk1 hk2 hk3 hk4,
        h₂ S (Finset.union_subset_right hTS) hS₀S k hk1 hk2 hk3 hk4]
    | smul c x _ hx =>
      obtain ⟨T, hT'⟩ := hx
      exact ⟨T, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => by rw [map_smul, hT' S hTS hS₀S k hk1 hk2 hk3 hk4]⟩
  obtain ⟨T, hTfix⟩ := hfix Φ (hN.le hΦ)
  obtain ⟨S, l, k, hTS, hl, hprod, hkinf, hkS, hkV, hkV'⟩ := GlobalTheory.T.exists_adelicUnitary_prod_localPoints_mul_latticeStabilizer _ _ _ Bs _ _ Γ hT.geo _ hinf (T ∪ S₀)
  have hk : om' (1, k) Φ = Φ :=
    hTfix S (Finset.union_subset_left hTS) (Finset.union_subset_right hTS) k hkinf hkS hkV hkV'
  have split' : ∀ (x y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J) Ψ, om' (1, x * y) Ψ = om' (1, x) (om' (1, y) Ψ) := by
    intro x y Ψ
    rw [show ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ l' : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J),
      (∀ x ∈ l', x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F x.1)) →
      ∀ Ψ ∈ N', om' (1, (l'.map Prod.snd).prod) Ψ ∈ N' := by
    intro l'
    induction l' with
    | nil =>
      intro _ Ψ hΨ
      simp only [List.map_nil, List.prod_nil]
      rw [Prod.mk_one_one, map_one]
      exact hΨ
    | cons x l' ih =>
      intro hx Ψ hΨ
      simp only [List.map_cons, List.prod_cons]
      rw [split']
      exact hN.stabFin x.1 x.2 (hx x List.mem_cons_self) _
        (ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) Ψ hΨ)
  rw [hprod, split', hk]
  exact key l (fun x hx => (hl x hx).2) Φ hΦ
end GlobalTheory.StabFinAdelic
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_stabilizer_finite_of_theta_subgroup : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (X : HSp D) (a a' : ℕ) (e : Fin X.rank ≃ Fin (a + a'))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ (hJ : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ)
    (N' : Submodule ℂ ((Fin a' × Fin (a + a') → AF D.host.F) → ℂ)),
    IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N' → ∀ g ∈ GfC X, ∀ Φ ∈ N', om' (1, kapX X e hJ g) Φ ∈ N' := by
  first | exact @_root_.GlobalTheory.StabFinAdelic.stabilizer_kappa_of_isThetaSubgroup | exact _root_.GlobalTheory.StabFinAdelic.stabilizer_kappa_of_isThetaSubgroup | (intros; apply _root_.GlobalTheory.StabFinAdelic.stabilizer_kappa_of_isThetaSubgroup <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomFieldIsNumberField
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.RowEx.BotField
theorem sums_mem_bottomField (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) {D : D7} {T : Type} [Finite T] {L : LevCh D T}
    {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}
    (hL : L.Is μ₀) (hX : IsBottomTri W i j X) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ SumsIn W (algebraMap M ℂ) X := by
  obtain ⟨M₁, h₁, Ω, hΩ, e₁⟩ := field_of_gens (fun t h k => X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h)
    (GfC WW : Set (GA D WW)) (_root_.GlobalTheory.T.bottom_spanned_by_classSums hP hI hL hX) (_root_.GlobalTheory.T.bottom_classSums_algebraic hP hI hL hX)
  obtain ⟨M₂, h₂, Ω', hΩ', e₂⟩ := field_of_gens (fun t h k => X.I' W.ψ W.θ t (MvPolynomial.monomial k 1) h)
    (GfC WW : Set (GA D WW)) (_root_.GlobalTheory.T.bottom_spanned_by_twistedClassSums hP hI hL hX) (_root_.GlobalTheory.T.bottom_twistedClassSums_algebraic hP hI hL hX)
  refine ⟨M₁ ⊔ M₂, inferInstance, Ω, Ω', hΩ, hΩ', fun t h hh => ⟨fun k _ => ?_, fun k _ => ?_⟩⟩
  · exact ⟨⟨_, (le_sup_left : M₁ ≤ _) (e₁ t h hh k)⟩, rfl⟩
  · exact ⟨⟨_, (le_sup_right : M₂ ≤ _) (e₂ t h hh k)⟩, rfl⟩
end GlobalTheory.RowEx.BotField
theorem GlobalTheory.RowEx.bottomField_isNumberField : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → NFBot := by
  intro hP hI
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  haveI : Finite T := hS.fin
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hex : ∀ ij : Fin D.R.m × Fin D.R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
      ∃ (A₁ A₂ WW : HSp D) (X : Tri T A₁ A₂ WW), IsBottomTri ch.W ij.1 ij.2 X ∧ SumsIn ch.W (algebraMap M ℂ) X := by
    intro ij
    obtain ⟨A₁, A₂, WW, X, hX⟩ := exists_bottomTri hL ch.G ch.W ij.1 ij.2
    obtain ⟨M, hM, hs⟩ := _root_.GlobalTheory.RowEx.BotField.sums_mem_bottomField hP hI hL hX
    exact ⟨M, hM, A₁, A₂, WW, X, hX, hs⟩
  choose M hM hB using hex
  haveI := hM
  refine ⟨⨆ ij, M ij, IntermediateField.finiteDimensional_iSup_of_finite, fun i j => ?_⟩
  obtain ⟨A₁, A₂, WW, X, hX, hs⟩ := hB (i, j)
  refine ⟨A₁, A₂, WW, X, hX, GlobalTheory.RowEx.BotField.sumsIn_mono hs ?_⟩
  rintro _ ⟨z, rfl⟩
  exact ⟨⟨z, (le_iSup M (i, j) : M (i, j) ≤ _) z.2⟩, rfl⟩
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteAdelicStabilizerFixesKappa
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.StabFinAdelic
theorem kappa_stabilized_of_isStabilizedW : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N, GlobalTheory.CoinvKer.IsStabW om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → ∀ g ∈ GfC X, ∀ ΦD ∈ N, om (1, kapX X e hO.JX g) ΦD ∈ N := by
  classical
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ hO hT Pi rf rl p p' _ N hN g hg Φ hΦ
  have hinf := GlobalTheory.InfKill.smul_mat_kapX_sub_one D X e hO.JX g hg
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.T.spherical_vector_fixes_vacua hP _ _ _ Bs _ _ Γ Xc om om' hT
  have hfix : ∀ Ψ ∈ algD Γ.M Bs.ψ Bs.emb, ∃ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F), ∀ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F),
      T ⊆ S → S₀ ⊆ S → ∀ k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J,
      (∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
      (∀ w ∈ S, ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin D.host.F w) u → u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k - 1) = 0) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V Γ.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V Γ.W w) →
      (∀ w ∉ S, ∀ γ, γ * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k)ᵀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V' Γ.W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV Γ.V' Γ.W w) →
      om (1, k) Ψ = Ψ := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, φ, -, hφ, hcof, rfl⟩ := hx
      refine ⟨hcof.toFinset, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => ?_⟩
      refine (hS₀ S hS₀S k hk1 hk2 hk3 hk4).1 f φ hφ fun w hw => ?_
      by_contra hne
      exact hw (hTS (Set.Finite.mem_toFinset _ |>.2 hne))
    | zero => exact ⟨∅, fun _ _ _ k _ _ _ _ => map_zero _⟩
    | add x y _ _ hx hy =>
      obtain ⟨T₁, h₁⟩ := hx
      obtain ⟨T₂, h₂⟩ := hy
      refine ⟨T₁ ∪ T₂, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => ?_⟩
      rw [map_add, h₁ S (Finset.union_subset_left hTS) hS₀S k hk1 hk2 hk3 hk4,
        h₂ S (Finset.union_subset_right hTS) hS₀S k hk1 hk2 hk3 hk4]
    | smul c x _ hx =>
      obtain ⟨T, hT'⟩ := hx
      exact ⟨T, fun S hTS hS₀S k hk1 hk2 hk3 hk4 => by rw [map_smul, hT' S hTS hS₀S k hk1 hk2 hk3 hk4]⟩
  obtain ⟨T, hTfix⟩ := hfix Φ (hN.1 hΦ)
  obtain ⟨S, l, k, hTS, hl, hprod, hkinf, hkS, hkV, hkV'⟩ := GlobalTheory.T.exists_adelicUnitary_prod_localPoints_mul_latticeStabilizer _ _ _ Bs _ _ Γ hT.geo _ hinf (T ∪ S₀)
  have hk : om (1, k) Φ = Φ :=
    hTfix S (Finset.union_subset_left hTS) (Finset.union_subset_right hTS) k hkinf hkS hkV hkV'
  have split' : ∀ (x y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J) Ψ, om (1, x * y) Ψ = om (1, x) (om (1, y) Ψ) := by
    intro x y Ψ
    rw [show ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ l' : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J),
      (∀ x ∈ l', x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F x.1)) →
      ∀ Ψ ∈ N, om (1, (l'.map Prod.snd).prod) Ψ ∈ N := by
    intro l'
    induction l' with
    | nil =>
      intro _ Ψ hΨ
      simp only [List.map_nil, List.prod_nil]
      rw [Prod.mk_one_one, map_one]
      exact hΨ
    | cons x l' ih =>
      intro hx Ψ hΨ
      simp only [List.map_cons, List.prod_cons]
      rw [split']
      exact hN.2.1 x.1 x.2 (hx x List.mem_cons_self) _
        (ih (fun y hy => hx y (List.mem_cons_of_mem _ hy)) Ψ hΨ)
  rw [hprod, split', hk]
  exact key l (fun x hx => (hl x hx).2) Φ hΦ
end GlobalTheory.StabFinAdelic
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_stabilizer_fixes_kappa : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ N, GlobalTheory.CoinvKer.IsStabW om Bs.emb (algD Γ.M Bs.ψ Bs.emb) N → ∀ g ∈ GfC X, ∀ ΦD ∈ N, om (1, kapX X e hO.JX g) ΦD ∈ N := by
  first | exact @_root_.GlobalTheory.StabFinAdelic.kappa_stabilized_of_isStabilizedW | exact _root_.GlobalTheory.StabFinAdelic.kappa_stabilized_of_isStabilizedW | (intros; apply _root_.GlobalTheory.StabFinAdelic.kappa_stabilized_of_isStabilizedW <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FlipSequenceStartCondition
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FlipStart
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
end GlobalTheory.FlipStart
open GlobalTheory.FlipStart in
theorem GlobalTheory.FlipStart.flipSequence_start_condition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m), GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧ ∀ M : Vol ch.G, M.Is t → ∀ y, TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) := by
  intro hP hC
  obtain ⟨a, h⟩ := ((_root_.GlobalTheory.T.flipSequence_column_succ hP hC).and (_root_.GlobalTheory.T.twisted_theta_tower_first_occurrence_exists hP hC)).and (_root_.GlobalTheory.T.twisted_theta_first_occurrence_finite_swapped_pair hP)
  refine ⟨a, fun ε CF hCF => ?_⟩
  obtain ⟨x, h⟩ := h ε CF hCF
  refine ⟨x, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j => ?_⟩
  obtain ⟨⟨hcol, hrow⟩, hfin⟩ := h D large₂ e hx Γ Pl0 T A Ks R F s ch i j
  obtain ⟨q, hq⟩ := exists_chainPols ch
  refine ⟨Finsupp.single (gPol ch.ρ q) 1, fun t => ?_⟩
  obtain ⟨f, hf⟩ := exists_chainVecs ch t
  obtain ⟨z, hz, hrep⟩ := hfin t f hf
  refine ⟨z, hz, fun Φ => ⟨Finsupp.single (givenFin ch.W t f Φ) (z : ℂ), hrep Φ, fun M hM y => ?_⟩⟩
  obtain ⟨hc1, hc2⟩ := hcol t f q hf hq M hM y
  obtain ⟨hr1, hr2⟩ := hrow t Φ M hM y
  rw [tensE_single]
  refine ⟨fun d hd => ?_, ?_⟩
  · have hd' := Finsupp.support_single_subset hd
    rw [Finset.mem_singleton] at hd'
    subst hd'
    rw [zip_given]
    refine (pathConv_comp ch.W M _ _ _ _ _).2 ⟨hc1, ?_⟩
    rw [hc2]
    exact hr1
  · rw [liftT_single, zip_given]
    unfold givenPath
    rw [pathLift_comp, hc2, ← hr2, smul_smul, inv_mul_cancel₀ (Units.ne_zero z), one_smul]
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipSequence_initial_term : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∃ Pg : GlobalTheory.FlipRun.PolE ch.G →₀ ℂ, ∀ t : T, ∃ z : ℂˣ, z ∈ GlobalTheory.RowClaim.xiVals R.toLevCh t ∧ ∀ Φ : ch.G.Datum, ∃ τg : TotT ch.G (GlobalTheory.FunObj.givenPath t D.R.m), GlobalTheory.FlipRun.RepFin ch.S.B ch.rm t (GlobalTheory.FunObj.givenPath t D.R.m) τg (fun w => (givenStage t w ch.S.B Φ).tensor) ∧ ∀ M : Vol ch.G, M.Is t → ∀ y, TotConv ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) ∧ thetaChi ch.W ch.M ch.ρ Φ (ch.cv.lift t y) = (z : ℂ)⁻¹ • liftT ch.W M _ (GlobalTheory.FlipRun.tensE ch.W _ Pg τg) (GlobalTheory.RowClaim.formTop ch t y) := by
  first | exact @_root_.GlobalTheory.FlipStart.flipSequence_start_condition | exact _root_.GlobalTheory.FlipStart.flipSequence_start_condition | (intros; apply _root_.GlobalTheory.FlipStart.flipSequence_start_condition <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoweSwap
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix
noncomputable section
namespace UpperTheory.Lit.HoweDuality
open GlobalTheory.HoweGlobalPair
theorem stageV_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), Xc.T ⊆ T →
        GlobalTheory.HoweGlobal.algAt G.M Bs.ψ Bs.emb T ≤ N ∨
          ∀ Φ ∈ N, Φ ∈ GlobalTheory.HoweGlobal.algAt G.M Bs.ψ Bs.emb T → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf Φ 0 := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN T hT
  classical
  obtain ⟨L, hL, hrange⟩ := GlobalTheory.T.exists_linear_tensor_polyVacuum_pureTensors G.M Bs.ψ Bs.emb hM.triple.geo.hM.std T
  have hloc := _root_.GlobalTheory.T.global_howe_transfer_real_place hP F E σ Bs a a' G Xc om om' R Rf hM hreal
  have hfl := fun v => locV hM v
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.T.global_howe_tensor_product_transfer hP F E σ Bs a a' G Xc om om' R Rf hM N hN T L hL
  have key := tens (ι := T) (M₀ := ↥(G.M.Pol Bs.ψ Bs.emb))
    (M := fun v : T => ↥(SB (Fin a × Fin (a + a') → Fv F v.1)))
    (GlobalTheory.HoweGlobal.opInf Bs G om) (fun v => GlobalTheory.HoweGlobal.opFin G om v.1)
    (GlobalTheory.HoweGlobal.relInf Bs G om) (fun v => GlobalTheory.HoweGlobal.relFin G om v.1)
    (R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype) (fun v => Rf.p v.1 ∘ₗ (SB _).subtype)
    hloc.1 (fun v => GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le F _ v.1) hloc.2.1 hloc.2.2.1 hloc.2.2.2.1 hloc.2.2.2.2
    (fun v => (hfl v.1).1) (fun v => (kerV hM v.1).2.1) (fun v => (hfl v.1).2) (fun v => (kerV hM v.1).2.2.2)
    (N.comap L) h1 h2 h3 h4
  rcases key with htop | hker
  · left
    intro Φ hΦ
    obtain ⟨t, rfl⟩ := hrange hΦ
    have ht : t ∈ N.comap L := by rw [htop]; exact Submodule.mem_top
    exact ht
  · right
    intro Φ hΦN hΦT
    obtain ⟨t, rfl⟩ := hrange hΦT
    have ht0 := hker (show t ∈ N.comap L from hΦN)
    obtain ⟨m, f, φ, rfl⟩ := GlobalTheory.HoweGlobal.decomp t
    refine ⟨T, hT, m, 0, fun j => ((f j : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F (Fin a × Fin (a + a'))),
      fun j v => if h : v ∈ T then ((φ j ⟨v, h⟩ : ↥(SB _)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) else G.M.vac v,
      Fin.elim0, Fin.elim0, fun j => ⟨(f j).2, fun v => ?_, fun v hv => by simp only [dif_neg hv]⟩, fun j => Fin.elim0 j, ?_, ?_, ?_⟩
    · by_cases h : v ∈ T
      · simp only [dif_pos h]; exact (φ j ⟨v, h⟩).2
      · simp only [dif_neg h]; exact (hM.triple.geo.hM.vac v).1
    · rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hL _ _ _ (fun v h => by simp only [dif_pos h]) (fun v h => by simp only [dif_neg h])
    · simp
    · rw [LinearMap.mem_ker, map_sum] at ht0
      rw [Fin.sum_univ_zero, ← ht0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod]
      simp
theorem allV_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M Bs.ψ Bs.emb om N →
        N ≠ G.M.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p f = 0) →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
      N ≠ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb →
      ∀ ΦD ∈ N, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf ΦD 0 := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN hne ΦD hΦ
  by_contra hc
  obtain ⟨T, hT, hΦT⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M Bs.ψ Bs.emb (hN.1.1 hΦ) Xc.T
  apply hne
  refine le_antisymm hN.1.1 fun Ψ hΨ => ?_
  obtain ⟨T', hT', hΨT'⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M Bs.ψ Bs.emb hΨ T
  rcases _root_.UpperTheory.Lit.HoweDuality.stageV_alt hP F E σ Bs a a' G Xc om om' R Rf hM hreal N hN T' (hT.trans hT') with h | h
  · exact h hΨT'
  · exact absurd (h ΦD hΦ (GlobalTheory.HoweGlobal.algAt_mono G.M Bs.ψ Bs.emb hT' hΦT)) hc
theorem twisted_theta_kernel_condition : _root_.GlobalTheory.T.TwistedThetaKernelCondition := fun hR hP F E _ _ _ _ _ σ Bs a a' G Xc om om' _ R Rf hM N hN hne =>
  _root_.UpperTheory.Lit.HoweDuality.allV_alt hP F E σ Bs a a' G Xc om om' R Rf hM (GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift hR F E σ Bs a a' G Xc om om' R Rf hM) N hN hne
theorem twisted_theta_jet_condition : _root_.GlobalTheory.T.TwistedThetaJetCondition := fun hR _ F E _ _ _ _ _ σ a a' Bs G Xc om om' R Rf hM N hN hne =>
  allVp F E σ Bs a a' G Xc om om' R Rf hM (GlobalTheory.T.howeDuality_realPlaces_trivialChar_fockLift_smallPair hR F E σ Bs a a' G Xc om om' R Rf hM) N hN hne
end UpperTheory.Lit.HoweDuality
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LatticeVacuumFixedOutsideFiniteSet
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.LatStabVac
theorem lattice_vacuum_fixed_outside_finite_set : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ v ∉ S₀,
      (∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v)) ∧
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT
  classical
  obtain ⟨S₁, hS₁⟩ := _root_.GlobalTheory.T.split_spherical_left_fixes_vacuum hP F E σ B a a' G X om om' hT
  obtain ⟨S₂, hS₂⟩ := _root_.GlobalTheory.T.split_vprime_stabilizer_fixes_vacuum hP F E σ B a a' G X om om' hT
  refine ⟨X.T ∪ S₁ ∪ S₂, fun v hv => ?_⟩
  simp only [Finset.mem_union, not_or] at hv
  obtain ⟨⟨hvT, hv₁⟩, hv₂⟩ := hv
  rcases GlobalTheory.KFinLoc.split_or_inert F E σ B hT.base v with hs | ⟨w, hw⟩
  · exact ⟨hS₁ v hv₁ hs, hS₂ v hv₂ hs⟩
  · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · exact GlobalTheory.T.inert_place_both_stabilisers_fix_vacuum F E σ B a a' G X om om' hT v w hw hvT k hk 1 (GlobalTheory.InertSph.one_mem_KAt σ G.W v)
    · exact GlobalTheory.T.inertPlace_stabilizer_fixes_vacuum_left F E σ B a a' G X om om' hT v w hw hvT k hk
end GlobalTheory.LatStabVac
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stabilizer_fixes_vacuum_vector : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∃ S₀ : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ v ∉ S₀,
      (∀ k ∈ GlobalTheory.InertSph.KAt σ G.V v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (k, 1)) (G.M.vac v) (G.M.vac v)) ∧
      ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  first | exact @_root_.GlobalTheory.LatStabVac.lattice_vacuum_fixed_outside_finite_set | exact _root_.GlobalTheory.LatStabVac.lattice_vacuum_fixed_outside_finite_set | (intros; apply _root_.GlobalTheory.LatStabVac.lattice_vacuum_fixed_outside_finite_set <;> assumption)
end
end

