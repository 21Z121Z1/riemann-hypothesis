import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0441
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0376
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0380
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0753
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0386
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0391
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0684
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0440
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0078
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0744
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0756
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0725
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0561
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0388
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0750
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0635
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0499
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0555
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0553
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0754
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0532
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantExtending
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureEulerProduct
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterContinuousUnit
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.CentreChar

theorem continuous_and_norm_chz : ∀ (D : D7) (ρ : ℕ) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ,
  Continuous (chz ψ b₀) ∧ ∀ z, ‖chz ψ b₀ z‖ = 1 := fun _ _ _ hψ b₀ =>
  ⟨GlobalTheory.CompanionTheory.PcB.continuous_chz hψ b₀, GlobalTheory.CompanionTheory.PcB.chz_norm hψ b₀⟩

end GlobalTheory.CompanionTheory.CentreChar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermFiniteOfSmaller
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CTFin

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

def leftN (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) : Submodule ℂ (Sm E (r + s)) where
  carrier := {F | ∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g}
  add_mem' := fun {F G} hF hG x g => by
    change F.1 _ + G.1 _ = F.1 _ + G.1 _
    rw [hF, hG]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c F hF x g => by
    change c • F.1 _ = c • F.1 _
    rw [hF]

def vanM (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) : Submodule ℂ (Sm E (r + s)) where
  carrier := {F | ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = 0}
  add_mem' := fun {F G} hF hG m => by
    change F.1 _ + G.1 _ = 0
    rw [hF, hG, add_zero]
  zero_mem' := fun _ => rfl
  smul_mem' := fun c F hF m => by
    change c • F.1 _ = 0
    rw [hF, smul_zero]

theorem aeval_mem_Zalg {n : ℕ} {x : Module.End ℂ (Sm E n)} (hx : x ∈ Zalg E n) (q : Polynomial ℂ) :
    Polynomial.aeval x q ∈ Zalg E n := by
  rw [← Polynomial.aeval_subalgebra_coe q (Zalg E n) ⟨x, hx⟩]
  exact (Polynomial.aeval (⟨x, hx⟩ : Zalg E n) q).2

theorem cap_mem_Zalg {n : ℕ} (τ : E →+* ℂ) (u : ℂ) : cap (a := n) τ u ∈ Zalg E n :=
  Algebra.subset_adjoin ⟨τ, u, rfl⟩

theorem centre (J : Set (Module.End ℂ (Sm E (r + s)))) (hJ : Cofin J) :
    ∃ (J₁ : Set (Module.End ℂ (Sm E r))) (J₂ : Set (Module.End ℂ (Sm E s))), Cofin J₁ ∧ Cofin J₂ ∧
    (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) →
      ∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ z ∈ J₁, z G = 0) ∧
    (∀ F : Sm E (r + s), (∀ (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)), F.1 (unip x * g) = F.1 g) → (∀ z ∈ J, z F = 0) →
      ∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ z ∈ J₂, z G = 0) := by
  let W₀ : Set (Sm E (r + s)) := {F | F ∈ leftN E r s ∧ ∀ z ∈ J, z F = 0}
  have key : ∀ τ : E →+* ℂ, (∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (capR r s τ u) q F ∈ vanM E r s) ∧
      ∀ u, ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀, Polynomial.aeval (capS r s τ u) q F ∈ vanM E r s := by
    intro τ
    obtain ⟨a, a1, a2, a3⟩ := GlobalTheory.T.quantum_determinant_polynomial_coefficients (Module.End ℂ (Sm E (r + s))) r
      (fun i j : Fin r => Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s j)) (((r : ℂ) - 1) / 2)
    obtain ⟨b, b1, b2, b3⟩ := GlobalTheory.T.quantum_determinant_polynomial_coefficients (Module.End ℂ (Sm E (r + s))) s
      (fun i j : Fin s => Eop (a := r + s) τ (Fin.natAdd r i) (Fin.natAdd r j)) (((s : ℂ) - 1) / 2)
    refine GlobalTheory.T.capelli_polynomial_coefficients_ideal (Sm E (r + s)) (fun u => cap (a := r + s) τ u) (capR r s τ) (capS r s τ) (leftN E r s) (vanM E r s) W₀
      (-(s : ℂ) / 2) ((r : ℂ) / 2) r s a b (fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).1)
      (fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).2.1) (fun u v => (GlobalTheory.T.capelli_operators_commute E r s τ u v).2.2)
      (fun u F hF => (GlobalTheory.T.capelli_constant_term_vanishing E r s τ u F).2 hF) (fun u F hF => ((GlobalTheory.T.capelli_constant_term_vanishing E r s τ u F).1 hF).1)
      (fun u F hF => ((GlobalTheory.T.capelli_constant_term_vanishing E r s τ u F).1 hF).2) ?_ a1 a2 a3 b1 b2 b3 (fun F hF => hF.1) ?_
    · intro u F hF m
      have := GlobalTheory.T.capelli_levi_factorization_sum E r s τ u F hF m
      change (cap (a := r + s) τ u F).1 _ - (capS r s τ (u + (r : ℂ) / 2) (capR r s τ (u + -(s : ℂ) / 2) F)).1 _ = 0
      rw [this, sub_eq_zero]
      have e : u + -(s : ℂ) / 2 = u - (s : ℂ) / 2 := by ring
      rw [e]
    · intro u
      obtain ⟨p, hp, h⟩ := GlobalTheory.T.cofinite_center_monic_annihilator E (r + s) J hJ _ (cap_mem_Zalg τ u)
      exact ⟨p, hp, fun F hF => h F hF.2⟩
  choose q₁ m₁ h₁ using fun τ => (key τ).1
  choose q₂ m₂ h₂ using fun τ => (key τ).2
  refine ⟨{z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := r) τ u) (q₁ τ u)},
    {z | ∃ (τ : E →+* ℂ) (u : ℂ), z = Polynomial.aeval (cap (a := s) τ u) (q₂ τ u)}, ?_, ?_, ?_, ?_⟩
  · refine GlobalTheory.T.cofinite_of_capelli_monic E r _ ?_ fun τ u => ⟨q₁ τ u, m₁ τ u, τ, u, rfl⟩
    rintro _ ⟨τ, u, rfl⟩
    exact aeval_mem_Zalg (cap_mem_Zalg τ u) _
  · refine GlobalTheory.T.cofinite_of_capelli_monic E s _ ?_ fun τ u => ⟨q₂ τ u, m₂ τ u, τ, u, rfl⟩
    rintro _ ⟨τ, u, rfl⟩
    exact aeval_mem_Zalg (cap_mem_Zalg τ u) _
  · rintro F hF hz G hG _ ⟨τ, u, rfl⟩
    refine Subtype.ext (funext fun m => ?_)
    rw [(GlobalTheory.T.capelli_restrict_levi E r s τ u (q₁ τ u) F).1 G hG m]
    exact h₁ τ u F ⟨hF, hz⟩ (m, 1)
  · rintro F hF hz G hG _ ⟨τ, u, rfl⟩
    refine Subtype.ext (funext fun m => ?_)
    rw [(GlobalTheory.T.capelli_restrict_levi E r s τ u (q₂ τ u) F).2 G hG m]
    exact h₂ τ u F ⟨hF, hz⟩ (1, m)

theorem exists_mem_goodCT (L : Subgroup (GL (Fin (r + s)) (Af E))) {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E (r + s)) W) (J : Set (Module.End ℂ (Sm E (r + s))))
    (hJ : Cofin J) (φ : Sm E (r + s)) (hφ : φ ∈ genSpace L ρ J)
    [MeasurableSpace (BlockIx (r + s) r → Ad E)] [BorelSpace (BlockIx (r + s) r → Ad E)]
    (μ : Measure (BlockIx (r + s) r → Ad E)) (𝓕 : Set (BlockIx (r + s) r → Ad E)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratN E (r + s) r) 𝓕 μ) :
    ∃ F ∈ goodCT L ρ J, ∀ g, F.1 g = ∫ x in 𝓕, φ.1 (unip x * g) ∂μ := by
  obtain ⟨hA, hLf, hK, hZ⟩ := hφ
  obtain ⟨F, hF1, hF2⟩ := GlobalTheory.T.constant_term_unipotent_integral_variant E (r + s) r φ hA.left hA.level μ 𝓕 hμ h𝓕
  have hlie : ∀ φ' F' : Sm E (r + s), (∀ (γ : GL (Fin (r + s)) E) (g : GA E (r + s)), φ'.1 (ratGL E (r + s) γ * g) = φ'.1 g) →
      IsOpen {k | finRep E (r + s) k φ' = φ'} → (∀ g, F'.1 g = ∫ x in 𝓕, φ'.1 (unip x * g) ∂μ) →
      ∀ (X : Lie E (r + s)) (g : GA E (r + s)), (lie E (r + s) X F').1 g = ∫ x in 𝓕, (lie E (r + s) X φ').1 (unip x * g) ∂μ := by
    intro φ' F' h1 h2 h3 X g
    obtain ⟨F'', e1, e2⟩ := GlobalTheory.T.constant_term_unipotent_integral_variant E (r + s) r φ' h1 h2 μ 𝓕 hμ h𝓕
    have : F' = F'' := Subtype.ext (funext fun g => (h3 g).trans (e1 g).symm)
    rw [this]
    exact e2 X g
  refine ⟨F, ⟨fun x g => ?_, fun γ g => ?_, fun k hk => ?_, fun g => ?_, fun g => ?_, fun z hz => ?_⟩, hF1⟩
  · rw [hF1, hF1]
    exact GlobalTheory.T.constant_term_translate_formula E (r + s) r φ hA.left hA.level μ 𝓕 hμ h𝓕 x g
  · rw [hF1, hF1]
    exact GlobalTheory.T.constant_term_levi_parabolic_formula E r s φ hA.left hA.level μ 𝓕 hμ h𝓕 γ g
  · refine Subtype.ext (funext fun g => ?_)
    change F.1 (g * finGL E (r + s) k) = F.1 g
    rw [hF1, hF1]
    refine congrArg (fun f : (BlockIx (r + s) r → Ad E) → ℂ => ∫ x in 𝓕, f x ∂μ) (funext fun x => ?_)
    have := congrFun (congrArg Subtype.val (hLf k hk)) (unip x * g)
    rw [← this]
    change _ = φ.1 (unip x * g * finGL E (r + s) k)
    rw [mul_assoc]
  · have h := GlobalTheory.T.constant_term_k_finite_coefficient E (r + s) r φ hA.left hA.level W ρ hK μ 𝓕 hμ h𝓕 g
    convert h using 1
    funext k
    exact hF1 _
  · obtain ⟨C, N, h⟩ := GlobalTheory.T.constant_term_moderate_growth_alt E (r + s) r φ hA μ 𝓕 hμ h𝓕 g
    exact ⟨C, N, fun y => by rw [hF1]; exact h y⟩
  · refine Subtype.ext (funext fun g => ?_)
    rw [GlobalTheory.T.constant_term_automorphic_criterion E (r + s) r μ 𝓕 hμ h𝓕 hlie φ F hA.left hA.level hF1 z (hJ.1 hz) g, hZ z hz]
    simp

theorem finiteDimensional_goodCT (h₁ : GenFin E r) (h₂ : GenFin E s) (L : Subgroup (GL (Fin (r + s)) (Af E)))
    (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E)))) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Kinf E (r + s)) W) (hρ : GlobalTheory.Published.AutFin.IsContRep ρ)
    (J : Set (Module.End ℂ (Sm E (r + s)))) (hJ : Cofin J) : FiniteDimensional ℂ (goodCT L ρ J) := by
  obtain ⟨J₁, J₂, c₁, c₂, k₁, k₂⟩ := centre J hJ
  obtain ⟨T, hT⟩ := GlobalTheory.T.constant_term_unseen_statement_a E r s L hL
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_dim_coefficients_finite_determining (Kinf E (r + s)) W ρ
  have key : ∀ (t : GL (Fin (r + s)) (Af E)) (κ : Kinf E (r + s)),
      ∃ 𝓥 : Submodule ℂ (GA E r × GA E s → ℂ), FiniteDimensional ℂ 𝓥 ∧ ∀ F ∈ goodCT L ρ J,
        (fun m => F.1 (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ))) ∈ 𝓥 := by
    intro t κ
    obtain ⟨L₁, ρ₁, o₁, q₁, e₁⟩ := GlobalTheory.T.constant_term_cofinite_ideal_transfer E r s L hL W ρ hρ J hJ J₁ c₁ k₁ t κ
    obtain ⟨L₂, ρ₂, o₂, q₂, e₂⟩ := GlobalTheory.T.constant_term_unseen_statement_b E r s L hL W ρ hρ J hJ J₂ c₂ k₂ t κ
    have f₁ := h₁ L₁ o₁ W ρ₁ q₁ J₁ c₁
    have f₂ := h₂ L₂ o₂ W ρ₂ q₂ J₂ c₂
    obtain ⟨𝓥, fd, hV⟩ := GlobalTheory.T.separately_finite_dim_functions_finite (GA E r) (GA E s)
      ((Submodule.span ℂ (genSpace L₁ ρ₁ J₁)).map (Sm E r).subtype)
      ((Submodule.span ℂ (genSpace L₂ ρ₂ J₂)).map (Sm E s).subtype) inferInstance inferInstance
    refine ⟨𝓥, fd, fun F hF => hV _ (fun m₂ => ?_) (fun m₁ => ?_)⟩
    · obtain ⟨G, hG, e⟩ := e₁ F hF m₂
      exact ⟨G, Submodule.subset_span hG, funext e⟩
    · obtain ⟨G, hG, e⟩ := e₂ F hF m₁
      exact ⟨G, Submodule.subset_span hG, funext e⟩
  choose 𝓥 fd hV using key
  let Ψ : goodCT L ρ J →ₗ[ℂ] ∀ p : T × S, 𝓥 p.1.1 p.2.1 :=
    { toFun := fun F p => ⟨_, hV p.1.1 p.2.1 F.1 F.2⟩
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  have hΨ : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun F hF => ?_
    obtain ⟨F, a1, a2, a3, a4, a5, a6⟩ := F
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    obtain ⟨x, m, t, k, l, ht, hl, rfl⟩ := hT g
    have e0 : ∀ κ ∈ S, F.1 (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits κ)) = 0 := by
      intro κ hκ
      have := congrFun (congrArg Subtype.val (congrFun hF (⟨t, ht⟩, ⟨κ, hκ⟩))) m
      exact this
    have hc := hS _ (a4 (lev (Ad E) r s m * finGL E (r + s) t)) e0
    have h1 := congrFun hc k
    have h2 := congrFun (congrArg Subtype.val (a3 l hl))
      (unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k))
    change F.1 (_ * finGL E (r + s) l) = _ at h2
    refine h2.trans ?_
    have e1 : unip x * lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k) =
        unip x * (lev (Ad E) r s m * finGL E (r + s) t * infGL E (r + s) (Unitary.toUnits k)) := by
      simp only [mul_assoc]
    rw [e1, a1]
    exact h1
  exact FiniteDimensional.of_injective Ψ hΨ

theorem ctFin : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), (∀ b < a, GenFin E b) →
    ∀ r, 0 < r → r < a → CTFin E a r := by
  intro E _ _ _ a hG r h0 hr
  obtain ⟨s, rfl⟩ : ∃ s, a = r + s := ⟨a - r, by omega⟩
  intro L hL W _ _ _ ρ hρ J hJ
  have hfd := finiteDimensional_goodCT (hG r hr) (hG s (by omega)) L hL ρ hρ J hJ
  refine ⟨(goodCT L ρ J).map (Sm E (r + s)).subtype, inferInstance, ?_⟩
  intro φ hφ _ _ μ 𝓕 hμ h𝓕
  obtain ⟨F, hF, e⟩ := exists_mem_goodCT L ρ J hJ φ hφ μ 𝓕 hμ h𝓕
  exact ⟨F, hF, funext e⟩

end GlobalTheory.CompanionTheory.CTFin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCutc
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EisE

variable {D : D7} {n r t a b : ℕ}

theorem jn_smul (hn : r + t = n) (e : AE D) (x : Mx D a r) (v : Mx D a t) :
    e • jn hn x v = jn hn (e • x) (e • v) := by
  ext i j
  simp only [jn, Matrix.smul_apply, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem intOff_jn (hn : r + t = n) {S : Finset (Pl D)} (x : Mx D a r) (v : Mx D a t) :
    IntOff S (jn hn x v) ↔ IntOff S x ∧ IntOff S v := by
  constructor
  · intro h
    refine ⟨fun w hw i j => ?_, fun w hw i j => ?_⟩
    · have := h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j))
      simpa [jn] using this
    · have := h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j))
      simpa [jn] using this
  · rintro ⟨h1, h2⟩ w hw i j
    simp only [jn, Matrix.submatrix_apply, id]
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j
    · exact h1 w hw i j
    · exact h2 w hw i j

theorem continuous_jn (hn : r + t = n) : Continuous (fun z : Mx D a r × Mx D a t => jn hn z.1 z.2) := by
  refine continuous_matrix fun i j => ?_
  simp only [jn, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j
  · exact continuous_fst.matrix_elem i j
  · exact continuous_snd.matrix_elem i j

def cutc (hn : r + t = n) (X : Mx D a n) : Mx D a r × Mx D a t :=
  (X.submatrix id fun j => (finSumFinEquiv.trans (finCongr hn)) (Sum.inl j),
    X.submatrix id fun j => (finSumFinEquiv.trans (finCongr hn)) (Sum.inr j))

theorem continuous_cutc (hn : r + t = n) : Continuous (cutc (D := D) (a := a) hn) := by
  refine Continuous.prodMk ?_ ?_ <;> exact continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem cutc_jn (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) : cutc hn (jn hn x v) = (x, v) := by
  refine Prod.ext ?_ ?_ <;> ext i j <;> simp [cutc, jn]

theorem intOff_smul {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) (x : Mx D a b) : IntOff S (e • x) := by
  intro v hv i j
  have h0 : cv D v e = 0 := by rw [hS.2 v, if_neg hv]
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, h0, zero_mul]
  exact zero_mem _

theorem adj_smul {e : AE D} (hc : cA D e = e) (x : Mx D a b) : adj (e • x) = e • adj x := by
  ext i j
  simp [adj, hc]

theorem ip_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (e • x) (e • y) = e • ip V x y := by
  simp only [ip, mm, adj_smul hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]

theorem yv_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : yv V b₀ (e • z.1, e • z.2) = e • yv V b₀ z := by
  simp only [yv, ip_smul he hc, mm, Matrix.mul_smul]

theorem pr_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (b₀ : HermE D r) (x y : Mx D r t) :
    pr b₀ (e • x) (e • y) = e • pr b₀ x y := by
  simp only [pr, adj_smul hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]

theorem qv_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : qv V b₀ (e • z.1, e • z.2) = e • qv V b₀ z := by
  simp only [qv, ip_smul he hc, yv_smul he hc, pr_smul he hc, smul_sub]

theorem pch_smul {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {x : Mx D t t} (hx : e • x = x) (T : Mx D t t) :
    pch ψ x (e • T) = pch ψ x T := by
  have : mm x (e • T) = mm x T := by
    conv_rhs => rw [← hx]
    simp only [mm, Matrix.smul_mul, Matrix.mul_smul]
  simp only [pch, this]

theorem isOrb_smul {V : HSp D} {b₀ : HermE D r} {e : AE D} {ν : Measure (Mx D V.rank r × Mx D V.rank t)}
    (h : IsOrb V b₀ e ν) (c : ℝ≥0) : IsOrb V b₀ e (c • ν) where
  fin := ⟨fun K hK => by
    have := h.fin.lt_top_of_isCompact hK
    rw [Measure.smul_apply]
    exact ENNReal.mul_lt_top (by simp) this⟩
  supp := by rw [Measure.smul_apply, h.supp, smul_zero]
  invU := fun g hg => by rw [Measure.map_smul, h.invU g hg]
  invS := fun y hy => by rw [Measure.map_smul, h.invS y hy]
  cov := fun g hg => by rw [Measure.map_smul, h.cov g hg, smul_comm]

theorem isOrb_zero {V : HSp D} {b₀ : HermE D r} {e : AE D} : IsOrb (t := t) V b₀ e 0 where
  fin := ⟨fun K _ => by simp⟩
  supp := by simp
  invU := fun g _ => by simp
  invS := fun y _ => by simp
  cov := fun g _ => by simp

end GlobalTheory.CompanionTheory.EisE

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousInvAddChar
section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZCuspPair

section Proofs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nontrivial_of_irr {G : Type} [Group G] [TopologicalSpace G] (τ : IrrRep G) : Nontrivial τ.V := by
  have hi := τ.irr
  by_contra hs
  rw [not_nontrivial_iff_subsingleton] at hs
  apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
  apply Subrepresentation.ext
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩

theorem continuous_inv_addChar (ψ : AddChar k Circle) (hc : Continuous ψ) : Continuous (ψ⁻¹ : AddChar k Circle) := by
  have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := funext fun a => AddChar.inv_apply ψ a
  rw [this]
  exact hc.comp continuous_neg

end Proofs

end GlobalTheory.CompanionTheory.BZCuspPair
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCovariance
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

theorem covar_of (hB : Bruhat) (hR : RatPts) : Covar := by
  intro D n V ψ χ θ μ ω hS γ hγ v Φ Ψ hΨ
  obtain ⟨-, -, -, -, -, -, ⟨𝓕, hC⟩, hW⟩ := hS
  have hF : FieldGen D.host.E (D.sp.cm.sig : D.host.E →+* D.host.E) n :=
    FieldGenPf.fieldGen_of_bruhat hB D.host.E _ (fun x => star_star x) two_ne_zero n
  exact Transfer.ratPts_transfer hR D n hF (CovAt ψ V ω) (fun _ _ h₁ h₂ => covAt_mul h₁ h₂)
    (fun g a h => covAt_levi D n V ψ χ θ μ ω hW g a h)
    (fun g b hb h => covAt_unip D n V ψ χ θ μ ω hW g b hb h)
    (fun g h => covAt_weyl D n V ψ χ θ μ ω hW hC.1 g h) γ hγ v Φ Ψ hΨ

theorem covar : Covar :=
  covar_of GlobalTheory.CompanionTheory.BruhatCell.bruhat GlobalTheory.CompanionTheory.RatPtsUnn.ratPtsUnn

end GlobalTheory.CompanionTheory.EisCovar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantExtendingStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_extending : ∀ {n : ℕ} (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)), IsPair E1 E2 → IsDerivK σ (kF E1 E2) → ∀ (E : KMod n) (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)), IsDualFam E G → ∀ (M : Finset (Fin n → ℤ)) (f : ∀ μ : Fin n → ℤ, hwOf G (wtR μ) →ₗ[ℂ] hwSp E1 E2 (wtR μ)), ∃ t ∈ invA σ E, ∀ μ ∈ M, ∀ ξ : hwOf G (wtR μ), t ξ = f μ ξ := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.ExtMulti.exists_inv_multi | exact GlobalTheory.CompanionTheory.RealCountG.ExtMulti.exists_inv_multi | (intros; apply GlobalTheory.CompanionTheory.RealCountG.ExtMulti.exists_inv_multi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiCoefficientOfBoundStatement
section
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_jacobi_coefficient_of_bound : PcBound → CfFJ := by
  first | exact @GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound | exact GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound | (intros; apply GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianEulerProductStandard
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg

theorem isHermND_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) :
    IsHermND σ (1 : Matrix (Fin M) (Fin M) E) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem exists_test_approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ n : ℕ, 0 < n → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → HermR (Ainf F) σ n → ℝ) (U : ℕ → ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (HermR (Fv F v) σ n)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : HermR (Fv F v) σ n) ∈ U k v) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets) ∧ (∀ k v, 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal) ∧ (∀ k, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k))) db ∧ ∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y * ψ (pairHerm (AF F) σ n y z) ∂db = GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ) * ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℂ)) ∧ (∀ k y, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y‖ ≤ ‖∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db‖) ∧ ∀ y, Filter.Tendsto (fun k => GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) Filter.atTop (nhds ((GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ y))) := by
  intro F E _ _ _ _ _ σ hCM n hn ψ hψ db hdb d b laminf lam hinf hlam
  obtain ⟨S₁, h⟩ := GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.exists_testH_approx F E σ hCM (2 * n + 1) 1 (isHermND_one σ _) n
    (by omega) ψ hψ db hdb d b laminf lam hinf hlam
  refine ⟨S₁, fun S hS => ?_⟩
  obtain ⟨ρ, U, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h S hS
  exact ⟨ρ, U, a1, a2, fun k v => ⟨(a3 k v).1, (a3 k v).2.1, (a3 k v).2.2.1⟩, a4, fun k v => (a3 k v).2.2.2, a5, a6, a7, a8⟩

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureEulerProductStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_measure_euler_product : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → HermR (Ainf F) σ n → ℝ) (U : ℕ → ∀ v : HeightOneSpectrum (𝓞 F), Set (HermR (Fv F v) σ n)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : HermR (Fv F v) σ n) ∈ U k v ∧ 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets) ∧ (∀ k, Integrable (fouH σ ψ db (testH σ b (ρ k) S (U k))) db ∧ ∀ z, ∫ y, fouH σ ψ db (testH σ b (ρ k) S (U k)) y * ψ (pairHerm (AF F) σ n y z) ∂db = testH σ b (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, testH σ b (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ) * ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℂ)) ∧ (∀ k y, ‖fouH σ ψ db (testH σ b (ρ k) S (U k)) y‖ ≤ ‖∫ w, testH σ b (ρ k) S (U k) w ∂db‖) ∧ ∀ y, Filter.Tendsto (fun k => fouH σ ψ db (testH σ b (ρ k) S (U k)) y / ∫ w, testH σ b (ρ k) S (U k) w ∂db) Filter.atTop (nhds ((intH σ b n S).indicator (fun _ => (1 : ℂ)) (hermFin σ y))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.exists_testH_approx | exact GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.exists_testH_approx | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.exists_testH_approx <;> assumption)
end

