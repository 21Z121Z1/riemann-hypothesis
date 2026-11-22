import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.HeightProofs.PowClassNumberIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0007
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0044
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0065
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCommonGrowthExponentGKDiscreteSeries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.TypeSum.CoefRep

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem norm_sum_list_le {p : ℕ} (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H) (y : Mx n) :
    ∀ L : List (ℂ × List (Mx n)),
      ‖∑ j, ℓ j (σ y ((L.map fun u => u.1 • Dw σ u.2 (x j)).sum))‖ ≤
        (L.map fun u => ‖u.1‖ * ‖∑ j, ℓ j (σ y (Dw σ u.2 (x j)))‖).sum
  | [] => by simp
  | u :: L => by
    simp only [List.map_cons, List.sum_cons, map_add, map_smul, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    refine (norm_add_le _ _).trans (add_le_add (le_of_eq (norm_mul _ _)) (norm_sum_list_le ℓ x y L))

theorem exists_rewrite : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ N : ℕ,
    ∃ S : List (List (Mx n)), Words (lieSet ε) S ∧ ∃ (m : List (List (Mx n)) → ℕ) (A : List (List (Mx n)) → ℝ),
    ∀ (p : ℕ) (ℓ : Fin p → (H →ₗ[ℂ] ℂ)) (x : Fin p → H), (∀ j, Sobolev₂ (lieSet ε) σ (ℓ j)) →
    (∀ j, IsKFin ε σ (x j)) → ∀ B : ℕ → ℝ,
    (∀ k (w : List (Mx n)), w.length ≤ k → (∀ X ∈ w, X ∈ lieSet ε ∧ Xᴴ = -X ∧ hs X ≤ 1) →
      ∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y (Dw σ w (x j)))‖ ≤ B k * (1 + hs y) ^ N) →
    ∃ (q : ℕ) (ℓ' : Fin q → (H →ₗ[ℂ] ℂ)) (x' : Fin q → H) (c : Fin q → ℝ),
      (∀ i, Sm ε σ (x' i)) ∧ (∀ i, 0 ≤ c i) ∧ (∀ i w, Sm ε σ w → ‖ℓ' i w‖ ≤ c i * sobNorm σ S w) ∧
      (∀ S', Words (lieSet ε) S' → ∑ i, c i * sobNorm σ S' (x' i) ≤ A S' * B (m S')) ∧
      ∀ y ∈ UJset ε, ∑ j, ℓ j (σ y (x j)) = ∑ i, ℓ' i (σ y (x' i)) := by
  intro _hHC hCW n ε H _ _ _ σ hstd N
  have hσ := hstd.1
  have hcb : CoefBound ε σ := GlobalTheory.TypeSum.coefBound_of_casselmanWallach hCW n ε H σ hstd
  obtain ⟨S, C, hS, hC, hM2⟩ := GlobalTheory.TypeSum.coefBound_two_finSum n ε H σ hstd hcb N
  obtain ⟨d, X, hX, hL1⟩ := GlobalTheory.TypeSum.TraceBound.trace_bound n ε H σ hstd
  have hL1' : ∀ T : List (List (Mx n)), ∃ (r : ℕ) (A : ℝ), Words (lieSet ε) T → ∀ (q : ℕ) (e : Fin q → H)
      (μ : Fin q → ℝ), Orthonormal ℂ e → (∀ i, IsKFin ε σ (e i)) → (∀ i, 1 ≤ μ i) →
      (∀ i, onePlusCas σ X (e i) = (μ i : ℂ) • e i) → ∑ i, sobNorm σ T (e i) ^ 2 / μ i ^ r ≤ A := by
    intro T
    by_cases hT : Words (lieSet ε) T
    · obtain ⟨r, A, h⟩ := hL1 T hT
      exact ⟨r, A, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hT⟩
  choose r A hrA using hL1'
  have hXl : ∀ i, X i ∈ lieSet ε := fun i => (hX i).1
  refine ⟨S, hS, fun S' => 2 * r (S ++ S'), fun S' => C * (1 + (d : ℝ)) ^ r (S ++ S') * max 0 (A (S ++ S')), ?_⟩
  intro p ℓ x hℓ hx B hB
  have hB0 : ∀ k, 0 ≤ B k := fun k => by
    have h := hB k [] (Nat.zero_le _) (by simp) 1 (one_mem_UJ ε)
    have hp : (0 : ℝ) < (1 + hs (1 : Mx n)) ^ N := pow_pos (by linarith [hs_nonneg (1 : Mx n)]) _
    exact (mul_nonneg_iff_of_pos_right hp).1 ((norm_nonneg _).trans h)
  obtain ⟨q, e, μ, he, heK, hμ, heig, hexp⟩ :=
    GlobalTheory.TypeSum.EigenSpan.exists_orthonormal_eigen n ε H σ hstd d X (fun i => ⟨(hX i).1, (hX i).2.1⟩) p x hx
  have heS : ∀ i, Sm ε σ (e i) := fun i => hstd.2.2.1 _ (heK i)
  have hxS : ∀ j, Sm ε σ (x j) := fun j => hstd.2.2.1 _ (hx j)
  have hμ0 : ∀ i (t : ℕ), 0 < μ i ^ t := fun i t => pow_pos (by linarith [hμ i]) t
  have hd0 : (0 : ℝ) ≤ 1 + (d : ℝ) := by positivity
  have key : ∀ (t : ℕ) (i : Fin q) (w : H), Sm ε σ w →
      ‖∑ j, ⟪e i, x j⟫_ℂ * ℓ j w‖ ≤
        C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) * sobNorm σ S w / μ i ^ t := by
    intro t i w hw
    obtain ⟨L, hL1, hL2, hL3⟩ := GlobalTheory.TypeSum.caspow_expand n ε H σ hσ d X hXl t
    have hxt : ∀ j, Sm ε σ ((onePlusCas σ X)^[t] (x j)) := fun j => sm_iterate_onePlusCas hσ hXl (hxS j) t
    have hM : 0 ≤ (1 + (d : ℝ)) ^ t * B (2 * t) := mul_nonneg (pow_nonneg hd0 _) (hB0 _)
    have hgrow : ∀ y ∈ UJset ε, ‖∑ j, ℓ j (σ y ((onePlusCas σ X)^[t] (x j)))‖ ≤
        (1 + (d : ℝ)) ^ t * B (2 * t) * (1 + hs y) ^ N := by
      intro y hy
      have e1 : ∀ j, (onePlusCas σ X)^[t] (x j) = (L.map fun u => u.1 • Dw σ u.2 (x j)).sum :=
        fun j => hL3 _ (hxS j)
      simp only [e1]
      refine (norm_sum_list_le ℓ x y L).trans ?_
      have hw0 : 0 ≤ B (2 * t) * (1 + hs y) ^ N :=
        mul_nonneg (hB0 _) (pow_nonneg (by linarith [hs_nonneg y]) _)
      calc (L.map fun u => ‖u.1‖ * ‖∑ j, ℓ j (σ y (Dw σ u.2 (x j)))‖).sum
          ≤ (L.map fun u => ‖u.1‖ * (B (2 * t) * (1 + hs y) ^ N)).sum := by
            refine List.sum_le_sum fun u hu => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
            refine hB (2 * t) u.2 (hL1 u hu).1 (fun Y hY => ?_) y hy
            obtain ⟨i, rfl⟩ := (hL1 u hu).2 Y hY
            exact hX i
        _ = (L.map fun u => ‖u.1‖).sum * (B (2 * t) * (1 + hs y) ^ N) := List.sum_map_mul_right _ _ _
        _ ≤ (1 + (d : ℝ)) ^ t * (B (2 * t) * (1 + hs y) ^ N) := mul_le_mul_of_nonneg_right hL2 hw0
        _ = _ := by ring
    have h2 := hM2 p ℓ _ hℓ hxt _ hM hgrow (e i) w (heS i) hw
    have e2 : ∀ j, ⟪e i, (onePlusCas σ X)^[t] (x j)⟫_ℂ = ((μ i : ℂ) ^ t) * ⟪e i, x j⟫_ℂ := fun j => by
      rw [inner_iterate_onePlusCas hσ hXl (heS i) (hxS j),
        iterate_onePlusCas_of_eq hσ hXl (heS i) (heig i), inner_smul_left]
      congr 1
      rw [← Complex.ofReal_pow, Complex.conj_ofReal]
    simp only [e2, mul_assoc, ← Finset.mul_sum] at h2
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith [hμ i])] at h2
    rw [le_div_iff₀ (hμ0 i t)]
    have hc := mul_comm (‖∑ j, ⟪e i, x j⟫_ℂ * ℓ j w‖) (μ i ^ t)
    linarith
  have hterm : ∀ (i : Fin q) (t : ℕ), 0 ≤ C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t :=
    fun i t => div_nonneg (mul_nonneg (mul_nonneg hC (mul_nonneg (pow_nonneg hd0 _) (hB0 _)))
      (sobNorm_nonneg σ S _)) (hμ0 i t).le
  have hbdd : ∀ i : Fin q, BddBelow (Set.range fun t : ℕ =>
      C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t) :=
    fun i => ⟨0, by rintro _ ⟨t, rfl⟩; exact hterm i t⟩
  refine ⟨q, fun i => ∑ j, ⟪e i, x j⟫_ℂ • ℓ j, e,
    fun i => ⨅ t : ℕ, C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t,
    heS, fun i => le_ciInf fun t => hterm i t, ?_, ?_, ?_⟩
  · intro i w hw
    have e3 : (∑ j, ⟪e i, x j⟫_ℂ • ℓ j) w = ∑ j, ⟪e i, x j⟫_ℂ * ℓ j w := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e3, mul_comm, Real.mul_iInf_of_nonneg (sobNorm_nonneg σ S w)]
    refine le_ciInf fun t => (key t i w hw).trans (le_of_eq ?_)
    ring
  · intro S' hS'
    have hW : Words (lieSet ε) (S ++ S') := words_append hS hS'
    have hA := hrA (S ++ S') hW q e μ he heK hμ heig
    set r₀ := r (S ++ S')
    have hK0 : 0 ≤ C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) :=
      mul_nonneg hC (mul_nonneg (pow_nonneg hd0 _) (hB0 _))
    calc ∑ i, (⨅ t : ℕ, C * ((1 + (d : ℝ)) ^ t * B (2 * t)) * sobNorm σ S (e i) / μ i ^ t) * sobNorm σ S' (e i)
        ≤ ∑ i, C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * sobNorm σ S (e i) / μ i ^ r₀ * sobNorm σ S' (e i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ciInf_le (hbdd i) r₀) (sobNorm_nonneg σ S' _)
      _ ≤ ∑ i, C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * (sobNorm σ (S ++ S') (e i) ^ 2 / μ i ^ r₀) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have a0 := sobNorm_nonneg σ S (e i)
          have b0 := sobNorm_nonneg σ S' (e i)
          have hab : sobNorm σ S (e i) * sobNorm σ S' (e i) ≤ sobNorm σ (S ++ S') (e i) ^ 2 := by
            rw [sobNorm_append]; nlinarith
          have hm := hμ0 i r₀
          calc C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * sobNorm σ S (e i) / μ i ^ r₀ * sobNorm σ S' (e i)
              = C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * (sobNorm σ S (e i) * sobNorm σ S' (e i) / μ i ^ r₀) := by
                ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hab hm.le) hK0
      _ = C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * ∑ i, sobNorm σ (S ++ S') (e i) ^ 2 / μ i ^ r₀ := by
          rw [Finset.mul_sum]
      _ ≤ C * ((1 + (d : ℝ)) ^ r₀ * B (2 * r₀)) * max 0 (A (S ++ S')) :=
          mul_le_mul_of_nonneg_left (hA.trans (le_max_right _ _)) hK0
      _ = C * (1 + (d : ℝ)) ^ r (S ++ S') * max 0 (A (S ++ S')) * B (2 * r (S ++ S')) := by ring
  · intro y _
    have h1 : ∀ j, ℓ j (σ y (x j)) = ∑ i, ⟪e i, x j⟫_ℂ * ℓ j (σ y (e i)) := fun j => by
      conv_lhs => rw [hexp j]
      simp only [map_sum, map_smul, smul_eq_mul]
    simp only [h1, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    exact Finset.sum_comm

end GlobalTheory.TypeSum.CoefRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsGrowthExponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.TypeSum GlobalTheory.TypeSum.GrowthAtPlace Formalism.REAL

namespace GlobalTheory.TypeSum.GKCoef

theorem exists_growth_exponent : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau), IsInfFam (D := D) θ → GlobalTheory.Published.HarishChandraModules →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    IsDS ε lam σ → IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T → ∀ x : GA D V, ∃ N : ℕ, ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ, ∃ C : ℝ,
      ∀ y ∈ UJset ε, ‖T w (x * atTau θ V τ (P⁻¹ * y * P))‖ ≤ C * (1 + Formalism.REAL.hs y) ^ N := by
  intro D θ V τ hθ hHC H _ _ σ lam ε P T hDS hP hPG hT x
  haveI : CompleteSpace H := hDS.1
  have hstd : Std ε σ := std_of_isDS hHC hDS
  obtain ⟨Th, hTh⟩ := LinearMap.exists_extend T
  have eTh : ∀ v (hv : v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ), Th v = T ⟨v, hv⟩ := fun v hv => LinearMap.congr_fun hTh ⟨v, hv⟩
  have hkf : ∀ v, IsKFin ε σ v → v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ := fun v hv => mem_kFin_iff.2 hv
  have hDw : ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) → ∀ v, IsKFin ε σ v → IsKFin ε σ (Dw σ l v) := by
    intro l hl v hv
    induction l with
    | nil => exact hv
    | cons X l ih =>
      exact isKFin_dRep _ ε H σ hstd _ (ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) X (hl X List.mem_cons_self)
  obtain ⟨u, hu, hu0⟩ := hstd.2.2.2.2
  obtain ⟨N, F, hF0, hFd, hFg⟩ := umg_atTau D θ hθ V τ (T ⟨u, hkf u hu⟩) (hT.aut _) ε P hP hPG x
  have hFeq : ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) → ∀ y ∈ UJset ε,
      F l y = Th (Dw σ l u) (x * atTau θ V τ (P⁻¹ * y * P)) := by
    intro l hl
    induction l with
    | nil => intro y hy; rw [hF0 y hy]; exact (congrFun (eTh u (hkf u hu)) _).symm
    | cons X l ih =>
      intro y hy
      have hl' : ∀ Y ∈ l, Y ∈ lieSet ε := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
      have hX := hl X List.mem_cons_self
      have k1 := hDw l hl' u hu
      have k2 := hDw (X :: l) hl u hu
      have d1 := hFd l hl' X hX y hy
      have d2 := hasDerivAt_map hθ hP hPG hT ⟨Dw σ l u, hkf _ k1⟩ ⟨Dw σ (X :: l) u, hkf _ k2⟩ hX
        (hstd.2.2.1 _ k1) rfl x hy
      have d1' : HasDerivAt (fun t : ℝ => T ⟨Dw σ l u, hkf _ k1⟩
          (x * atTau θ V τ (P⁻¹ * (y * NormedSpace.exp (t • X)) * P))) (F (X :: l) y) 0 := by
        refine d1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
        show _ = F l _
        rw [ih hl' _ (mul_mem_UJ hy (exp_mem_UJ hX t)), eTh _ (hkf _ k1)]
      rw [d1'.unique d2, eTh _ (hkf _ k2)]
  obtain ⟨Pr, hPr⟩ : ∃ Pr : H → Prop, ∀ w, Pr w ↔ ∀ l : List (Mx V.rank), (∀ X ∈ l, X ∈ lieSet ε) →
      ∃ C : ℝ, ∀ y ∈ UJset ε, ‖Th (Dw σ l w) (x * atTau θ V τ (P⁻¹ * y * P))‖ ≤ C * (1 + hs y) ^ N :=
    ⟨_, fun _ => Iff.rfl⟩
  have hSm : ∀ w, IsKFin ε σ w → Sm ε σ w := hstd.2.2.1
  obtain ⟨W, hW⟩ : ∃ W : Submodule ℂ H, ∀ w, w ∈ W ↔ IsKFin ε σ w ∧ Pr w := by
    refine ⟨{ carrier := {w | IsKFin ε σ w ∧ Pr w}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ },
      fun _ => Iff.rfl⟩
    · rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
      refine ⟨mem_kfin.1 ((kfin ε σ).add_mem (mem_kfin.2 ha1) (mem_kfin.2 hb1)), (hPr _).2 fun l hl => ?_⟩
      obtain ⟨C1, h1⟩ := (hPr a).1 ha2 l hl
      obtain ⟨C2, h2⟩ := (hPr b).1 hb2 l hl
      refine ⟨C1 + C2, fun y hy => ?_⟩
      rw [Dw_add hstd.1 hl (hSm _ ha1) (hSm _ hb1), map_add, Pi.add_apply, add_mul]
      exact (norm_add_le _ _).trans (add_le_add (h1 y hy) (h2 y hy))
    · have h0 : IsKFin ε σ (0 : H) := mem_kfin.1 (kfin ε σ).zero_mem
      refine ⟨h0, (hPr _).2 fun l hl => ⟨0, fun y hy => ?_⟩⟩
      have e := Dw_smul hstd.1 hl (0 : ℂ) (hSm _ h0)
      rw [zero_smul, zero_smul] at e
      rw [e, map_zero]
      simp
    · rintro c a ⟨ha1, ha2⟩
      refine ⟨mem_kfin.1 ((kfin ε σ).smul_mem c (mem_kfin.2 ha1)), (hPr _).2 fun l hl => ?_⟩
      obtain ⟨C, h1⟩ := (hPr a).1 ha2 l hl
      refine ⟨‖c‖ * C, fun y hy => ?_⟩
      rw [Dw_smul hstd.1 hl c (hSm _ ha1), map_smul, Pi.smul_apply, smul_eq_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_left (h1 y hy) (norm_nonneg c)).trans_eq (by ring)
  have hWk : ∀ w ∈ W, IsKFin ε σ w := fun w hw => ((hW w).1 hw).1
  have hWX : ∀ X, inG ε X → ∀ w ∈ W, dRep σ X w ∈ W := by
    intro X hXg w hw
    obtain ⟨hw1, hw2⟩ := (hW w).1 hw
    have hXl : X ∈ lieSet ε := hXg
    refine (hW _).2 ⟨isKFin_dRep _ ε H σ hstd w hw1 X hXl, (hPr _).2 fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := (hPr w).1 hw2 (l ++ [X]) (by
      intro Y hY
      rcases List.mem_append.1 hY with h | h
      · exact hl Y h
      · rw [List.mem_singleton] at h; rw [h]; exact hXl)
    refine ⟨C, fun y hy => ?_⟩
    have e : Dw σ l (dRep σ X w) = Dw σ (l ++ [X]) w := by rw [Dw_append]; rfl
    rw [e]
    exact hC y hy
  have hWK : ∀ k ∈ Kset ε, ∀ w ∈ W, σ k w ∈ W := by
    intro k hk w hw
    obtain ⟨hw1, hw2⟩ := (hW w).1 hw
    have hkU := K_le_UJ hk
    refine (hW _).2 ⟨isKFin_translate hw1 hk, (hPr _).2 fun l hl => ?_⟩
    have hl' : ∀ X ∈ l.map (fun X => k⁻¹ * X * k), X ∈ lieSet ε := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
      exact conj_mem_lie (isUnit_Jm ε) hkU (hl Y hY)
    obtain ⟨C, hC⟩ := (hPr w).1 hw2 _ hl'
    have hv' := hDw _ hl' w hw1
    refine ⟨|C| * (1 + hs k) ^ N, fun y hy => ?_⟩
    rw [Dw_translate hstd.1 hkU (hSm _ hw1) hl, eTh _ (hkf _ (isKFin_translate hv' hk)),
      map_K hθ hP hPG hT hk ⟨_, hkf _ hv'⟩ _ rfl x hy, ← eTh _ (hkf _ hv')]
    refine (hC (y * k) (mul_mem_UJ hy hkU)).trans ?_
    have hp : (1 + hs (y * k)) ^ N ≤ (1 + hs y) ^ N * (1 + hs k) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith [hs_nonneg (y * k)]) (one_add_hs_mul_le y k) N
    calc C * (1 + hs (y * k)) ^ N ≤ |C| * (1 + hs (y * k)) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith [hs_nonneg (y * k)]) _)
      _ ≤ |C| * ((1 + hs y) ^ N * (1 + hs k) ^ N) := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
      _ = |C| * (1 + hs k) ^ N * (1 + hs y) ^ N := by ring
  have huW : u ∈ W := (hW u).2 ⟨hu, (hPr u).2 fun l hl => by
    obtain ⟨C, hC⟩ := hFg l hl
    exact ⟨C, fun y hy => by rw [← hFeq l hl y hy]; exact hC y hy⟩⟩
  have hW0 : W ≠ ⊥ := fun hb => hu0 ((Submodule.mem_bot ℂ).1 (hb ▸ huW))
  have hd := GlobalTheory.HCModIrred.dense_of_stable hHC hstd.1 hstd.2.1 hWk hWX hWK hW0
  refine ⟨N, fun w => ?_⟩
  have hmem := GlobalTheory.HCModIrred.mem_of_dense hstd hd hWk hWK (mem_kFin_iff.1 w.2)
  obtain ⟨C, hC⟩ := (hPr _).1 ((hW _).1 hmem).2 [] (by simp)
  refine ⟨C, fun y hy => ?_⟩
  have := hC y hy
  rwa [show Dw σ [] (w : H) = w from rfl, eTh _ w.2] at this

end GlobalTheory.TypeSum.GKCoef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsShortSeriesTwistCharOfTwistingIdeleChar
section
noncomputable section

namespace GlobalTheory.FinalJoin2.ReadTwist

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cjFin_val (D : D7) (y : (AfE D)ˣ) :
    ((cjFin D y : (AfE D)ˣ) : AfE D) = GlobalTheory.NormOneChar.bar (cF D) (y : AfE D) := by
  have h : D.conjF = (cF D : D.host.E →ₐ[D.host.F] D.host.E) :=
    AlgHom.ext fun a => (D.conjF_eq a).trans (GlobalTheory.TwistFieldCompare.cF_eq a).symm
  unfold cjFin
  rw [h]
  rfl

theorem normOne_iff {D : D7} (x : (AfE D)ˣ) :
    NormOne x ↔ (x : AfE D) * GlobalTheory.NormOneChar.bar (cF D) (x : AfE D) = 1 := Iff.rfl

theorem congOne_iff {D : D7} (N : ℕ) (x : (AfE D)ˣ) :
    x ∈ GlobalTheory.NormOneChar.congOne (cF D) N ↔ CongOne N x ∧ NormOne x := by
  unfold CongOne
  simp only [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers, nsmul_eq_mul]
  exact Iff.rfl

theorem cF_cF (D : D7) (y : D.host.E) : cF D (cF D y) = y := star_star y

theorem exists_rat {D : D7} (x : (AfE D)ˣ) (a : D.host.E) (h : (x : AfE D) = 1 ⊗ₜ a) (hn : NormOne x) :
    ∃ (y : (AfE D)ˣ) (b : D.host.E), (y : AfE D) = 1 ⊗ₜ b ∧ x = y / cjFin D y := by
  have key : ∀ b : D.host.E, b ≠ 0 → (x : AfE D) * GlobalTheory.NormOneChar.diag D.host.F D.host.E (cF D b) =
      GlobalTheory.NormOneChar.diag D.host.F D.host.E b →
      ∃ (y : (AfE D)ˣ) (b : D.host.E), (y : AfE D) = 1 ⊗ₜ b ∧ x = y / cjFin D y := fun b hb e => by
    refine ⟨(GlobalTheory.NormOneChar.isUnit_diag D.host.F D.host.E hb).unit, b, rfl, eq_div_iff_mul_eq'.2 (Units.ext ?_)⟩
    rw [Units.val_mul, cjFin_val]
    exact e
  have hx : (x : AfE D) = GlobalTheory.NormOneChar.diag D.host.F D.host.E a := h
  by_cases ha : 1 + a = 0
  · have hc : cF D ≠ 1 := by
      have : cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
      rw [this]
      exact IsCMField.complexConj_ne_one _
    obtain ⟨z, hz⟩ : ∃ z, cF D z ≠ z := by
      by_contra h0
      push_neg at h0
      exact hc (AlgEquiv.ext h0)
    refine key (z - cF D z) (sub_ne_zero.2 hz.symm) ?_
    rw [hx, ← map_mul, map_sub, cF_cF]
    congr 1
    linear_combination (cF D z - z) * ha
  · refine key (1 + a) ha ?_
    have h1 : (x : AfE D) * GlobalTheory.NormOneChar.diag D.host.F D.host.E (cF D a) = 1 := by
      have := (normOne_iff x).1 hn
      rw [h] at this
      rw [h]
      exact this
    rw [map_add, map_one, map_add, map_add, map_one, mul_add, h1, ← hx, mul_one, add_comm]

theorem cong_div {D : D7} (N : ℕ) (y : (AfE D)ˣ) (hu : IntUnit y) (hy : CongOne N y) :
    CongOne N (y / cjFin D y) ∧ NormOne (y / cjFin D y) := by
  have hv : ((y / cjFin D y : (AfE D)ˣ) : AfE D) =
      (y : AfE D) * GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D) := by
    rw [div_eq_mul_inv, ← map_inv, Units.val_mul, cjFin_val]
  have h1 : (y : AfE D) * ((y⁻¹ : (AfE D)ˣ) : AfE D) = 1 := Units.mul_inv y
  have h2 : GlobalTheory.NormOneChar.bar (cF D) (y : AfE D) * GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D) = 1 := by
    rw [← map_mul, h1, map_one]
  rw [← congOne_iff]
  obtain ⟨-, hi⟩ := hu
  obtain ⟨w, hw, e⟩ := hy
  rw [GlobalTheory.CharFin.integralFiniteAdeles_eq_adelicCompletion_integers] at hi hw
  rw [nsmul_eq_mul] at e
  have e' := congrArg (GlobalTheory.NormOneChar.bar (cF D)) e
  rw [map_sub, map_one, map_mul, map_natCast] at e'
  have hi' := GlobalTheory.NormOneChar.bar_mem (cF D) hi
  have hw' := GlobalTheory.NormOneChar.bar_mem (cF D) hw
  refine ⟨⟨(w - GlobalTheory.NormOneChar.bar (cF D) w) * GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D),
    mul_mem (sub_mem hw hw') hi', ?_⟩, ?_⟩
  · rw [hv]
    linear_combination (GlobalTheory.NormOneChar.bar (cF D) ((y⁻¹ : (AfE D)ˣ) : AfE D)) * (e - e') + h2
  · rw [hv, map_mul, GlobalTheory.NormOneChar.bar_bar _ (cF_cF D)]
    linear_combination ((y : AfE D) * ((y⁻¹ : (AfE D)ˣ) : AfE D)) * h2 + h1

theorem exists_xiOK_xiTilde : ∀ (D : D7) (p : ℕ) (de : (AfE D)ˣ →* ℂˣ), (p = D.host.pde ∨ p = D.host.pde') → XiRec D p de → ∃ xi, XiOK D p xi ∧ XiTilde xi de := by
  intro D p de hp h
  obtain ⟨h90, hfix, hcong⟩ := GlobalTheory.T.finiteIdeles_normOne_eq_div_conj_of_congOne D
  have hpp : p.Prime ∧ p % 15 = 1 := by
    rcases hp with rfl | rfl
    · exact ⟨D.host.pde_prime, D.host.pde_mod.1⟩
    · exact ⟨D.host.pde'_prime, D.host.pde_mod.2⟩
  have hp2 : p ≠ 2 := by rintro rfl; exact absurd hpp.2 (by norm_num)
  let q : (AfE D)ˣ →* (AfE D)ˣ := MonoidHom.id _ / cjFin D
  obtain ⟨xi, hxi⟩ := GlobalTheory.PrimaryCharacter.exists_factor_of_ker_le q de fun x hx => by
    have h1 : x = cjFin D x := div_eq_one.1 hx
    obtain ⟨a, ha⟩ := hfix x h1.symm
    exact h.real x a ha
  have ht : XiTilde xi de := hxi
  refine ⟨xi, ⟨fun x a ha hn => ?_, fun x hn hc => ?_, ?_, ?_, fun x hn => ?_⟩, ht⟩
  · obtain ⟨y, b, hb, rfl⟩ := exists_rat x a ha hn
    rw [ht, h.rat y b hb]
  · obtain ⟨y, hy, hyc, rfl⟩ := hcong p _ x hpp.1 hp2 (Dvd.intro_left _ rfl)
      (Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hpp.1.pos) hn hc
    rw [ht, h.tame y hy hyc]
  · obtain ⟨y, hy, hyc, hne⟩ := h.ram
    obtain ⟨c1, c2⟩ := cong_div _ y hy hyc
    exact ⟨_, c2, c1, by rwa [ht]⟩
  · obtain ⟨m, hm, hf⟩ := h.fin
    refine ⟨m, hm, fun x hn => ?_⟩
    obtain ⟨y, rfl⟩ := h90 x hn
    rw [ht, hf]
  · obtain ⟨y, rfl⟩ := h90 x hn
    rw [ht]
    exact h.val y

end GlobalTheory.FinalJoin2.ReadTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsStagesWithDeltaStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stages_with_delta : ∀ (B : Base) (Del : ℚ) (letter : B.Word → Fin (B.R.k - 2) → Bool) (η : ℝ), 0 < Del → 0 < η → Function.Injective letter → (∀ w τ (l : ℕ) (h : l + 1 < B.R.k - 1), (B.hcW w τ).v ⟨l, by omega⟩ - (B.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) → (∀ w τ (l : ℕ) (h : l < B.R.k - 2), (B.hcW w τ).u ⟨l + 1, by omega⟩ = (B.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)) → ∃ X : Stages, X.B = B ∧ X.toD7.s.Del = Del ∧ X.toD7.div.etaF = η ∧ DV.KapDef X.toD7 ∧ ∀ w, X.toD7.what₂.muAt w = X.toD7.what₂.mu0 → ∀ j, 1 ≤ j → j ≤ X.toD7.R.m → X.toD7.what₂.Aj j w = 0 := by
  first | exact @GlobalTheory.StandInStages.exists_stages_prescribed | exact GlobalTheory.StandInStages.exists_stages_prescribed | (intros; apply GlobalTheory.StandInStages.exists_stages_prescribed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExpSecondKindCoordinatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_second_kind_coordinates : ∀ (n : ℕ) (ε : Fin n → Bool) (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n), (∀ i, b i ∈ lieSet ε) →
    LinearIndependent ℝ b → (∀ Z ∈ lieSet ε, ∃ c : Fin d → ℝ, Z = ∑ i, c i • b i) →
    ∀ c : Fin d → ℝ, ∃ τ : ℝ → (Fin d → ℝ), τ 0 = 0 ∧ HasDerivAt τ c 0 ∧
      ∀ᶠ t in nhds (0 : ℝ), NormedSpace.exp (t • ∑ i, c i • b i) =
        (List.ofFn fun i => NormedSpace.exp (τ t i • b i)).prod := by
  first | exact @GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero | exact GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero | (intros; apply GlobalTheory.SecondKindChart.exp_eq_expProd_near_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HostXiOrderBoundsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_xi_order_bounds : ∀ (P : Pre) (L : ℝ), HostSz P.host L → Real.log P.restRowsFiniteGroupCard ≤ P.R.f * (P.R.r : ℝ) ^ 2 * (18 * L + 2) ∧ (∀ p ∈ [P.host.pde, P.host.pde'], 0 < xiOrd P.host (P.host.g 0 * P.host.g 1 * p) ∧ Real.log (xiOrd P.host (P.host.g 0 * P.host.g 1 * p)) ≤ 1 + Real.log (classNumber P.host.E) + 2 * P.R.f * (21 * L)) ∧ 8 ≤ P.R.f ∧ 2 * P.R.m ≤ P.R.r := by
  first | exact @GlobalTheory.FieldSize.roots_sizes | exact GlobalTheory.FieldSize.roots_sizes | (intros; apply GlobalTheory.FieldSize.roots_sizes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IntrinsicIndexBoundOfFiniteNetHypothesesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_secNorm_inputsR_of_inputsNet : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ), InputsNet large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF Tn nP nW h0 nus → ∃ n : SecNorm B, InputsR large₂ (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) K H Ch Ah Cq Aq C2 A2 CR CT (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF Tn nP nW h0 nus := by
  first | exact @GlobalTheory.FinalJoin.inputsR_of_inputsNet | exact GlobalTheory.FinalJoin.inputsR_of_inputsNet | (intros; apply GlobalTheory.FinalJoin.inputsR_of_inputsNet <;> assumption)
end

