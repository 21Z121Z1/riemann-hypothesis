import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0841
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelOfDualParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0348
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0085
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0344
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0340
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0331
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0555
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EdgeFactorNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}

theorem mulSingle_ne {m : ℕ} (κ : GL (Fin (Γ.rank (0, m))) k) {X : ℕ × ℕ} (h : X ≠ (0, m)) :
    (Pi.mulSingle (0, m) κ : Γ.VertexGroup) X = 1 := Pi.mulSingle_eq_of_ne h _

theorem moveArgs_fill (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (x : ColArgs Γ) (y : RowArgs Γ)
    (e : Vars Γ) :
    Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (fill hs x y e) = fill hs x (Function.update y 0 ((κ⁻¹).val * y 0)) e := by
  funext b
  cases b with
  | theta i j =>
    by_cases h : i = Γ.m
    · subst h
      rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt, hm]), mulSingle_ne κ (by simp [Edge.src, hm])]
      simp [fill]
    · simp [moveArgs, fill, h]
  | ex i j =>
    by_cases hj : j = Γ.m
    · subst hj
      by_cases hi : i = 0
      · subst hi
        rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt]), fill_ex, fill_ex]
        simp only [Edge.src, Pi.mulSingle_eq_same, Function.update_self, map_one, inv_one, Units.val_one, Matrix.one_mul]
        rw [Matrix.transpose_mul, Assignment.read, invT_val]
      · rw [moveArgs, mulSingle_ne κ (by simp [Edge.tgt]), mulSingle_ne κ (by simp [Edge.src, hi])]
        simp [fill, Function.update_of_ne hi]
    · simp [moveArgs, fill, hj]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid MeasureTheory

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}

theorem moveArgs_mul (s : Assignment) (g g' : Γ.VertexGroup) (z : Γ.Args) :
    Γ.moveArgs s (g * g') z = Γ.moveArgs s g' (Γ.moveArgs s g z) := by
  funext b
  simp only [moveArgs, Pi.mul_apply, map_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem mulSingle_comm (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (g : Γ.VertexGroup) (hg : g (0, Γ.m) = 1) :
    Pi.mulSingle (0, Γ.m) κ * g = g * Pi.mulSingle (0, Γ.m) κ := by
  funext X
  by_cases h : X = (0, Γ.m)
  · subst h; simp [hg]
  · simp [Pi.mulSingle_eq_of_ne h]

theorem elt_zero_m (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) {J : Γ.Level} (ρ : Reps hs J) (β : Cosets hs J) : ρ.elt β (0, Γ.m) = 1 := by
  simp [Reps.elt, onColumn, Ne.symm hm]

theorem prod_edgeFactor (hm : Γ.m ≠ 0) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod =
      Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) (.ex 0 Γ.m) := by
  have h1 : ∀ b : Edge, b.src ≠ (0, Γ.m) → b.tgt ≠ (0, Γ.m) → Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) b = 1 := by
    intro b hs ht
    simp [edgeFactor, Pi.mulSingle_eq_of_ne hs, Pi.mulSingle_eq_of_ne ht]
  obtain ⟨n, hn⟩ : ∃ n, Γ.m = n + 1 := ⟨Γ.m - 1, by omega⟩
  rw [oppositePath, List.map_append, List.prod_append]
  have h2 : (((List.range Γ.m).reverse.map (Edge.theta Γ.m)).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod = 1 := by
    refine List.prod_eq_one fun a ha => ?_
    simp only [List.map_map, List.mem_map, Function.comp_apply] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact h1 _ (by simp [Edge.src, hm]) (by simp [Edge.tgt, hm])
  rw [h2, mul_one]
  have h3 : List.range Γ.m = 0 :: (List.range n).map Nat.succ := by rw [hn, List.range_succ_eq_map]
  rw [h3, List.map_cons, List.map_cons, List.prod_cons]
  have h4 : ((((List.range n).map Nat.succ).map (Edge.ex · Γ.m)).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod = 1 := by
    refine List.prod_eq_one fun a ha => ?_
    simp only [List.map_map, List.mem_map, Function.comp_apply] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact h1 _ (by simp [Edge.src]) (by simp [Edge.tgt])
  rw [h4, mul_one]

variable [MeasurableSpace k] [BorelSpace k]

theorem moved_law (keep : Bool) (g : Γ.VertexGroup) (hg : g (0, Γ.m) = 1) (κ : GL (Fin (Γ.rank (0, Γ.m))) k)
    (T : Γ.Args → ℂ) (c : ℂ) (hlaw : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (0, Γ.m) κ) T = c • T) (z : Γ.Args) :
    ((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod *
      moved Γ keep g T (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) z) = c * moved Γ keep g T z := by
  have h1 := congrFun hlaw (Γ.moveArgs .one g z)
  simp only [pathAct, Pi.smul_apply, smul_eq_mul] at h1
  have h2 : Γ.moveArgs .one g (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) z) =
      Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (Γ.moveArgs .one g z) := by
    rw [← moveArgs_mul, ← moveArgs_mul, mulSingle_comm κ g hg]
  simp only [moved, pathAct, h2]
  calc _ = (if keep then (1 : ℂ) else (((charFactor Γ g)⁻¹ : ℂˣ) : ℂ)) * ((oppositePath Γ.m).map (Γ.edgeFactor .one g)).prod *
        (((oppositePath Γ.m).map (Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ))).prod *
          T (Γ.moveArgs .one (Pi.mulSingle (0, Γ.m) κ) (Γ.moveArgs .one g z))) := by ring
    _ = _ := by rw [h1]; ring

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

open GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Grid MeasureTheory

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {Γ : Grid k}
  [MeasurableSpace k] [BorelSpace k]

theorem datum_law (hs : 1 ≤ Γ.s) (hm : Γ.m ≠ 0) (ψ : AddChar k Circle) (ν : Measure k) {J : Γ.Level} (keep : Bool)
    (ρ : Reps hs J) (T : Γ.Args → ℂ) (β : Cosets hs J) (κ : GL (Fin (Γ.rank (0, Γ.m))) k) (c : ℂ)
    (hlaw : Γ.pathAct .one (oppositePath Γ.m) (Pi.mulSingle (0, Γ.m) κ) T = c • T) (x : ColArgs Γ) (y : RowArgs Γ) :
    Γ.edgeFactor .one (Pi.mulSingle (0, Γ.m) κ) (.ex 0 Γ.m) *
        (unfTerm ψ ν keep ρ T β).datum x (Function.update y 0 ((κ⁻¹).val * y 0)) =
      c * (unfTerm ψ ν keep ρ T β).datum x y := by
  simp only [unfTerm, flatTensor, flatIntegrand, ← moveArgs_fill hs hm κ x y]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  have h := moved_law keep (ρ.elt β) (elt_zero_m hs hm ρ β) κ T c hlaw (fill hs x y e)
  rw [prod_edgeFactor hm] at h
  simp only
  rw [← mul_assoc, h, mul_assoc]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def kapAt (S : GridChoice W U) (t : T) (w : Pl D.host.E) (k : FinPt G (.grid 0 D.R.m)) :
    GL (Fin ((locGrid G t w).rank (0, D.R.m))) (Kw w) :=
  inBasis (rank_vertex G t w (X := (0, D.R.m)) ⟨Nat.zero_le _, le_rfl⟩) (S.B.β 0 D.R.m) w (finG (G.V (.grid 0 D.R.m)) k)

theorem edgeFactor_ne_zero {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Γ : GlobalTheory.SplitFlip.Grid k) (g : Γ.VertexGroup) (b : GlobalTheory.SplitFlip.Edge) : Γ.edgeFactor .one g b ≠ 0 := by
  simp only [GlobalTheory.SplitFlip.Grid.edgeFactor]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) (GlobalTheory.SplitFlip.apow_ne_zero _ _))
    (GlobalTheory.SplitFlip.apow_ne_zero _ _)

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

theorem prod_update_comp {m : ℕ} {X : Fin m → Type} (F : ∀ i, X i → ℂ) (i₀ : Fin m) (f : X i₀ → X i₀) (ys : ∀ i, X i) :
    ∏ i, Function.update F i₀ (fun y => F i₀ (f y)) i (ys i) = ∏ i, F i (Function.update ys i₀ (f (ys i₀)) i) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : i = i₀
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem sum_update_comp {κ : Type} {m n : ℕ} {X : Fin n → Type} {Y : Fin m → Type} (τ : κ →₀ ℂ) (A : κ → ∀ j, X j → ℂ)
    (B : κ → ∀ i, Y i → ℂ) (i₀ : Fin m) (f : Y i₀ → Y i₀) (xs : ∀ j, X j) (ys : ∀ i, Y i) :
    (τ.sum fun d a' => a' * (∏ j, A d j (xs j)) * ∏ i, Function.update (B d) i₀ (fun y => B d i₀ (f y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, A d j (xs j)) * ∏ i, B d i (Function.update ys i₀ (f (ys i₀)) i) :=
  Finset.sum_congr rfl fun d _ => by beta_reduce; rw [prod_update_comp]

theorem key_cancel (s PE PL P P' : ℂ) (h1 : PE ≠ 0) (h2 : s * PL = PE) (h3 : PE * P' = PL * P) : s * P' = P :=
  mul_left_cancel₀ h1 (by linear_combination s * h3 + P * h2)

end GlobalTheory.FirstRowTermLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicInvariantFormVacuumSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitAlgForm

open GlobalTheory.SplitScalar GlobalTheory.LevelSeries.IdemSumForm GlobalTheory.AlgWave

theorem psi_ne_zero {G : Type} [AddGroup G] (ψ : AddChar G ℂ) (x : G) : ψ x ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem fin_smul {D : D7} {m n : ℕ} (a : AE D) {x : Mx D m n} (hx : x.map (infPart D) = 0) :
    (a • x).map (infPart D) = 0 := by
  ext i j
  have : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
  show infPart D (a * x i j) = 0
  rw [RingHom.map_mul, this, mul_zero]

theorem fin_add {D : D7} {m n : ℕ} {x y : Mx D m n} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + y).map (infPart D) = 0 := by
  rw [Matrix.map_add _ (map_add (infPart D)), hx, hy, add_zero]

set_option maxHeartbeats 1000000 in

theorem exists_alg_form : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ e : Formalism.L2.Theta.AE D, IsSplitIdem D e → ∀ (n : ℕ) (w : Fin n → WO S T), (∀ p, (w p).map (infPart D) = 0) →
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧
      ℓ v = 1 ∧ ∀ p, IsAlgebraic ℚ (ℓ (heisO ψ S T (w p) v)) := by
  intro D ψ θ S T sS sT ΛS ΛT v hv hS hT e he n w hw
  classical
  have hψ : IsStdChar D ψ (-1) := hv.1
  obtain ⟨hd, -, hsg⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  set Λ : AddSubgroup (WO S T) := latO S T (ΛS : Set (Fin S.rank → D.host.E))
    (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛdef
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ := fun a ha =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha]))
  have hΛfin : ∀ u ∈ Λ, u.map (infPart D) = 0 := fun u hu => latO_fin hu
  have hth : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hvth : IsThetaFunO ψ S T v := hv.2.theta
  have hlat : IsLatVac (heisO ψ S T) Λ v := hv.2.lat
  have hsign : ∀ u ∈ Λ, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ heisO ψ S T u v = ε • v := fun u hu => by
    obtain ⟨ε, hε, h⟩ := hsg v hlat u hu
    exact ⟨ε, hε, h v hlat⟩
  have hεQ : ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ε ∈ Qb ∧ ε ≠ 0 := by
    rintro ε (rfl | rfl)
    · exact ⟨one_mem _, one_ne_zero⟩
    · exact ⟨neg_mem (one_mem _), neg_ne_zero.2 one_ne_zero⟩
  have hpsi : ∀ x y : WO S T, x.map (infPart D) = 0 → y.map (infPart D) = 0 → ψ (symplO S T x y) ∈ Qb :=
    fun x y hx hy => GlobalTheory.BotFourier.psi_mem hψ hS hT hx hy
  have hpsiH : ∀ x y : WO S T, x.map (infPart D) = 0 → y.map (infPart D) = 0 → ψ (symplOH S T x y) ∈ Qb :=
    fun x y hx hy => GlobalTheory.BotFourier.psiH_mem hψ hS hT hx hy

  have hcS : IsSplitIdem D (cA D e) := isSplitIdem_conj he
  have he1 : e * e = e := he.1
  have hec : e * (cA D e) = 0 := he.2.1
  have hce : (cA D e) * e = 0 := by rw [mul_comm]; exact hec
  have hc1 : (cA D e) * (cA D e) = (cA D e) := by rw [← RingHom.map_mul, he1]
  have hcc : cA D (cA D e) = e := GlobalTheory.DualPairCheck.cA_cA e
  have hq1 : (1 - (e + (cA D e))) * (1 - (e + (cA D e))) = 1 - (e + (cA D e)) := by linear_combination he1 + hc1 + 2 * hec
  have hcq : cA D (1 - (e + (cA D e))) = 1 - (e + (cA D e)) := by
    rw [map_sub, map_one, map_add, hcc, add_comm (cA D e) e]
  have hcq0 : (cA D e) * (1 - (e + (cA D e))) = 0 := by linear_combination -hc1 - hce
  have hqc0 : cA D (1 - (e + (cA D e))) * (cA D e) = 0 := by rw [hcq, mul_comm]; exact hcq0
  have hdec : ∀ x : WO S T, (cA D e) • x + (e • x + (1 - (e + (cA D e))) • x) = x := fun x => by
    rw [← add_smul, ← add_smul, ← add_assoc, add_comm (cA D e) e, add_sub_cancel, one_smul]

  have caseB : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ℓ v = 1 → ∀ x : WO S T, x.map (infPart D) = 0 → (1 - (e + (cA D e))) • x ∈ Λ → ℓ (heisO ψ S T x v) ∈ Qb := by
    intro ℓ hinv h1 x hx hx'
    obtain ⟨ε, hε, hεv⟩ := hsign _ hx'
    have hxe : IsHalf e (e • x) := (isHalf_iff _ _).2 (by rw [smul_smul, he1])
    have hxc : IsHalf (cA D e) ((cA D e) • x) := (isHalf_iff _ _).2 (by rw [smul_smul, hc1])
    have hxq : IsHalf (1 - (e + (cA D e))) ((1 - (e + (cA D e))) • x) := (isHalf_iff _ _).2 (by rw [smul_smul, hq1])
    have horth : symplO S T (e • x) ((1 - (e + (cA D e))) • x) = 0 := symplO_eq_zero S T hcq0 hxe hxq
    have e1 : heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v = ε • heisO ψ S T (e • x) v := by
      rw [heisO_add_of_orth ψ S T horth, hεv, heisO_smul]
    have e2 : heisO ψ S T ((cA D e) • x) (heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v) =
        ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)) • heisO ψ S T x v := by
      rw [heisO_heisO, hdec x]
    have e3 : ℓ (heisO ψ S T ((cA D e) • x) (heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v)) =
        ε * ℓ (heisO ψ S T (e • x) v) := by
      rw [hinv _ hxc _ (hth _ _ hvth), e1, map_smul, smul_eq_mul]
    rw [e2, map_smul, smul_eq_mul] at e3
    have hx0 := psi_ne_zero ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x))
    have hpq : ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)) ∈ Qb :=
      hpsiH _ _ (fin_smul _ hx) (fin_add (fin_smul _ hx) (fin_smul _ hx))
    have e4 : ℓ (heisO ψ S T x v) = (ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)))⁻¹ *
        (ε * ℓ (heisO ψ S T (e • x) v)) := by
      rw [← e3, inv_mul_cancel_left₀ hx0]
    rw [e4]
    refine mul_mem (inv_mem hpq) (mul_mem (hεQ ε hε).1 ?_)
    by_cases hxΛ : e • x ∈ Λ
    · rw [hlat.2 e he _ hxΛ hxe, h1]; exact one_mem _
    · obtain ⟨l, hl, hlc, hne⟩ := dual_half he1 (fun u hu => half_fin he hu) hd (fun u hu => hΛ (cA D e) hc1 u hu) hxe hxΛ
      have h0 : ℓ (heisO ψ S T (e • x) v) = 0 := by
        have k1 := hinv l hlc _ (hth (e • x) v hvth)
        rw [heisO_comm, hlat.2 (cA D e) hcS l hl hlc, map_smul, smul_eq_mul] at k1
        have : (ψ (symplO S T l (e • x)) - 1) * ℓ (heisO ψ S T (e • x) v) = 0 := by
          rw [sub_mul, k1, one_mul, sub_self]
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
      rw [h0]; exact zero_mem _

  have step : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ℓ v = 1 → ∀ x : WO S T, x.map (infPart D) = 0 → ∃ ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ,
        (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ' (heisO ψ S T u f) = ℓ' f) ∧ ℓ' v = 1 ∧
        ℓ' (heisO ψ S T x v) ∈ Qb ∧ ∀ y : WO S T, y.map (infPart D) = 0 →
          ∃ a ∈ Qb, ℓ' (heisO ψ S T y v) = a * ℓ (heisO ψ S T y v) := by
    intro ℓ hinv h1 x hx
    by_cases hB : (1 - (e + (cA D e))) • x ∈ Λ
    · exact ⟨ℓ, hinv, h1, caseB ℓ hinv h1 x hx hB, fun y _ => ⟨1, one_mem _, (one_mul _).symm⟩⟩
    have hex : ¬ ∀ u ∈ Λ, ψ (symplO S T ((1 - (e + (cA D e))) • x) u) = 1 := fun h => hB ((hd _ (fin_smul _ hx)).2 h)
    push_neg at hex
    obtain ⟨u', hu', hne'⟩ := hex
    have huΛ : (1 - (e + (cA D e))) • u' ∈ Λ := hΛ _ hq1 u' hu'
    have huq : IsHalf (1 - (e + (cA D e))) ((1 - (e + (cA D e))) • u') := (isHalf_iff _ _).2 (by rw [smul_smul, hq1])
    rw [symplO_smul, hcq] at hne'
    have hne := psi_skew_ne hne'
    obtain ⟨ε, hε, hεv⟩ := hsign _ huΛ
    obtain ⟨hεQ', hε0⟩ := hεQ ε hε
    have hzQ : ψ (symplO S T ((1 - (e + (cA D e))) • u') x) ∈ Qb := hpsi _ _ (hΛfin _ huΛ) hx
    have hk : ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x) ≠ 0 := by
      rw [← mul_one_sub]
      exact mul_ne_zero hε0 (sub_ne_zero.2 (Ne.symm hne))
    have hcomm : ∀ w₁ : WO S T, heisO ψ S T ((1 - (e + (cA D e))) • u') (heisO ψ S T w₁ v) =
        (ψ (symplO S T ((1 - (e + (cA D e))) • u') w₁) * ε) • heisO ψ S T w₁ v := fun w₁ => by
      rw [heisO_comm, hεv, heisO_smul, smul_smul]
    refine ⟨(ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x))⁻¹ •
      (ℓ ∘ₗ (heisL ψ S T ((1 - (e + (cA D e))) • u') - (ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x)) • LinearMap.id)),
      fun y hy f hf => ?_, ?_, ?_, fun y hy => ?_⟩
    all_goals simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.sub_apply, heisL_apply,
      LinearMap.id_apply, map_sub, map_smul, smul_eq_mul]
    · have hc' : heisO ψ S T ((1 - (e + (cA D e))) • u') (heisO ψ S T y f) =
          heisO ψ S T y (heisO ψ S T ((1 - (e + (cA D e))) • u') f) := by
        rw [heisO_comm, symplO_eq_zero S T hqc0 huq hy, AddChar.map_zero_eq_one, one_smul]
      rw [hc', hinv y hy _ (hth _ _ hf), hinv y hy f hf]
    · rw [hεv, map_smul, smul_eq_mul, h1, mul_one, mul_one, inv_mul_cancel₀ hk]
    · rw [hcomm, map_smul, smul_eq_mul]
      have : ψ (symplO S T ((1 - (e + (cA D e))) • u') x) * ε * ℓ (heisO ψ S T x v) -
          ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x) * ℓ (heisO ψ S T x v) = 0 := by ring
      rw [this, mul_zero]
      exact zero_mem _
    · refine ⟨(ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x))⁻¹ *
        (ψ (symplO S T ((1 - (e + (cA D e))) • u') y) * ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x)),
        mul_mem (inv_mem (sub_mem hεQ' (mul_mem hεQ' hzQ)))
          (sub_mem (mul_mem (hpsi _ _ (hΛfin _ huΛ) hy) hεQ') (mul_mem hεQ' hzQ)), ?_⟩
      rw [hcomm, map_smul, smul_eq_mul]
      ring

  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp⟩ := hv.2.norm.1
    have := hv.2.norm.2 p hp
    simp [nrm2] at this
  obtain ⟨ℓ₀, hℓ₀, hinv₀⟩ := invariant_form (e := (cA D e)) (Λ := Λ) hc1 (by rw [hcc]; exact hec)
    (fun u hu => half_fin hcS hu) hd (fun u hu => by rw [hcc]; exact hΛ e he1 u hu) hv0
    (fun l hl hh => hlat.2 (cA D e) hcS l hl hh) (fun l hl hh => hlat.2 e he l hl (by rwa [hcc] at hh))
  have main : ∀ (n : ℕ) (w : Fin n → WO S T), (∀ p, (w p).map (infPart D) = 0) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ℓ v = 1 ∧
      ∀ p, ℓ (heisO ψ S T (w p) v) ∈ Qb := by
    intro n
    induction n with
    | zero =>
      intro w _
      refine ⟨(ℓ₀ v)⁻¹ • ℓ₀, fun u hu f hf => ?_, ?_, fun p => p.elim0⟩
      · rw [LinearMap.smul_apply, LinearMap.smul_apply, hinv₀ u hu f hf]
      · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hℓ₀]
    | succ n ih =>
      intro w hw
      obtain ⟨ℓ, hinv, h1, halg⟩ := ih (fun p => w p.castSucc) fun p => hw _
      obtain ⟨ℓ', hinv', h1', hlast, hfac⟩ := step ℓ hinv h1 (w (Fin.last n)) (hw _)
      refine ⟨ℓ', hinv', h1', fun p => ?_⟩
      induction p using Fin.lastCases with
      | last => exact hlast
      | cast q =>
        obtain ⟨a, ha, h⟩ := hfac _ (hw q.castSucc)
        rw [h]
        exact mul_mem ha (halg q)
  obtain ⟨ℓ, hinv, h1, halg⟩ := main n w hw
  exact ⟨ℓ, fun u hu f hf => hinv u hu f hf, h1, fun p => mem_algebraicClosure_iff.1 (halg p)⟩

end GlobalTheory.SplitAlgForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanSignatureFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PackLoc

theorem isEnum_cast' {S : SPar} {n k : ℕ} (h : k = n) {lam : Fin n → ℝ} {ε : Fin n → Bool} (hE : IsEnum S lam ε) :
    IsEnum S (fun i : Fin k => lam (Fin.cast h i)) (fun i => ε (Fin.cast h i)) := by
  subst h
  simpa using hE

theorem UH_mul' {n : ℕ} {H a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH H) (hb : b ∈ Formalism.QuantumDeterminants.UH H) :
    a * b ∈ Formalism.QuantumDeterminants.UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  show (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

theorem conj_mul' {n : ℕ} {B : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit B) (x y : Matrix (Fin n) (Fin n) ℂ) :
    B * (x * y) * B⁻¹ = B * x * B⁻¹ * (B * y * B⁻¹) := by
  have hBi : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).1 hB)
  calc B * (x * y) * B⁻¹ = B * x * (B⁻¹ * B) * y * B⁻¹ := by rw [hBi, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = B * x * B⁻¹ * (B * y * B⁻¹) := by simp only [Matrix.mul_assoc]

end GlobalTheory.PackLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHalfCosetRepresentativesCardDvdStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_halfCosetRepresentatives_card_dvd : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃! r, r ∈ R ∧ y - r ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ R.card ∣ k ^ (D.R.f * S.rank * T.rank) := by
  first | exact @GlobalTheory.HalfCosetCount.halfCoset_reps_card | exact GlobalTheory.HalfCosetCount.halfCoset_reps_card | (intros; apply GlobalTheory.HalfCosetCount.halfCoset_reps_card <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepIntertwinersThetaChainStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_innerStepIntertwiners_thetaChain : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → HostHyp D → R.IsChainW → R.ex_ItY := by
  first | exact @GlobalTheory.Chain.ExItY.ex_ItY_holds | exact GlobalTheory.Chain.ExItY.ex_ItY_holds | (intros; apply GlobalTheory.Chain.ExItY.ex_ItY_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_eq_exponent_add_half_index : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau) (a : ℚ), IsHeckeChar D χ → ResEta D χ n → HasInfExp D χ τ a → ∃ e : ℤ, (e : ℚ) = a + (n : ℚ) / 2 := by
  first | exact @GlobalTheory.SplitParity.exists_int_add_half | exact GlobalTheory.SplitParity.exists_int_add_half | (intros; apply GlobalTheory.SplitParity.exists_int_add_half <;> assumption)
end

