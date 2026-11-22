import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFunctionFactorizableSum
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1508
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenAtAllPlaces
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

noncomputable section

open scoped Classical

namespace GlobalTheory.VacEig

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_schwartz_one (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ Φ : SchwartzMap V ℂ, Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

theorem eventually_int' (x : κ → AF F) :
    ∀ᶠ u in cofinite, ∀ i, evFin F u (x i) ∈ u.adicCompletionIntegers F :=
  Filter.eventually_all.mpr fun i => (x i).2.2

theorem finite_mulSupport' (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (x : κ → AF F) : (Function.mulSupport fun u => φ u (fun i => evFin F u (x i))).Finite := by
  have h : ∀ᶠ u in cofinite, φ u (fun i => evFin F u (x i)) = 1 := by
    filter_upwards [hφ, eventually_int' x] with u hu hx
    rw [hu]
    simp [indO, Set.indicator, hx]
  exact (Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp

theorem pure_split (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) (x : κ → AF F) :
    pure f φ x = φ v (fun i => evFin F v (x i)) *
      (f (fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i))) := by
  have hfin := finite_mulSupport' _ hφ x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [← mul_finprod_cond_ne v hfin]
  ring

theorem pure_update_split (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) (g : (κ → Fv F v) → ℂ) (x : κ → AF F) :
    pure f (Function.update φ v g) x = g (fun i => evFin F v (x i)) *
      (f (fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i))) := by
  have hφ' : ∀ᶠ u in cofinite, Function.update φ v g u = indO u := by
    filter_upwards [hφ, (Set.finite_singleton v).compl_mem_cofinite] with u hu hv
    rw [Function.update_of_ne hv, hu]
  rw [pure_split f _ hφ' v x, Function.update_self]
  congr 2
  exact finprod_congr fun u => finprod_congr fun hu => by rw [Function.update_of_ne hu]

theorem vac_eig : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ →
    ∀ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ,
    (∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d),
      M.co.rho ψ γ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = c v γ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) →
    ∀ v, ∀ γ ∈ latAtV X W v, locOp ψ v (locPt v (M.co.e γ)) (M.vac v) = c v γ • M.vac v := by
  intro F E _ _ _ _ _ σ n d X W M ψ hM c hc v γ hγ
  have hvacO : ∀ᶠ u in cofinite, M.vac u = indO u := by
    filter_upwards [hM.std] with u hu
    rw [hu]
    rfl
  obtain ⟨f, hf⟩ := exists_schwartz_one (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  have e2 := hc v γ hγ f
  rw [GlobalTheory.T.weil_rep_pure_tensor_local M ψ v γ (at_latAtV hγ) f M.vac hvacO] at e2
  choose w hw using fun u => Function.ne_iff.mp (hM.vac u).2.1
  have hT : {u | M.vac u ≠ indO u ∧ u ≠ v}.Finite :=
    (Filter.eventually_cofinite.mp hvacO).subset fun u hu => hu.1
  set T := hT.toFinset with hTdef
  funext z
  set y : Fin n × Fin d → Af F := fun i => singleFin v (z i) + ∑ u ∈ T, singleFin u (w u i) with hy
  set x := mkPt (fun _ => (0 : mixedEmbedding.mixedSpace F)) y with hx
  have hxv : (fun i => evFin F v (x i)) = z := by
    funext i
    rw [hx, evFin_mkPt, hy]
    simp only [map_add, map_sum, evalV_singleFin_self]
    rw [Finset.sum_eq_zero, add_zero]
    intro u hu
    have : u ≠ v := (hT.mem_toFinset.mp hu).2
    exact evalV_singleFin_ne (Ne.symm this) _
  have hxu : ∀ u, u ≠ v → M.vac u (fun i => evFin F u (x i)) ≠ 0 := by
    intro u huv
    have hcomp : ∀ i, evFin F u (x i) = ∑ u' ∈ T, evalV F u (singleFin u' (w u' i)) := by
      intro i
      rw [hx, evFin_mkPt, hy]
      simp only [map_add, map_sum, evalV_singleFin_ne huv, zero_add]
    by_cases huT : u ∈ T
    · have : (fun i => evFin F u (x i)) = w u := by
        funext i
        rw [hcomp, Finset.sum_eq_single_of_mem u huT, evalV_singleFin_self]
        intro u' _ hne
        exact evalV_singleFin_ne (Ne.symm hne) _
      rw [this]
      exact hw u
    · have hstd : M.vac u = indO u := by
        by_contra h
        exact huT (hT.mem_toFinset.mpr ⟨h, huv⟩)
      have : (fun i => evFin F u (x i)) = 0 := by
        funext i
        rw [hcomp, Finset.sum_eq_zero]
        · rfl
        intro u' hu'
        have hne : u ≠ u' := fun h => huT (h ▸ hu')
        exact evalV_singleFin_ne hne _
      rw [this, hstd]
      simp [indO, Set.indicator, zero_mem]
  have hR : (f fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), M.vac u (fun i => evFin F u (x i)) ≠ 0 := by
    refine mul_ne_zero ?_ (finprod_ne_zero fun u => ?_)
    · have : (fun i => evI F (x i)) = 0 := by
        funext i
        rw [hx, evI_mkPt]
        rfl
      rw [this, hf]
      exact one_ne_zero
    · rw [finprod_eq_if]
      split_ifs with huv
      · exact hxu u huv
      · exact one_ne_zero
  have h := congrFun e2 x
  rw [Pi.smul_apply, smul_eq_mul, pure_update_split f M.vac hvacO v _ x, pure_split f M.vac hvacO v x, hxv] at h
  rw [Pi.smul_apply, smul_eq_mul]
  exact mul_right_cancel₀ hR (by linear_combination h)

end GlobalTheory.VacEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumUniqueProductEigen
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine
open scoped Classical

namespace GlobalTheory.VacFactor

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mem_SB_iff' {X : Type} [TopologicalSpace X] (f : X → ℂ) :
    f ∈ SB X ↔ IsLocallyConstant f ∧ HasCompactSupport f := Iff.rfl

theorem pt_ext {a b : κ → Af F} (h : ∀ u i, evalV F u (a i) = evalV F u (b i)) : a = b :=
  funext fun i => Subtype.ext (funext fun u => h u i)

def setAt (y : κ → Af F) (v : Pl F) (z : κ → Fv F v) : κ → Af F :=
  fun i => y i + singleFin v (z i - evalV F v (y i))

theorem evalV_setAt_self (y : κ → Af F) (v : Pl F) (z : κ → Fv F v) (i : κ) :
    evalV F v (setAt y v z i) = z i := by
  rw [setAt, map_add, evalV_singleFin_self]; ring

theorem evalV_setAt_ne (y : κ → Af F) {v u : Pl F} (h : u ≠ v) (z : κ → Fv F v) (i : κ) :
    evalV F u (setAt y v z i) = evalV F u (y i) := by
  rw [setAt, map_add, evalV_singleFin_ne h, add_zero]

theorem setAt_eval (y : κ → Af F) (v : Pl F) : setAt y v (fun i => evalV F v (y i)) = y := by
  funext i; simp [setAt]

theorem setAt_add (y : κ → Af F) (v : Pl F) (z p : κ → Fv F v) :
    (setAt y v z + fun i => singleFin v (p i)) = setAt y v (z + p) := by
  apply pt_ext
  intro u i
  by_cases h : u = v
  · subst h
    simp only [Pi.add_apply, map_add, evalV_setAt_self, evalV_singleFin_self]
  · simp only [Pi.add_apply, map_add, evalV_setAt_ne y h, evalV_singleFin_ne h, add_zero]

def setOn (S : Finset (Pl F)) (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) : κ → Af F :=
  fun i => y i + ∑ v ∈ S, singleFin v (z₀ v i - evalV F v (y i))

theorem evalV_setOn_mem {S : Finset (Pl F)} (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) {u : Pl F} (hu : u ∈ S)
    (i : κ) : evalV F u (setOn S y z₀ i) = z₀ u i := by
  rw [setOn, map_add, map_sum, Finset.sum_eq_single u (fun w _ hw => evalV_singleFin_ne (Ne.symm hw) _)
    (fun h => absurd hu h), evalV_singleFin_self]
  ring

theorem evalV_setOn_not {S : Finset (Pl F)} (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) {u : Pl F} (hu : u ∉ S)
    (i : κ) : evalV F u (setOn S y z₀ i) = evalV F u (y i) := by
  rw [setOn, map_add, map_sum, Finset.sum_eq_zero (fun w hw => evalV_singleFin_ne (by rintro rfl; exact hu hw) _),
    add_zero]

theorem setOn_empty (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) : setOn ∅ y z₀ = y := by
  funext i; simp [setOn]

theorem setAt_setOn {S : Finset (Pl F)} (y : κ → Af F) (z₀ : ∀ v : Pl F, κ → Fv F v) {w : Pl F} (hw : w ∉ S) :
    setAt (setOn S y z₀) w (z₀ w) = setOn (insert w S) y z₀ := by
  apply pt_ext
  intro u i
  by_cases h : u = w
  · subst h
    rw [evalV_setAt_self, evalV_setOn_mem y z₀ (Finset.mem_insert_self u S)]
  · rw [evalV_setAt_ne _ h]
    by_cases hS : u ∈ S
    · rw [evalV_setOn_mem y z₀ hS, evalV_setOn_mem y z₀ (Finset.mem_insert_of_mem hS)]
    · rw [evalV_setOn_not y z₀ hS, evalV_setOn_not y z₀ (by simp [h, hS])]

theorem slice_mem_SB {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (y : κ → Af F) (v : Pl F) :
    (fun z : κ → Fv F v => g (setAt y v z)) ∈ SB (κ → Fv F v) := by
  obtain ⟨hlc, hcs⟩ := (mem_SB_iff' g).mp hg
  have hcont : Continuous fun z : κ → Fv F v => setAt y v z :=
    continuous_pi fun i => continuous_const.add
      ((continuous_singleFin v).comp ((continuous_apply i).sub continuous_const))
  have hE : Continuous fun x : κ → Af F => fun i => evalV F v (x i) :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
  refine (mem_SB_iff' _).mpr ⟨hlc.comp_continuous hcont, ?_⟩
  refine HasCompactSupport.intro (hcs.isCompact.image hE) fun z hz => ?_
  by_contra h
  exact hz ⟨setAt y v z, subset_tsupport _ h, funext fun i => evalV_setAt_self y v z i⟩

theorem locOp_slice (ψ : AddChar (AF F) ℂ) (g : (κ → Af F) → ℂ) (y : κ → Af F) (v : Pl F)
    (p : (κ → Fv F v) × (κ → Fv F v)) (c : ℂ) (h : finOp ψ v p g = c • g) :
    locOp ψ v p (fun z => g (setAt y v z)) = c • fun z => g (setAt y v z) := by
  funext z
  have e := congrFun h (setAt y v z)
  have hz : (fun i => evalV F v (setAt y v z i)) = z := funext fun i => evalV_setAt_self y v z i
  simp only [finOp, Pi.smul_apply, smul_eq_mul, hz, setAt_add] at e
  simp only [locOp, Pi.smul_apply, smul_eq_mul]
  exact e

theorem eigen_place (ψ : AddChar (AF F) ℂ) (v : Pl F) (vacv : (κ → Fv F v) → ℂ)
    (Qv : Set (((κ → Fv F v) × (κ → Fv F v)) × ℂ))
    (hline : ∀ φ ∈ SB (κ → Fv F v), (∀ q ∈ Qv, locOp ψ v q.1 φ = q.2 • φ) → ∃ a : ℂ, φ = a • vacv)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (heig : ∀ q ∈ Qv, finOp ψ v q.1 g = q.2 • g)
    (y : κ → Af F) (z₁ : κ → Fv F v) :
    g y * vacv z₁ = g (setAt y v z₁) * vacv (fun i => evalV F v (y i)) := by
  obtain ⟨a, ha⟩ := hline _ (slice_mem_SB hg y v) fun q hq => locOp_slice ψ g y v q.1 q.2 (heig q hq)
  have h1 := congrFun ha (fun i => evalV F v (y i))
  have h2 := congrFun ha z₁
  simp only [Pi.smul_apply, smul_eq_mul, setAt_eval] at h1 h2
  rw [h1, h2]; ring

theorem eigen_finset (ψ : AddChar (AF F) ℂ) (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (Q : ∀ v : Pl F, Set (((κ → Fv F v) × (κ → Fv F v)) × ℂ))
    (hline : ∀ v, ∀ φ ∈ SB (κ → Fv F v), (∀ q ∈ Q v, locOp ψ v q.1 φ = q.2 • φ) → ∃ a : ℂ, φ = a • vac v)
    {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) (heig : ∀ v, ∀ q ∈ Q v, finOp ψ v q.1 g = q.2 • g)
    (z₀ : ∀ v : Pl F, κ → Fv F v) (y : κ → Af F) (S : Finset (Pl F)) :
    g y * ∏ v ∈ S, vac v (z₀ v) = g (setOn S y z₀) * ∏ v ∈ S, vac v (fun i => evalV F v (y i)) := by
  induction S using Finset.induction_on with
  | empty => simp [setOn_empty]
  | insert w S hw ih =>
    have e := eigen_place ψ w (vac w) (Q w) (hline w) hg (heig w) (setOn S y z₀) (z₀ w)
    rw [setAt_setOn y z₀ hw] at e
    have hyw : (fun i => evalV F w (setOn S y z₀ i)) = fun i => evalV F w (y i) :=
      funext fun i => evalV_setOn_not y z₀ hw i
    rw [hyw] at e
    rw [Finset.prod_insert hw, Finset.prod_insert hw]
    linear_combination (vac w (z₀ w)) * ih + (∏ v ∈ S, vac v (fun i => evalV F v (y i))) * e

theorem finprod_split (S : Finset (Pl F)) (y : κ → Af F) (A : Pl F → ℂ) :
    (∏ᶠ u, if u ∈ S then A u else indO u (fun i => evalV F u (y i))) =
      (∏ u ∈ S, A u) * ∏ᶠ u, if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i)) := by
  have hf1 : Function.mulSupport (fun u => if u ∈ S then A u else (1 : ℂ)) ⊆ (S : Set (Pl F)) := by
    intro u hu
    by_contra h
    exact hu (by simp only [Finset.mem_coe] at h; simp [h])
  have hint : ∀ᶠ u in cofinite, ∀ i, evalV F u (y i) ∈ HeightOneSpectrum.adicCompletionIntegers F u :=
    Filter.eventually_all.mpr fun i => (y i).2
  have hf2 : (Function.mulSupport fun u => if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i))).Finite := by
    have h : ∀ᶠ u in cofinite, (if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i))) = 1 := by
      filter_upwards [hint] with u hu
      split_ifs
      · rfl
      · simp [indO, Set.indicator, hu]
    exact (Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp
  have hsplit : (fun u => if u ∈ S then A u else indO u (fun i => evalV F u (y i))) =
      fun u => (if u ∈ S then A u else (1 : ℂ)) * (if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i))) := by
    funext u; split_ifs <;> simp
  rw [hsplit, finprod_mul_distrib ((S.finite_toSet).subset hf1) hf2, finprod_eq_prod_of_mulSupport_subset _ hf1]
  congr 1
  exact Finset.prod_congr rfl fun u hu => if_pos hu

theorem eq_smul_vacProd : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ) (Q : ∀ v : Pl F, Set (((κ → Fv F v) × (κ → Fv F v)) × ℂ)),
    (∀ v, vac v ∈ SB (κ → Fv F v)) → (∀ v, vac v ≠ 0) → (∀ᶠ v in cofinite, vac v = indO v) →
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), (∀ q ∈ Q v, locOp ψ v q.1 φ = q.2 • φ) → ∃ a : ℂ, φ = a • vac v) →
    ∀ g ∈ SB (κ → Af F), (∀ v, ∀ q ∈ Q v, finOp ψ v q.1 g = q.2 • g) → ∃ a : ℂ, g = a • vacProd vac := by
  intro F _ _ κ _ ψ vac Q _ hne hvacO hline g hg heig
  obtain ⟨m, φ, -, hφstd, hrep⟩ := GlobalTheory.SBRestrProd.sb_eq_sum_restrProd g hg
  have hgood : ∀ᶠ v in cofinite, (∀ j, φ j v = indO v) ∧ vac v = indO v :=
    (Filter.eventually_all.mpr hφstd).and hvacO
  have hfin := Filter.eventually_cofinite.mp hgood
  set S := hfin.toFinset with hSdef
  have hout : ∀ u, u ∉ S → (∀ j, φ j u = indO u) ∧ vac u = indO u := by
    intro u hu
    by_contra h
    exact hu (hfin.mem_toFinset.mpr h)
  have hz : ∀ v, ∃ z, vac v z ≠ 0 := fun v => Function.ne_iff.mp (hne v)
  choose z₀ hz₀ using hz
  have hP0 : (∏ v ∈ S, vac v (z₀ v)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => hz₀ v
  set R : (κ → Af F) → ℂ := fun y => ∏ᶠ u, if u ∈ S then (1 : ℂ) else indO u (fun i => evalV F u (y i)) with hR
  set c : ℂ := ∑ j, ∏ u ∈ S, φ j u (z₀ u) with hc
  have hvac : ∀ y, vacProd vac y = (∏ u ∈ S, vac u (fun i => evalV F u (y i))) * R y := by
    intro y
    rw [← finprod_split S y]
    unfold vacProd
    refine finprod_congr fun u => ?_
    split_ifs with h
    · rfl
    · rw [(hout u h).2]
  have hgS : ∀ y, g (setOn S y z₀) = c * R y := by
    intro y
    rw [hrep, hc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← finprod_split S y]
    refine finprod_congr fun u => ?_
    split_ifs with h
    · congr 1
      exact funext fun i => evalV_setOn_mem y z₀ h i
    · rw [(hout u h).1 j]
      congr 1
      exact funext fun i => evalV_setOn_not y z₀ h i
  refine ⟨c / ∏ v ∈ S, vac v (z₀ v), funext fun y => ?_⟩
  have key := eigen_finset ψ vac Q hline hg heig z₀ y S
  rw [hgS] at key
  rw [Pi.smul_apply, smul_eq_mul, hvac]
  field_simp
  linear_combination key

end GlobalTheory.VacFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepFinitePeriodicityPolynomialHeight
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

namespace GlobalTheory.ArchDecay

theorem per_om_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧ Per F m (om (g, h) Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨C, k, hCk⟩ := GlobalTheory.ThetaLevel.periodic_level F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  refine ⟨C, k, fun g h => ?_⟩
  obtain ⟨m, hm1, hmle, hper⟩ := hCk g h
  refine ⟨m, hm1, hmle, fun x z hz => ?_⟩
  choose a ha0 haI haz using hz
  have hz' : z = (m : AF F) • a := by
    funext i; simp [haz i]
  rw [hz']
  exact hper x a fun i => ⟨ha0 i, haI i⟩

end GlobalTheory.ArchDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepMovedArchimedeanCoordsPolynomialHeight
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

noncomputable section

namespace GlobalTheory.ArchDecay.MovSize

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

abbrev Zs (F : Type) [Field F] [NumberField F] (n d : ℕ) : Type :=
  (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)

theorem infAd_add (a b : mixedEmbedding.mixedSpace F) : infAd F (a + b) = infAd F a + infAd F b := by
  unfold infAd
  rw [map_add, map_add]
  rfl

theorem infAd_smul (t : ℝ) (a : mixedEmbedding.mixedSpace F) : infAd F (t • a) = realAd F t * infAd F a := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • a) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a
    rw [← map_mul, Algebra.smul_def]
  · show (0 : FiniteAdeleRing (𝓞 F) F) = 0 * 0
    rw [mul_zero]

theorem liftI_add (M : Model σ X W) (ζ ζ' : Zs F n d) : liftI M (ζ + ζ') = liftI M ζ + liftI M ζ' := by
  unfold liftI
  rw [← map_add]
  congr 1
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [infAd_add]

theorem liftI_smul (M : Model σ X W) (t : ℝ) (ζ : Zs F n d) : liftI M (t • ζ) = realAd F t • liftI M ζ := by
  unfold liftI
  rw [← LinearEquiv.map_smul]
  congr 1
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [infAd_smul]

theorem arch_e_liftI (M : Model σ X W) (ζ : Zs F n d) :
    (arch F (M.co.e (liftI M ζ)).1, arch F (M.co.e (liftI M ζ)).2) = ζ := by
  unfold liftI arch
  rw [LinearEquiv.apply_symm_apply]
  refine Prod.ext ?_ ?_ <;> funext i <;>
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _

variable (τ : ∀ w : InfinitePlace F, EmbOver E w)

def readC (M : Model σ X W) : Zs F n d →ₗ[ℝ] (InfinitePlace F → Fin n → Fin d → ℂ) where
  toFun ζ w i j := piInf (τ w) (liftI M ζ i j)
  map_add' ζ ζ' := by funext w i j; simp [liftI_add, map_add]
  map_smul' t ζ := by
    funext w i j
    simp only [liftI_smul, Matrix.smul_apply, RingHom.id_apply, Pi.smul_apply]
    rw [GlobalTheory.RealScalar.piInf_realAd_smul, Complex.real_smul]

theorem readC_injective (hCM : IsCMExt F E σ) (M : Model σ X W) : Function.Injective (readC τ M) := by
  rw [injective_iff_map_eq_zero]
  intro ζ hζ
  have hA := (liftI_at_movI F E σ n d X W M 1 ζ).1
  have h0 : liftI M ζ = 0 := by
    ext i j
    refine GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hCM τ _ ?_ ?_
    · intro a ha
      have := congrFun (congrFun (hA a ha) i) j
      simpa [Matrix.smul_apply] using this
    · intro w
      exact congrFun (congrFun (congrFun hζ w) i) j
  rw [← arch_e_liftI M ζ, h0, map_zero]
  refine Prod.ext ?_ ?_ <;> funext i <;> exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem norm_piInf_eq (hCM : IsCMExt F E σ) {w : InfinitePlace F} (τ₀ τ' : EmbOver E w) (z : AE F E) :
    ‖piInf τ' z‖ = ‖piInf τ₀ z‖ := by
  unfold piInf
  rcases infEmb_eq_or_conj hCM τ₀ τ' with e | e
  · rw [RingHom.comp_apply, RingHom.comp_apply, e]
  · rw [RingHom.comp_apply, RingHom.comp_apply, e, RingHom.comp_apply, Complex.norm_conj]

end GlobalTheory.ArchDecay.MovSize

open GlobalTheory.ArchDecay.MovSize in

theorem GlobalTheory.ArchDecay.movI_size : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∃ (C : ℝ) (k : ℕ), ∀ (g : UA σ X.J) (h : UA σ W.J) (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ‖movI M (g, h) ζ‖ ≤ C * ((ht g : ℝ) * ht h) ^ k * ‖ζ‖ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hCM : IsCMExt F E σ := hP.base.cm
  set L := readC B.emb M with hL
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith (LinearMap.ker_eq_bot.2 (readC_injective B.emb hCM M))
  set Lc := LinearMap.toContinuousLinearMap L with hLc
  refine ⟨K * (n * d) * ‖Lc‖, 1, fun g h ζ => ?_⟩
  have h1 : ‖movI M (g, h) ζ‖ ≤ K * ‖L (movI M (g, h) ζ)‖ := by
    have := hK.le_mul_dist (movI M (g, h) ζ) 0
    simpa [dist_eq_norm] using this
  have hB : ∀ (w : InfinitePlace F) (τ' : EmbOver E w) k l, ‖piInf τ' (liftI M ζ k l)‖ ≤ ‖L ζ‖ := by
    intro w τ' k l
    rw [norm_piInf_eq hCM (B.emb w) τ']
    exact (norm_le_pi_norm (L ζ w k) l).trans ((norm_le_pi_norm (L ζ w) k).trans (norm_le_pi_norm (L ζ) w))
  have hg : (ht (((g, h)⁻¹ : UA σ X.J × UA σ W.J)).1 : ℝ) = ht g := by
    show ((heightGL F ((g⁻¹ : UA σ X.J) : GL (Fin n) (AE F E))) : ℝ) = heightGL F (g : GL (Fin n) (AE F E))
    rw [Subgroup.coe_inv, heightGL_inv]
  have hh : (ht (((g, h)⁻¹ : UA σ X.J × UA σ W.J)).2 : ℝ) = ht h := by
    show ((heightGL F ((h⁻¹ : UA σ W.J) : GL (Fin d) (AE F E))) : ℝ) = heightGL F (h : GL (Fin d) (AE F E))
    rw [Subgroup.coe_inv, heightGL_inv]
  have hgh : (0 : ℝ) ≤ n * d * ((ht g : ℝ) * ht h) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))
  have hpos : (0 : ℝ) ≤ n * d * ((ht g : ℝ) * ht h) * ‖L ζ‖ := mul_nonneg hgh (norm_nonneg _)
  have h2 : ‖L (movI M (g, h) ζ)‖ ≤ n * d * ((ht g : ℝ) * ht h) * ‖L ζ‖ := by
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun w => ?_
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun i => ?_
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun j => ?_
    show ‖piInf (B.emb w) (liftI M (movI M (g, h) ζ) i j)‖ ≤ _
    rw [(liftI_at_movI F E σ n d X W M (g, h) ζ).2]
    have := GlobalTheory.WeilDirBound.norm_piInf_actAB_le σ n d X.J W.J (g, h)⁻¹ (liftI M ζ) ‖L ζ‖ (norm_nonneg _) hB w
      (B.emb w) i j
    rwa [hg, hh] at this
  have h3 : ‖L ζ‖ ≤ ‖Lc‖ * ‖ζ‖ := Lc.le_opNorm ζ
  have hK0 : (0 : ℝ) ≤ K := K.2
  calc ‖movI M (g, h) ζ‖ ≤ K * (n * d * ((ht g : ℝ) * ht h) * (‖Lc‖ * ‖ζ‖)) :=
        h1.trans (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 hgh)) hK0)
    _ = K * (n * d) * ‖Lc‖ * ((ht g : ℝ) * ht h) ^ 1 * ‖ζ‖ := by ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralEquivariantNonzeroStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_integral_equivariant_nonzero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (ν : kˣ →* ℂˣ) (z : ℂ), IsSmU ν → (n : ℝ) - 1 < z.re →
    IsEqv ν z (fun φ : Matrix (Fin n) (Fin n) k → ℂ => ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n)))) ∧
    ∃ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∫ g : GL (Fin n) k, φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z ∂(haarVol (KO k (Fin n))) ≠ 0 := by
  first | exact @GlobalTheory.GJForm.isEqv_integral_and_ne_zero | exact GlobalTheory.GJForm.isEqv_integral_and_ne_zero | (intros; apply GlobalTheory.GJForm.isEqv_integral_and_ne_zero <;> assumption)
end

