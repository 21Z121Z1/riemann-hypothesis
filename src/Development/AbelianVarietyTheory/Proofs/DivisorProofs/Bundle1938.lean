import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1911
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0154
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrix
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympUnip

open GlobalTheory.SympChange GlobalTheory.AdelicSvNQuad GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic

section Ring

variable {R κ : Type} [CommRing R] [Fintype κ]

def mulR (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun φ x := χ (quad h A x) * φ x
  map_add' φ φ' := funext fun x => mul_add _ _ _
  map_smul' a φ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mulR_apply (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R) (φ : (κ → R) → ℂ) (x : κ → R) :
    mulR χ h A φ x = χ (quad h A x) * φ x := rfl

theorem mulR_neg (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R) (φ : (κ → R) → ℂ) :
    mulR χ h (-A) (mulR χ h A φ) = φ := by
  funext x
  rw [mulR_apply, mulR_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, neg_add_cancel,
    AddChar.map_zero_eq_one, one_mul]

theorem mulR_mem [TopologicalSpace R] [IsTopologicalRing R] {χ : AddChar R ℂ} (hχ : IsLocallyConstant χ) (h : R)
    (A : Matrix κ κ R) {φ : (κ → R) → ℂ} (hφ : φ ∈ SB (κ → R)) : mulR χ h A φ ∈ SB (κ → R) :=
  ⟨(hχ.comp_continuous (continuous_quad h A)).mul hφ.1, hφ.2.mul_left⟩

theorem spAct_unipM {K : Type} [Field K] [Algebra K R] [DecidableEq κ] (S : Matrix κ κ K)
    (w : (κ → R) × (κ → R)) : spAct (unipM S) w = (w.1, S.map (algebraMap K R) *ᵥ w.1 + w.2) := by
  have h1 : (1 : Matrix κ κ K).map (algebraMap K R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h0 : (0 : Matrix κ κ K).map (algebraMap K R) = 0 := Matrix.map_zero _ (map_zero _)
  simp only [spAct, unipM, Matrix.fromBlocks_map, h1, h0, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl,
    Sum.elim_comp_inr, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, Sum.elim_inl, Sum.elim_inr]

theorem mulR_schr [Invertible (2 : R)] {K : Type} [Field K] [Algebra K R] [DecidableEq κ] (χ : AddChar R ℂ)
    (S : Matrix κ κ K) (hS : Sᵀ = S) (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    mulR χ (⅟2) (-S.map (algebraMap K R)) (schr χ w φ) =
      schr χ (spAct (unipM S) w) (mulR χ (⅟2) (-S.map (algebraMap K R)) φ) := by
  have hA : (-S.map (algebraMap K R))ᵀ = -S.map (algebraMap K R) := by
    rw [Matrix.transpose_neg, ← Matrix.transpose_map, hS]
  funext x
  rw [spAct_unipM, mulR_apply]
  simp only [schr]
  rw [mulR_apply, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_add _ hA,
    Matrix.neg_mulVec, neg_neg]

end Ring

variable {F : Type} [Field F] [NumberField F]

theorem eventually_integral (z : Af F) : ∀ᶠ v : Pl F in cofinite, evalV F v z ∈ v.adicCompletionIntegers F := z.2

theorem eventually_evFin (a : AF F) : ∀ᶠ v : Pl F in cofinite, evFin F v a ∈ v.adicCompletionIntegers F :=
  eventually_integral (sndA F a)

theorem exists_finite_trivial (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) : ∃ I : Set (Pl F), I.Finite ∧
    ∀ z : Af F, (∀ v, evalV F v z ∈ v.adicCompletionIntegers F) → (∀ v ∈ I, evalV F v z = 0) → finChar ψ z = 1 := by
  let f : (∀ v : Pl F, v.adicCompletionIntegers F) → FiniteAdeleRing (𝓞 F) F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
  have hf : Continuous f := RestrictedProduct.isEmbedding_structureMap.continuous
  have hlc : IsLocallyConstant (fun y => finChar ψ (f y)) := (finChar_isLocallyConstant ψ hψ).comp_continuous hf
  have h0 := hlc.eventually_eq 0
  rw [Filter.Eventually, nhds_pi, Filter.mem_pi] at h0
  obtain ⟨I, hI, t, ht, hs⟩ := h0
  refine ⟨I, hI, fun z hz hz0 => ?_⟩
  have hy : (fun v : Pl F => (⟨evalV F v z, hz v⟩ : v.adicCompletionIntegers F)) ∈ I.pi t := fun v hv => by
    have : (⟨evalV F v z, hz v⟩ : v.adicCompletionIntegers F) = 0 := Subtype.ext (hz0 v hv)
    exact Set.mem_of_eq_of_mem this (mem_of_mem_nhds (ht v))
  have h1 : finChar ψ z = finChar ψ 0 := hs hy
  rw [h1, AddChar.map_zero_eq_one]

theorem finChar_eq_finprod (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (z : Af F) :
    (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evalV F v z)).Finite ∧
      finChar ψ z = ∏ᶠ v : Pl F, GlobalTheory.LatVac.psiAt ψ v (evalV F v z) := by
  classical
  obtain ⟨I, hI, h⟩ := exists_finite_trivial ψ hψ
  have hT : (I ∪ {v | evalV F v z ∉ v.adicCompletionIntegers F}).Finite := hI.union (eventually_integral z)
  have hloc : ∀ (v : Pl F) (y : Fv F v), GlobalTheory.LatVac.psiAt ψ v y = finChar ψ (singleFin v y) := fun _ _ => rfl
  have hsub : (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evalV F v z)) ⊆ hT.toFinset := by
    intro v hv
    by_contra hn
    rw [Set.Finite.coe_toFinset, Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
    refine hv ((hloc v _).trans (h _ (fun u => ?_) fun u hu => ?_))
    · by_cases huv : u = v
      · subst huv
        rw [evalV_singleFin_self]; exact hn.2
      · rw [evalV_singleFin_ne huv]; exact zero_mem _
    · exact evalV_singleFin_ne (fun e : u = v => hn.1 (e ▸ hu)) _
  refine ⟨hT.toFinset.finite_toSet.subset hsub, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  set s : Af F := ∑ v ∈ hT.toFinset, singleFin v (evalV F v z) with hs
  have hev : ∀ u, evalV F u s = if u ∈ hT.toFinset then evalV F u z else 0 := by
    intro u
    rw [hs, map_sum]
    split_ifs with hu
    · rw [Finset.sum_eq_single_of_mem u hu fun v _ hv => evalV_singleFin_ne hv.symm _, evalV_singleFin_self]
    · exact Finset.sum_eq_zero fun v hv => evalV_singleFin_ne (fun e : u = v => hu (e ▸ hv)) _
  have h1 : finChar ψ (z - s) = 1 := by
    refine h _ (fun u => ?_) fun u hu => ?_
    · rw [map_sub, hev]
      split_ifs with hu
      · rw [sub_self]; exact zero_mem _
      · rw [Set.Finite.mem_toFinset, Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hu
        rw [sub_zero]; exact hu.2
    · rw [map_sub, hev, if_pos (hT.mem_toFinset.2 (Or.inl hu)), sub_self]
  have h2 : ∀ T : Finset (Pl F), finChar ψ (∑ v ∈ T, singleFin v (evalV F v z)) =
      ∏ v ∈ T, GlobalTheory.LatVac.psiAt ψ v (evalV F v z) := by
    intro T
    induction T using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.prod_empty, AddChar.map_zero_eq_one]
    | insert a T ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih, hloc]
  rw [← h2, ← hs, ← one_mul (finChar ψ s), ← h1, ← AddChar.map_add_eq_mul, sub_add_cancel]

theorem psiAt_isLocallyConstant (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F) :
    IsLocallyConstant (GlobalTheory.LatVac.psiAt ψ v) :=
  (finChar_isLocallyConstant ψ hψ).comp_continuous (continuous_singleFin v)

theorem quad_mem {κ : Type} [Fintype κ] {v : Pl F} {h : Fv F v} {A : Matrix κ κ (Fv F v)} {x : κ → Fv F v}
    (hh : h ∈ v.adicCompletionIntegers F) (hA : ∀ i j, A i j ∈ v.adicCompletionIntegers F)
    (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) : quad h A x ∈ v.adicCompletionIntegers F :=
  mul_mem hh (sum_mem fun i _ => mul_mem (hx i) (sum_mem fun j _ => mul_mem (hA i j) (hx j)))

open scoped Classical in

theorem hasOp_unipM : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) → (∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (S : Matrix κ κ F), S.transpose = S →
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.unipM S) := by
  intro F _ _ ψ hψ hunr _ κ _ _ S hS
  let A : Matrix κ κ (AF F) := -S.map (algebraMap F (AF F))
  let Av : ∀ v : Pl F, Matrix κ κ (Fv F v) := fun v => -S.map (algebraMap F (Fv F v))
  have hAv : ∀ v, A.map (evFin F v : AF F →+* Fv F v) = Av v := fun v => by
    refine Matrix.ext fun i j => ?_
    change evFin F v (-algebraMap F (AF F) (S i j)) = -algebraMap F (Fv F v) (S i j)
    rw [map_neg, AlgHom.commutes]
  let q : AF F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
  let hi := q (⅟2)
  let Ai := A.map q
  refine ⟨mulR ψ (⅟2) A, SchwartzMap.smulLeftCLM ℂ (archMul hi Ai),
    fun v => mulR (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (Av v), fun f => ?_, mulQ_mem ψ hψ _ A,
    fun w Φ _ => mulR_schr ψ S hS w Φ, fun v => ?_, fun v φ _ h0 => ?_,
    fun v w φ _ => mulR_schr _ S hS w φ, ?_, fun f φ _ hφ => ?_⟩
  · refine ⟨SchwartzMap.smulLeftCLM ℂ (archMul hi (-Ai)) f, SchwartzMap.ext fun y => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
      SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_smul, archMul, archMul, eChar_apply,
      eChar_apply, ← Complex.exp_add, quad_neg, map_neg, neg_neg]
    rw [show ∀ a : ℂ, a = 0 → Complex.exp a • f y = f y from fun a ha => by rw [ha, Complex.exp_zero, one_smul]]
    push_cast
    ring
  · have hlc := psiAt_isLocallyConstant ψ hψ.1 v
    refine le_antisymm ?_ fun φ hφ => ⟨mulR _ (⅟2) (-Av v) φ, mulR_mem hlc _ _ hφ, ?_⟩
    · rintro _ ⟨φ, hφ, rfl⟩
      exact mulR_mem hlc _ _ hφ
    · have := mulR_neg (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-Av v) φ
      rwa [neg_neg] at this
  · rw [← mulR_neg (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (Av v) φ]
    exact (congrArg _ h0).trans (map_zero _)
  · have h2 : ∀ᶠ v : Pl F in cofinite, evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := eventually_evFin _
    have h3 : ∀ᶠ v : Pl F in cofinite, ∀ i j, evFin F v (A i j) ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => eventually_all.2 fun j => eventually_evFin (A i j)
    filter_upwards [hunr, h2, h3] with v hv h2 h3
    funext x
    rw [mulR_apply]
    by_cases hx : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
    · rw [GlobalTheory.VacAny.evFin_invOf_two] at h2
      have h4 := (hv 1).2 (one_mem _) _ (quad_mem (A := Av v) h2 (fun i j => by rw [← hAv v]; exact h3 i j) hx)
      rw [one_mul] at h4
      rw [GlobalTheory.LatVac.psiAt_apply, h4, one_mul]
    · rw [indO, Set.indicator_of_notMem hx, mul_zero]
  · funext x
    have hfin : (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite := by
      have h3 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
        eventually_all.2 fun i => eventually_evFin (x i)
      have h4 : ∀ᶠ v : Pl F in cofinite, (φ v fun i => evFin F v (x i)) = 1 := by
        filter_upwards [hφ, h3] with v hv h3
        rw [hv, indO, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3)]
        rfl
      exact h4
    have hq : ∀ v : Pl F, evalV F v (p2 (quad (⅟2) A x)) = quad (⅟2) (Av v) fun i => evFin F v (x i) := fun v => by
      have := map_quad (evFin F v : AF F →+* Fv F v) (⅟2) A x
      rw [hAv] at this
      exact this.trans (congrArg (fun t => quad t (Av v) fun i => evFin F v (x i)) GlobalTheory.VacAny.evFin_invOf_two)
    obtain ⟨hs, hp⟩ := finChar_eq_finprod ψ hψ.1 (p2 (quad (⅟2) A x))
    simp only [hq] at hs hp
    have h3 : ψ (mk (p1 (quad (⅟2) A x)) 0) = archMul hi Ai fun i => evI F (x i) := by
      have e1 : evI F (mk (p1 (quad (⅟2) A x)) 0) = quad hi Ai fun i => evI F (x i) := map_quad q (⅟2) A x
      rw [hψ.2.2 _ (at_mk _), e1, archMul, eChar_apply]
      congr 1
      push_cast
      ring
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mulR_apply]
    rw [finprod_mul_distrib hs hfin, ← hp, map_eq_mul ψ, h3,
      SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul]
    ring

end GlobalTheory.SympUnip

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTopGridStageExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor NegIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SqTower.TopGridExists

open Matrix in

theorem exists_isONBasis {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {ε : Fin k → Bool}
    (hG : Bᴴ * G * B = Formalism.REAL.Jm ε) (hs : s * B = B * Formalism.REAL.Jm ε) :
    ∃ (B' : Matrix (Fin k) (Fin k) ℂ) (p : ℕ), IsONBasis G s B' p := by
  obtain ⟨π, hπ⟩ := GlobalTheory.FockOrder.exists_sortPerm ε
  generalize (Finset.univ.filter fun a => ε a = true).card = p at hπ
  have hJ : (Matrix.diagonal fun a => (((if ε a then 1 else -1 : ℝ)) : ℂ)) = Formalism.REAL.Jm ε := by
    unfold Formalism.REAL.Jm
    congr 1
    funext a
    cases ε a <;> simp
  refine ⟨B.submatrix id π, p, fun a => if a.val < p then 1 else -1, fun a => ?_, ?_, ?_⟩
  · by_cases ha : a.val < p
    · left; simp [ha]
    · right; simp [ha, not_lt.1 ha]
  · have e : (B.submatrix id π)ᴴ * G * B.submatrix id π = (Bᴴ * G * B).submatrix π π := by
      ext a b; simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [e, hG, ← hJ, Matrix.submatrix_diagonal_equiv]
    congr 1; funext a; simp [hπ a]
  · have e : s * B.submatrix id π = (s * B).submatrix id π := by
      ext a b; simp [Matrix.mul_apply]
    rw [e, hs, ← Matrix.submatrix_mul_equiv (e₂ := π), ← hJ, Matrix.submatrix_diagonal_equiv]
    congr 2; funext a; simp [hπ a]

open Matrix GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle in

theorem exists_rig_of_frame {D : D7} {V : HSp D} (A : Fr V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : ∃ r : Rig V, r.Λ = Λ ∧ r.s = A.cart ∧ r.Is := by
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E V.rank Λ hΛ.1
  have hτ : ∀ τ : D.what₂.Tau, ∃ (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (p : ℕ),
      IsONBasis (gramAt D V τ) (A.cart τ) B p := fun τ => by
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
    have h1 := Matrix.mul_nonsing_inv _ hu
    refine exists_isONBasis (B := (A.fr τ)⁻¹) (ε := A.ε τ) ?_ ?_
    · rw [← A.fr_gram τ]
      simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.one_mul]
    · simp only [Fr.cart, Matrix.mul_assoc, h1, Matrix.mul_one]
  choose B hB using hτ
  exact ⟨⟨Λ, β, A.cart, B⟩, rfl, rfl, hΛ, hβ, fun τ => ⟨GlobalTheory.CompactFockAction.cart_isCartanInv A τ, hB τ⟩⟩

set_option maxHeartbeats 1000000 in
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Doubling GlobalTheory.SqTower.TopExists in

theorem top_grid_exists : GlobalTheory.FunPr.Hypotheses₂ →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ X : TriG G i j, TopGrid W i j X ∧ IsStageC W i j (pp D j) (qq D j) X := by
  intro _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G W i j => ?_⟩⟩
  have hi := i.2
  have hj := j.2
  have a := node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨by omega, by omega⟩
  have a' := node_isV G hL (X := .grid i j) ⟨by omega, by omega⟩
  have b := node_isV G hL (X := .grid i (j + 1)) ⟨by omega, by omega⟩
  have b' := node_isV G hL (X := .grid (i + 1) j) ⟨by omega, by omega⟩
  have ng : ∀ {X : LSp D} {ν q : ℕ}, X.IsV ν q → NegIdx X.sp q := fun h =>
    GlobalTheory.Grid.Vertex.negIdx_of_sig _ _ h.sigOK fun τ => by rw [h.sig, h.rank]
  have ho : ∀ (x : (G.V (.grid i (j + 1))).V) (y : (G.V (.grid (i + 1) j)).V),
      (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).hD (LinearMap.inl D.host.E _ _ x) (LinearMap.inr D.host.E _ _ y) = 0 :=
    fun x y => by simp [HSpace.hD, orthSum_apply]
  have hsig := sigOK_hsum b.sigOK b'.sigOK
  have hsd := GlobalTheory.Twist.OrthSum.selfDual_hsum b.sd b'.sd
  have hneg := negIdx_of_orth rfl _ _ (isIsomEmb_inl _ _) (isIsomEmb_inr _ _) ho (ng b) (ng b')
  obtain ⟨FA, hFA⟩ := exists_isGridFr W (X := .grid (i + 1) (j + 1)) ⟨by omega, by omega⟩
  obtain ⟨FA', hFA'⟩ := exists_isGridFr W (X := .grid i j) ⟨by omega, by omega⟩
  obtain ⟨FV, hFV⟩ := exists_isGridFr W (X := .grid i (j + 1)) ⟨by omega, by omega⟩
  obtain ⟨FV', hFV'⟩ := exists_isGridFr W (X := .grid (i + 1) j) ⟨by omega, by omega⟩
  obtain ⟨rA, eA, sA, hA⟩ := exists_rig_of_frame FA _ a.sd
  obtain ⟨rA', eA', sA', hA'⟩ := exists_rig_of_frame FA' _ a'.sd
  obtain ⟨rW, eW, sW, hW⟩ := exists_rig_of_frame (frSum FV FV') _ hsd
  have hrk : (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank = rankV D (i + 1) (j + 1) + rankV D i j := by
    have h0 : (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))).rank =
      (G.V (.grid i (j + 1))).rank + (G.V (.grid (i + 1) j)).rank := rfl
    have h1 : (G.V (.grid i (j + 1))).rank = rankV D i (j + 1) := b.rank
    have h2 : (G.V (.grid (i + 1) j)).rank = rankV D (i + 1) j := b'.rank
    rw [h0, h1, h2]; simp only [rankV]; ring
  have htg : ∀ (AV : Fr (G.V (.grid i (j + 1)))) (AV₁ : Fr (G.V (.grid (i + 1) j))), IsGridFr W _ AV → IsGridFr W _ AV₁ →
      rW.s = (frSum AV AV₁).cart := fun AV AV₁ h h₁ => by
    rw [sW]; funext τ
    rw [GlobalTheory.SquareAlg.cart_frSum, GlobalTheory.SquareAlg.cart_frSum, (h τ).2, (h₁ τ).2, (hFV τ).2, (hFV' τ).2]
  have ch := chars G hL W i j
  have hψ := W.ψ_std
  have hθ := W.θ_is
  have hη := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have rA1 : (G.V (.grid (i + 1) (j + 1))).rank = rankV D (i + 1) (j + 1) := a.rank
  have rA2 : (G.V (.grid i j)).rank = rankV D i j := a'.rank
  choose ω hω using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη true (G.V (.grid (i + 1) (j + 1))) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) (ch t).2.1
    (ch t).2.2.2.1 (by rw [rA1]; exact (ch t).2.2.2.2.2.1) (by rw [hrk]; exact (ch t).2.2.2.2.2.2.2)
  choose ω' hω' using fun t => GlobalTheory.ConstRatio.exists_isWeil hψ hη false (G.V (.grid i j)) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) (ch t).1
    (ch t).2.2.1 (by rw [rA2]; exact (ch t).2.2.2.2.1) (by rw [hrk]; exact (ch t).2.2.2.2.2.2.1)
  have hneg' : IsSelfDualC (neg (G.V (.grid (i + 1) (j + 1)))) rA.Λ := by
    refine ⟨hA.1.1, fun y => (hA.1.2 y).trans (forall₂_congr fun x _ => ⟨fun ⟨c, hc⟩ => ⟨-c, ?_⟩, fun ⟨c, hc⟩ => ⟨-c, ?_⟩⟩)⟩
    · simp [neg_gram, hc]
    · simp [neg_gram] at hc ⊢
      exact neg_eq_iff_eq_neg.2 hc
  obtain ⟨vac, hv⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ (neg (G.V (.grid (i + 1) (j + 1)))) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) (fun τ => -rA.s τ) rW.s
    (sigOK_sgn true a.sigOK) hsig (fun τ => isCartanInv_sgn true _ τ (hA.2.2 τ).1) (fun τ => (hW.2.2 τ).1) rA.Λ rW.Λ hneg' hW.1
  obtain ⟨vac', hv'⟩ := GlobalTheory.VacuumO.vacExists D W.ψ W.θ hψ hθ (G.V (.grid i j)) (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) rA'.s rW.s
    a'.sigOK hsig (fun τ => (hA'.2.2 τ).1) (fun τ => (hW.2.2 τ).1) rA'.Λ rW.Λ hA'.1 hW.1
  choose e he using idem_exists G hL W
  choose c hc using fun t w => GlobalTheory.ConstRatio.exists_expAt (nuH G t i j) w
  have hI : ∀ t, (∏ w ∈ locPl G t, w.asIdeal ^ c t w) ≠ ⊥ := fun t =>
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  choose f hf _ using fun t => GlobalTheory.T.first_standard_pair_member_has_theta_function D W.ψ W.θ _ (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) rA rW _ _ _ _ _ hA hW (ch t).2.2.1 (he t) (hI t) hv
  choose f' hf' _ using fun t =>
    GlobalTheory.T.exists_thetaFunction_standardPairSecond D W.ψ W.θ _ (hsum (G.V (.grid i (j + 1))) (G.V (.grid (i + 1) j))) rA' rW _ _ _ _ (G.V (.grid (i + 1) (j + 1))).rank _ hA' hW (ch t).2.2.1 (he t) (hI t) hv'
  obtain ⟨m, fd, hm⟩ := GlobalTheory.ConstRatio.exists_meas (G.V (.grid (i + 1) (j + 1)))
  obtain ⟨m', fd', hm'⟩ := GlobalTheory.ConstRatio.exists_meas (G.V (.grid i j))
  refine ⟨⟨rA, rA', rW, ω, ω', vac, vac', e, c, f, f', m, fd, m', fd'⟩,
    ⟨eA, eA', eW, sA.trans (funext fun τ => (hFA τ).2), sA'.trans (funext fun τ => (hFA' τ).2), htg⟩,
    le_rfl, le_rfl, by rw [rA1], by rw [rA2], ng a, ng a', hneg,
    ⟨by rw [hrk, rA1, rA2], hA, hA', hW, hω, hω', hv, hv', he, fun t w _ => hc t w, hf, hf', hm, hm'⟩⟩

end GlobalTheory.SqTower.TopGridExists

end
end

