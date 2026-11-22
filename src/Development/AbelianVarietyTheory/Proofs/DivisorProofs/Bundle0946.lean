import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0924
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationEqPartialLogCoordsProof
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvDer

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.LawLog GlobalTheory.FactorDepth
  GlobalTheory.IsoTriv

section Two

variable {K : Type} [Field K] [CharZero K] {d : ℕ}

theorem subst_secondBlockZero_twoPointVariables {ι : Type} (Y : Fin d → MvPowerSeries ι K) (hY : ∀ i, constantCoeff (Y i) = 0)
    (f : PS K 2 d) :
    subst Y (subst (GlobalTheory.LogJacobian.substSecondBlockZero (C := K) d) (subst (twoVars K d) f : MvPowerSeries (Fin d ⊕ Fin d) K) :
        MvPowerSeries (Fin d) K) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then Y q.2 else 0) f := by
  have hYs : HasSubst Y := hasSubst_of_constantCoeff_zero hY
  have hA := GlobalTheory.LogJacobian.hasSubst_substSecondBlockZero (C := K) d
  have hB : HasSubst (fun q : Fin 2 × Fin d => subst (GlobalTheory.LogJacobian.substSecondBlockZero (C := K) d) (twoVars K d q)) :=
    hasSubst_of_constantCoeff_zero fun q =>
      constantCoeff_subst_eq_zero hA (GlobalTheory.LogJacobian.constantCoeff_substSecondBlockZero d) (cc_twoVars q)
  rw [subst_comp_subst_apply hs_twoVars hA, subst_comp_subst_apply hB hYs]
  congr 1
  funext q
  simp only [twoVars]
  rw [subst_X hA]
  split_ifs with h
  · simp [GlobalTheory.LogJacobian.substSecondBlockZero, subst_X hYs]
  · simp only [GlobalTheory.LogJacobian.substSecondBlockZero, Sum.elim_inr]
    rw [← coe_substAlgHom hYs, map_zero]

theorem pderiv_inr_twoVars (k : Fin d) (f : PS K 2 d) :
    pderiv K (Sum.inr k) (subst (twoVars K d) f) = subst (twoVars K d) (pderiv K ((1 : Fin 2), k) f) := by
  classical
  rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst cc_twoVars, Finset.sum_eq_single ((1 : Fin 2), k)]
  · simp [twoVars, pderiv_X, Pi.single_apply]
  · intro q _ hq
    obtain ⟨a, i⟩ := q
    fin_cases a
    · simp [twoVars, pderiv_X, Pi.single_apply]
    · have : i ≠ k := fun h => hq (by simp [h])
      simp [twoVars, pderiv_X, Pi.single_apply, this]
  · simp

end Two

section Main

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℝ)} {d n : ℕ} {ι : Type}

theorem subst_jacEntry (F : FGLaw K d) (hF : ∀ a, MvIsInt v (subst (twoVars K d) (F.F a)))
    (Y : Fin d → MvPowerSeries ι K) (hY : ∀ i, constantCoeff (Y i) = 0) (k j : Fin d) :
    subst Y (GlobalTheory.LogJacobian.jacEntry (logFGLOf v F hF) k j) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then Y q.2 else 0) (pderiv K ((1 : Fin 2), k) (F.F j)) := by
  rw [← subst_secondBlockZero_twoPointVariables Y hY, ← pderiv_inr_twoVars]
  rfl

omit [CharZero K] in

theorem subst_ev_pt_zero [Finite ι] (T : Fin n × Fin d → MvPowerSeries ι K) (hT : ∀ q, constantCoeff (T q) = 0)
    (b : Fin n) (g : PS K 2 d) :
    subst T (ev (n := n) ![pt K d b, 0] g) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then T (b, q.2) else 0) g := by
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have h2 : HasSubst (fun p : Fin 2 × Fin d => (![pt K d b, 0] : Fin 2 → Pt K n d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j <;> simp [pt]
  unfold ev
  rw [subst_comp_subst_apply h2 hTs]
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  · simp [pt, subst_X hTs]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply, one_ne_zero, if_false]
    rw [← coe_substAlgHom hTs, map_zero]

omit [CharZero K] in

theorem constantCoeff_subst_self {σ : Type} [Finite σ] (T : σ → MvPowerSeries ι K)
    (hT : ∀ q, constantCoeff (T q) = 0) (f : MvPowerSeries σ K) :
    constantCoeff (subst T f : MvPowerSeries ι K) = constantCoeff f := by
  have hs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have h0 : constantCoeff (subst T (f - (constantCoeff f) • 1) : MvPowerSeries ι K) = 0 :=
    constantCoeff_subst_eq_zero hs hT (by simp)
  rw [← coe_substAlgHom hs, map_sub, map_smul, map_one, coe_substAlgHom hs] at h0
  simpa [sub_eq_zero] using h0

variable [Fintype ι]

def logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) : Fin d → MvPowerSeries ι K :=
  fun e => ∑ l, (if cp l = b then u l e else 0) • (X l : MvPowerSeries ι K)

omit [CharZero K] in
theorem cc_logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) (e : Fin d) :
    constantCoeff (logLin cp u b e) = 0 := by
  simp only [logLin, map_sum, constantCoeff_smul, constantCoeff_X, smul_zero, Finset.sum_const_zero]

omit [CharZero K] in
theorem pderiv_logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) (e : Fin d) (l : ι) :
    pderiv K l (logLin cp u b e) = if cp l = b then C (u l e) else 0 := by
  classical
  unfold logLin
  rw [map_sum, Finset.sum_eq_single l]
  · rw [Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]
    split_ifs <;> simp
  · intro l' _ hl
    rw [Derivation.map_smul, pderiv_X_of_ne hl, smul_zero]
  · simp

theorem pderiv_subst_expPt (F : FGLaw K d) (hF : ∀ a, MvIsInt v (subst (twoVars K d) (F.F a)))
    (cp : ι → Fin n) (u : ι → Fin d → K) (l : ι) (Φ : PS K n d) :
    subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) (DofN F.F (cp l) (u l) Φ) =
      pderiv K l (subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) Φ) := by
  classical
  set G := logFGLOf v F hF with hG
  set T : Fin n × Fin d → MvPowerSeries ι K := fun q => expPt G (logLin cp u q.1) q.2 with hTdef
  have hT : ∀ q, constantCoeff (T q) = 0 := fun q => cc_expPt G (cc_logLin cp u q.1) q.2
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have key : ∀ b j, pderiv K l (T (b, j)) = if cp l = b then
      ∑ i : Fin d, C (u l i) * subst T (ev (n := n) ![pt K d b, 0] (pderiv K ((1 : Fin 2), i) (F.F j))) else 0 := by
    intro b j
    have h1 : pderiv K l (T (b, j)) = ∑ i, subst (logLin cp u b) (pderiv K i (expOf G j)) *
        pderiv K l (logLin cp u b i) :=
      ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst (cc_logLin cp u b) (expOf G j) l
    have h2 : ∀ i, subst (logLin cp u b) (pderiv K i (expOf G j)) =
        subst T (ev (n := n) ![pt K d b, 0] (pderiv K ((1 : Fin 2), i) (F.F j))) := by
      intro i
      rw [GlobalTheory.LogJacobian.pderiv_expOf, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (isExp_expOf G).1)
        (hasSubst_of_constantCoeff_zero (cc_logLin cp u b)), subst_ev_pt_zero T hT]
      exact subst_jacEntry F hF (fun e => T (b, e)) (fun e => hT (b, e)) i j
    rw [h1]
    simp only [h2, pderiv_logLin]
    split_ifs
    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · simp
  rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst hT, Fintype.sum_prod_type, Finset.sum_eq_single (cp l)]
  · unfold DofN
    simp only [key, if_true]
    rw [← coe_substAlgHom hTs, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_sum, mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, coe_substAlgHom hTs, subst_C]
  · intro b _ hb
    simp [key, Ne.symm hb]
  · simp

end Main

theorem invDer : InvDerSt := by
  intro K _ _ v d F hF n ι _ cp u P Φ
  classical
  show _ = derivAt0 P (subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) Φ)
  have hk := pderiv_subst_expPt F hF cp u
  set T : Fin n × Fin d → MvPowerSeries ι K := fun q => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2
  have hT : ∀ q, constantCoeff (T q) = 0 := fun q => cc_expPt _ (cc_logLin cp u q.1) q.2
  have hit : ∀ (l : ι) (c : ℕ) (g : PS K n d),
      subst T ((DofN F.F (cp l) (u l))^[c] g) = (pderiv K l)^[c] (subst T g : MvPowerSeries ι K) := by
    intro l c
    induction c with
    | zero => intro g; rfl
    | succ c ih => intro g; rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hk]
  have hfold : ∀ (m : ι →₀ ℕ) (L : List ι),
      subst T (L.foldr (fun l g => (DofN F.F (cp l) (u l))^[m l] g) Φ) =
        L.foldr (fun l g => (pderiv K l)^[m l] g) (subst T Φ : MvPowerSeries ι K) := by
    intro m L
    induction L with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, hit, ih]
  unfold DpolyN derivAt0
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, constantCoeff_C, mul_assoc, ← constantCoeff_subst_self T hT]
  congr 1
  unfold DmonN
  rw [hfold, ← coeff_zero_eq_constantCoeff_apply,
    ReciprocityTheory.ChartRestriction.G.TB.MV.coeff_fold (fun l : ι => l) (fun _ _ h => h) m _ _ (Finset.nodup_toList _) 0,
    Finset.sum_map_toList, Finset.prod_map_toList]
  have h1 : (∑ l, m l • Finsupp.single l 1 : ι →₀ ℕ) = m := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact Finsupp.univ_sum_single m
  have h2 : (mfact m : K) = ∏ l, ((m l).factorial : K) := Finsupp.prod_fintype _ _ (by simp)
  simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.one_ascFactorial]
  rw [h1, h2, mul_comm]

end GlobalTheory.InvDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.TopForm GlobalTheory.ChartGlue GlobalTheory.CechPic
open scoped ContDiff

namespace GlobalTheory

open CxPts

section Pull

variable {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k}
  {p' : Y' ⟶ Sp k'} {σ : k →+* ℂ} {σ' : k' →+* ℂ} {D D' : ℕ} {f : Y' ⟶ Y}
  {m : CxPts p' σ' → CxPts p σ}

namespace CxPts

theorem continuous_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ f) : Continuous m :=
  continuous_induced_rng.2
    (((Points.continuous_comp f).comp continuous_subtype_val).congr fun z => (hm z).symm)

theorem mem_ptsIn_preimage (hm : ∀ z, (m z).1 = z.1 ≫ f) {U : Y.Opens} {z : CxPts p' σ'} :
    z ∈ ptsIn p' σ' (f ⁻¹ᵁ U) ↔ m z ∈ ptsIn p σ U := by
  change _ ↔ ⊤ ≤ (m z).1 ⁻¹ᵁ U
  rw [hm]
  rfl

theorem ev_of_comp (hm : ∀ z, (m z).1 = z.1 ≫ f) (U : Y.Opens) (g : Γ(Y, U)) (z : CxPts p' σ') :
    ev p σ U g (m z) = ev p' σ' (f ⁻¹ᵁ U) (f.app U g) z := by
  rw [ev, ev, hm]
  exact valR_comp _ _ _ _

end CxPts

theorem AlgChart.holo_map (hm : ∀ z, (m z).1 = z.1 ≫ f) (c' : AlgChart p' σ' D')
    (c : AlgChart p σ D) : DifferentiableOn ℂ (c.e ∘ m ∘ c'.e.symm)
      (c'.e.target ∩ c'.e.symm ⁻¹' (m ⁻¹' c.e.source)) :=
  differentiableOn_euclidean.2 fun a => ((c'.holo _ (f.app _ (c.x a))).mono fun _ hv =>
    ⟨hv.1, (mem_ptsIn_preimage hm).2 (c.source_subset hv.2)⟩).congr fun _ hv =>
      (c.apply_eq _ hv.2 a).trans (ev_of_comp hm _ _ _)

namespace AnRead

variable {R : AnRead p σ D} {S : Set (CxPts p σ)}

theorem exists_eventuallyEq_comp (hm : ∀ z, (m z).1 = z.1 ≫ f) (c : AlgChart p' σ' D') {v : V D'}
    (hv : v ∈ c.e.target) {E : Type*} (g : CxPts p σ → E) :
    ∃ i, m (c.e.symm v) ∈ (R.chart i).e.source ∧
      (g ∘ m) ∘ c.e.symm =ᶠ[𝓝 v] (g ∘ (R.chart i).e.symm) ∘ (R.chart i).e ∘ m ∘ c.e.symm := by
  obtain ⟨i, hi⟩ := R.cover (m (c.e.symm v))
  exact ⟨i, hi, eventually_of_mem ((isOpen_over c.e ((R.chart i).e.open_source.preimage
    (continuous_of_comp hm))).mem_nhds ⟨hv, hi⟩)
    fun w hw => (congrArg g ((R.chart i).e.left_inv hw.2)).symm⟩

theorem HoloOn.comp_map {g : CxPts p σ → ℂ} (h : R.HoloOn S g) (hS : IsOpen S)
    (hm : ∀ z, (m z).1 = z.1 ≫ f) (R' : AnRead p' σ' D') : R'.HoloOn (m ⁻¹' S) (g ∘ m) :=
  fun j v hv => by
  obtain ⟨i, hi, e⟩ := exists_eventuallyEq_comp (R := R) hm (R'.chart j) hv.1 g
  have ho := isOpen_over (R'.chart j).e ((R.chart i).e.open_source.preimage (continuous_of_comp hm))
  exact ((((h i).differentiableAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hv.2))).comp v
    (((R'.chart j).holo_map hm (R.chart i)).differentiableAt
      (ho.mem_nhds ⟨hv.1, hi⟩))).congr_of_eventuallyEq e).differentiableWithinAt

theorem SmoothOn.comp_map {g : CxPts p σ → ℝ} (h : R.SmoothOn S g) (hS : IsOpen S)
    (hm : ∀ z, (m z).1 = z.1 ≫ f) (R' : AnRead p' σ' D') : R'.SmoothOn (m ⁻¹' S) (g ∘ m) :=
  fun j v hv => by
  obtain ⟨i, hi, e⟩ := exists_eventuallyEq_comp (R := R) hm (R'.chart j) hv.1 g
  have ho := isOpen_over (R'.chart j).e ((R.chart i).e.open_source.preimage (continuous_of_comp hm))
  have ht : ContDiffOn ℝ ∞ ((R.chart i).e ∘ m ∘ (R'.chart j).e.symm) _ :=
    (contDiffOn_piLp 2).2 fun a => contDiffOn_real ho
      (differentiableOn_euclidean.1 ((R'.chart j).holo_map hm (R.chart i)) a)
  exact ((((h i).contDiffAt ((isOpen_over _ hS).mem_nhds (mem_over _ hi hv.2))).comp v
    (ht.contDiffAt (ho.mem_nhds ⟨hv.1, hi⟩))).congr_of_eventuallyEq e).contDiffWithinAt

end AnRead

namespace Weight

variable {R : AnRead p σ D} {B : LB Y} {φ : Weight p σ B}

theorem IsSmooth.linComb (h : φ.IsSmooth R) {κ : Type} [Fintype κ] (f : κ → (Y' ⟶ Y)) (ε : κ → ℤ)
    (m : κ → CxPts p' σ' → CxPts p σ) (hm : ∀ a z, (m a z).1 = z.1 ≫ f a) (R' : AnRead p' σ' D') :
    (φ.linComb f ε m hm).IsSmooth R' := fun j c =>
  ContDiffOn.sum (f := fun a v => (ε a : ℝ) * φ.φ (j a) (m a ((R'.chart c).e.symm v))) fun a _ =>
    contDiffOn_const.mul ((((h (j a)).comp_map (isOpen_ptsIn _) (hm a) R').mono
      fun z hz => mem_of_mem_linComb (hm · z) hz a) c)

theorem IsSmooth.pull (h : φ.IsSmooth R) {q : Y' ⟶ Sp k} (f : Y' ⟶ Y) (hf : f ≫ p = q)
    (R' : AnRead q σ D') : (φ.pull f hf).IsSmooth R' :=
  h.linComb _ _ _ _ R'

end Weight

end Pull

section Conj

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ σ' : k →+* ℂ} {A B : LB Y}

theorem CxPts.ev_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {U : Y.Opens} (hy : y ∈ ptsIn p σ U) (g : Γ(Y, U)) :
    ev p σ' U g y' = starRingEnd ℂ (ev p σ U g y) := by
  rw [ev, h]
  exact valR_conjHomeomorph y.1 U hy g

theorem sum_normSq_vecMul_unitary {α : Type*} [Fintype α] [DecidableEq α] {U : Matrix α α ℂ}
    (hU : U ∈ Matrix.unitaryGroup α ℂ) (w : α → ℂ) :
    ∑ a, ‖Matrix.vecMul w U a‖ ^ 2 = ∑ a, ‖w a‖ ^ 2 := by
  have key (x : α → ℂ) : ((∑ a, ‖x a‖ ^ 2 : ℝ) : ℂ) = x ⬝ᵥ star x := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.mul_conj', Complex.ofReal_sum,
      Complex.ofReal_pow]
  apply Complex.ofReal_injective
  rw [key, key, Matrix.star_vecMul, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.1 hU, Matrix.vecMul_one]

namespace Weight

theorem isConj_fsBasis_of_unitary {α : Type*} [Fintype α] [DecidableEq α] (hB : B.IsLB)
    (b : α → B.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) {M M' U : Matrix α α ℂ}
    (hM : M.det ≠ 0) (hM' : M'.det ≠ 0) (hU : U ∈ Matrix.unitaryGroup α ℂ)
    (e : M' = M.map (starRingEnd ℂ) * U) :
    (fsBasis p σ hB b hb M hM).IsConj (fsBasis p σ' hB b hb M' hM') := fun i y y' h hy => by
  rw [fsBasis_φ, fsBasis_φ]
  congr 1
  have hv (j : α) : valR y'.1 (B.U i) ((b j).f i) = starRingEnd ℂ (valR y.1 (B.U i) ((b j).f i)) :=
    CxPts.ev_conj h hy _
  have := sum_normSq_vecMul_unitary hU fun a =>
    starRingEnd ℂ (∑ j, M j a * valR y.1 (B.U i) ((b j).f i))
  simp only [RCLike.norm_conj] at this
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) this
  congr 2
  simp only [e, hv, Matrix.mul_apply, Matrix.map_apply, Matrix.vecMul, dotProduct, map_sum, map_mul,
    Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

theorem isConj_fsBasis {α : Type*} [Fintype α] [DecidableEq α] (hB : B.IsLB)
    (b : α → B.Sec) (hb : ⨆ j, nonzeroLocus (b j) = ⊤) {M M' : Matrix α α ℂ}
    (hM : M.det ≠ 0) (hM' : M'.det ≠ 0) (e : M' = M.map (starRingEnd ℂ)) :
    (fsBasis p σ hB b hb M hM).IsConj (fsBasis p σ' hB b hb M' hM') :=
  isConj_fsBasis_of_unitary hB b hb hM hM' (one_mem _) (e.trans (Matrix.mul_one _).symm)

variable {φ : Weight p σ B} {φ' : Weight p σ' B}

theorem IsConj.tens {ψ : Weight p σ A} {ψ' : Weight p σ' A} (h' : ψ.IsConj ψ') (h : φ.IsConj φ') :
    (ψ.tens φ).IsConj (ψ'.tens φ') := fun c y y' e hy =>
  congrArg₂ (· + ·) (h' c.1 y y' e (mem_ptsIn_inf.1 hy).1) (h c.2 y y' e (mem_ptsIn_inf.1 hy).2)

theorem IsConj.dual (h : φ.IsConj φ') : φ.dual.IsConj φ'.dual := fun i y y' e hy =>
  congrArg Neg.neg (h i y y' e hy)

theorem IsConj.linComb (h : φ.IsConj φ') {k' : Type} [CommRing k'] {Y' : Scheme.{0}}
    {q : Y' ⟶ Sp k'} {τ τ' : k' →+* ℂ} {κ : Type} [Fintype κ] (f : κ → (Y' ⟶ Y)) (ε : κ → ℤ)
    (m : κ → CxPts q τ → CxPts p σ) (hm : ∀ a z, (m a z).1 = z.1 ≫ f a)
    (m' : κ → CxPts q τ' → CxPts p σ') (hm' : ∀ a z, (m' a z).1 = z.1 ≫ f a) :
    (φ.linComb f ε m hm).IsConj (φ'.linComb f ε m' hm') := fun j z z' e hz =>
  Finset.sum_congr rfl fun a _ => congrArg (_ * ·) (h (j a) _ _
    (by rw [hm, hm', e, Category.assoc]) (mem_of_mem_linComb (hm · z) hz a))

theorem IsConj.zpow (h : φ.IsConj φ') (n : ℤ) : (φ.zpow n).IsConj (φ'.zpow n) :=
  h.linComb _ _ _ _ _ _

theorem IsConj.pull (h : φ.IsConj φ') {Y' : Scheme.{0}} {q : Y' ⟶ Sp k} (f : Y' ⟶ Y)
    (hf : f ≫ p = q) : (φ.pull f hf).IsConj (φ'.pull f hf) :=
  h.linComb _ _ _ _ _ _

end Weight

end Conj

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMatrixIdentityGermPullbackChartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMatrixIdentity_germ_pullback_chart : ∀ {Rg : Type} [CommRing Rg] {A B : Over (Sp Rg)} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left} {k : ℕ} {mA mB : ℕ} {bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))} {bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))} {eA : LB.Gen (L.pull (eSec A))} {eB : LB.Gen (M.pull (eSec B))} {R : Type} [CommRing R] {t : Sp R ⟶ Sp Rg} {A' B' : Over (Sp R)} [GrpObj A'] [GrpObj B'] {φA' : A'.left ⟶ A.left} {φB' : B'.left ⟶ B.left} {Φ' : A' ⟶ B'} {c : Fin mA → Fin mB → Γ(Sp R, ⊤)}, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → ∃ (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left), ψA ≫ (snd (topS Rg) A).left = φA' ∧ ψB ≫ (snd (topS Rg) B).left = φB' ∧ ∀ (Z : Scheme.{0}) (e : Z ⟶ A'.left) (z : Z) (pM : Fin 1 → M.ι) (q : Fin 1 → L.ι), (e ≫ Φ'.left ≫ ψB) z ∈ (LPow B M (k : ℤ) (topS Rg)).U pM → (e ≫ ψA) z ∈ (LPow A L (k : ℤ) (topS Rg)).U q → ∃ u : (Z.presheaf.stalk z)ˣ, ∀ j, gs (e ≫ Φ'.left ≫ ψB) z _ ((bB j).f pM) = u * ∑ i, gs (e ≫ A'.hom) z ⊤ (c i j) * gs (e ≫ ψA) z _ ((bA i).f q) := by
  first | (exact @GlobalTheory.HomFixMat.isMat_germ) | (exact GlobalTheory.HomFixMat.isMat_germ) | (intros; apply GlobalTheory.HomFixMat.isMat_germ  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfLiftCompleteDvrCharZeroStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_lift_completeDvr_charZero : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s → Flat s → (∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : R →+* V) (x : Sp K ⟶ X), x ≫ s = spMap ((algebraMap V K).comp β) → ∃ (W L : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (_ : Field L) (_ : Algebra V W) (_ : Algebra W L) (_ : Algebra K L) (_ : IsFractionRing W L), (algebraMap W L).comp (algebraMap V W) = (algebraMap K L).comp (algebraMap V K) ∧ IsLocalHom (algebraMap V W) ∧ ∃ f : Sp W ⟶ X, spMap (algebraMap K L) ≫ x = spMap (algebraMap W L) ≫ f) → IsProper s := by
  first | exact @GlobalTheory.ValuativeFlat.isProper_of_lift_dominating | exact GlobalTheory.ValuativeFlat.isProper_of_lift_dominating | (intros; apply GlobalTheory.ValuativeFlat.isProper_of_lift_dominating <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPToLiftReal
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.ThetaPRead

theorem isThetaP_restrict {G' H' S' Si Tau Y ι : Type} [MeasurableSpace H'] [AddCommGroup Si] [Module ℂ Si]
    [AddCommGroup Tau] [Module ℂ Tau] [AddCommGroup Y] [Module ℂ Y]
    {M : ι → Type} [∀ ρ, AddCommGroup (M ρ)] [∀ ρ, Module ℂ (M ρ)] (low : ∀ ρ, Submodule ℂ (M ρ))
    {ν : Measure H'} {𝓕 : Set H'} {th : G' → H' → S' → ℂ} {pt : Si → S'}
    {io : (⨂[ℂ] ρ, low ρ) →ₗ[ℂ] Tau →ₗ[ℂ] Si} (L : Y →ₗ[ℂ] (H' → Tau)) (hL : Function.Injective L)
    (S : Submodule ℂ (H' → Tau)) (U : Y →ₗ[ℂ] MultilinearMap ℂ M (G' → ℂ))
    (h : ∃ thP, Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range L) thP ∧
      ∀ x (v : ∀ ρ, low ρ), U x (fun ρ => v ρ) = thP (L.rangeRestrict x) (PiTensorProduct.tprod ℂ v)) :
    Lift.IsThetaP ν 𝓕 th pt io (LinearMap.range L ⊓ S)
      (LinearMap.lcomp ℂ (G' → ℂ) (PiTensorProduct.map fun ρ => (low ρ).subtype) ∘ₗ
        (PiTensorProduct.lift : MultilinearMap ℂ M (G' → ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ U ∘ₗ
        (LinearEquiv.ofInjective L hL).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left) := by
  obtain ⟨thP, hP, hv⟩ := h
  have key : ∀ f : ↥(LinearMap.range L ⊓ S),
      (LinearMap.lcomp ℂ (G' → ℂ) (PiTensorProduct.map fun ρ => (low ρ).subtype) ∘ₗ
        (PiTensorProduct.lift : MultilinearMap ℂ M (G' → ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ U ∘ₗ
        (LinearEquiv.ofInjective L hL).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left) f =
        thP (Submodule.inclusion inf_le_left f) := by
    intro f
    set x := (LinearEquiv.ofInjective L hL).symm (Submodule.inclusion inf_le_left f) with hx
    have h1 : L.rangeRestrict x = Submodule.inclusion inf_le_left f := by
      have := LinearEquiv.apply_symm_apply (LinearEquiv.ofInjective L hL) (Submodule.inclusion inf_le_left f)
      rw [← hx] at this
      rw [← this]
      rfl
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lcomp_apply, LinearEquiv.coe_coe, PiTensorProduct.map_tprod, Submodule.coe_subtype,
      PiTensorProduct.lift.tprod]
    rw [← hx, hv x v, h1]
  refine ⟨fun f e g => ?_, fun f e g => ?_⟩
  · exact hP.integ (Submodule.inclusion inf_le_left f) e g
  · rw [key f]
    exact hP.eq _ e g

theorem isThetaP_toLiftReal : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), R.thP_thF → ∀ μ i, Lift.IsThetaP ((RecTie.toLiftReal R F tupT hm hTop hinj).measV μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).fdV μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).thW μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).ptW μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).ioK i) ((RecTie.toLiftReal R F tupT hm hTop hinj).Amt μ i) ((RecTie.toLiftReal R F tupT hm hTop hinj).thC μ i) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj h μ i
  exact isThetaP_restrict _ _ _ _ _ (h i (tupT μ))

end GlobalTheory.ThetaPRead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchesParahoricLevelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isometry_matches_parahoric_levels : ∀ {D : D7} (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (r t : ℕ) (hr : r ≤ V.rank) (hr' : r ≤ V'.rank) (Pg : Finset (Pl D.host.E)) (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V'), IsFinIso V V' β β' Pg j Φ → ∀ κ : GfC V, (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) ↔ finE V' (Φ κ : GA D V') ∈ parLev D.sp.cm V'.gram β' (princDat V'.rank r t hr' Pg χ')) ∧ (finE V (κ : GA D V) ∈ parLev D.sp.cm V.gram β (princDat V.rank r t hr Pg χ) → (rTup β' (princDat V'.rank r t hr' Pg χ') (finE V' (Φ κ : GA D V')) : G0 Pg r) = (rTup β (princDat V.rank r t hr Pg χ) (finE V (κ : GA D V)) : G0 Pg r)) := by
  first | exact @GlobalTheory.LevTrans.levtrans | exact GlobalTheory.LevTrans.levtrans | (intros; apply GlobalTheory.LevTrans.levtrans <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSpreadStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lbIso_spread_alt : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Type) [CommRing S] (R₀ : Subring S) (s₀ : Sp R₀ ⟶ Sp B) (d₀ : SiegPre g n ζ s₀) (Y : Scheme.{0}) (sY : Y ⟶ Sp B) (u : SiegPre g n ζ sY) (h₀ : Sp R₀ ⟶ Y) (ψ : d₀.A.left ⟶ u.A.left) (sE : Sp S ⟶ Sp B) (e : SiegPre g n ζ sE) (j : e.A.left ⟶ d₀.A.left), IsPullback ψ d₀.A.hom u.A.hom h₀ → ∀ (j₂ : (G2 e.A).left ⟶ (G2 d₀.A).left) (φ₂ : (G2 e.A).left ⟶ (G2 u.A).left), IsPullback j e.A.hom d₀.A.hom (spMap R₀.subtype) → IsSquare j j₂ → LBIso e.P (d₀.P.pull j₂) → IsSquare (j ≫ ψ) φ₂ → LBIso e.P (u.P.pull φ₂) → ∃ F : Finset S, ∀ (R₁ : Subring S) (hle : R₀ ≤ R₁), (F : Set S) ⊆ R₁ → ∀ (s₁ : Sp R₁ ⟶ Sp B) (d₁ : SiegPre g n ζ s₁) (φ₁ : d₁.A.left ⟶ d₀.A.left) (φ₁₂ : (G2 d₁.A).left ⟶ (G2 d₀.A).left) (χ₂ : (G2 d₁.A).left ⟶ (G2 u.A).left), IsPullback φ₁ d₁.A.hom d₀.A.hom (spMap (Subring.inclusion hle)) → IsSquare φ₁ φ₁₂ → LBIso d₁.P (d₀.P.pull φ₁₂) → IsSquare (φ₁ ≫ ψ) χ₂ → LBIso d₁.P (u.P.pull χ₂) := by
  first | exact @GlobalTheory.SiegBundleSpread.lbIso_spread | exact GlobalTheory.SiegBundleSpread.lbIso_spread | (intros; apply GlobalTheory.SiegBundleSpread.lbIso_spread <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureSpecialUnitarySupportedAtPlacesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_specialUnitarySupportedAtPlaces : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ SUAdelic σ J, g ∈ closure {x : HA (AF F) σ J | ∃ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η ∧ x ∈ SUSupp σ J η} := by
  first | exact @GlobalTheory.SUTrunc.mem_closure_supp | exact GlobalTheory.SUTrunc.mem_closure_supp | (intros; apply GlobalTheory.SUTrunc.mem_closure_supp <;> assumption)
end

