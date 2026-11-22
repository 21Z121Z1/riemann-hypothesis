import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactEntriesBd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnePowNotMemHeightOneAsIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieNumberFieldPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder

namespace GlobalTheory.FunObj

open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def OpenBdd {a : Type} [Fintype a] [DecidableEq a] (H : Subgroup (GL a k)) : Prop :=
  IsOpen (H : Set (GL a k)) ∧ ∃ C : Set (GL a k), IsCompact C ∧ (H : Set (GL a k)) ⊆ C

theorem openBdd_of_le {a : Type} [Fintype a] [DecidableEq a] {H : Subgroup (GL a k)} (h1 : KOne k a ≤ H) (h2 : H ≤ KO k a) :
    OpenBdd H :=
  ⟨Subgroup.isOpen_mono h1 isOpen_KOne, _, isCompact_KO, h2⟩

theorem OpenBdd.map {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] {H : Subgroup (GL a k)}
    (hH : OpenBdd H) (f : GL a k ≃* GL b k) (hf : Continuous f) (hf' : Continuous f.symm) : OpenBdd (H.map f.toMonoidHom) := by
  have e : ((H.map f.toMonoidHom : Subgroup (GL b k)) : Set (GL b k)) = f.symm ⁻¹' (H : Set (GL a k)) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_map, Set.mem_preimage, MulEquiv.coe_toMonoidHom]
    exact ⟨fun ⟨y, hy, e⟩ => by rw [← e, MulEquiv.symm_apply_apply]; exact hy,
      fun h => ⟨_, h, MulEquiv.apply_symm_apply _ _⟩⟩
  obtain ⟨ho, C, hC, hHC⟩ := hH
  refine ⟨e ▸ ho.preimage hf', f '' C, hC.image hf, ?_⟩
  rw [e]
  intro x hx
  exact ⟨_, hHC hx, MulEquiv.apply_symm_apply _ _⟩

theorem continuous_reGL {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) :
    Continuous (reGL (k := k) e) :=
  Continuous.units_map _ (continuous_id.matrix_reindex _ _)

theorem continuous_reGL_symm {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) :
    Continuous (reGL (k := k) e).symm := by
  have : (reGL (k := k) e).symm = reGL e.symm := by
    ext g i j
    rfl
  rw [this]
  exact continuous_reGL e.symm

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem openBdd_givenLevel (t : T) (w : Pl D.host.E) (i : ℕ) : OpenBdd (givenLevel G t w (i, D.R.m)) := by
  obtain ⟨m', hm⟩ : ∃ m', D.R.m = m' + 1 := ⟨D.R.m - 1, by have := D.R.two_le_m; omega⟩
  have key : ∀ X : ℕ × ℕ, X = (i, m' + 1) → OpenBdd (givenLevel G t w X) := by
    rintro _ rfl
    rcases i with _ | i
    · refine OpenBdd.map ?_ _ (continuous_reGL _) (continuous_reGL_symm _)
      unfold stepGroup
      split_ifs
      · exact openBdd_of_le (TypeDatum.KOne_le _) (TypeDatum.le_KO _)
      · exact openBdd_of_le (TypeDatum.KOne_le _) (TypeDatum.le_KO _)
      · exact openBdd_of_le KOne_le_KO le_rfl
    · exact openBdd_of_le KOne_le_KO le_rfl
  exact key _ (by rw [hm])

theorem openBdd_conjLevel (t : T) (w : Pl D.host.E) (g : (locGrid G t w).VertexGroup) {j : ℕ} (h0 : 0 < j)
    (hj : j < (locGrid G t w).m) : OpenBdd (conjLevel (G := locGrid G t w) one_le_sLen (givenLevel G t w) g hj) := by
  have hK : OpenBdd (givenLevel G t w ((locGrid G t w).m, j)) := by
    obtain ⟨m', hm⟩ : ∃ m', (locGrid G t w).m = m' + 1 := ⟨(locGrid G t w).m - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have key : ∀ X : ℕ × ℕ, X = (m' + 1, j' + 1) → OpenBdd (givenLevel G t w X) := by
      rintro _ rfl
      exact openBdd_of_le KOne_le_KO le_rfl
    exact key _ (by rw [hm])
  refine OpenBdd.map (OpenBdd.map hK _ ?_ ?_) _ ?_ ?_
  · exact (continuous_const.mul continuous_id).mul continuous_const
  · exact (continuous_const.mul continuous_id).mul continuous_const
  · exact Continuous.units_map _ (continuous_id.matrix_reindex _ _)
  · exact Continuous.units_map _ (continuous_id.matrix_reindex _ _)

theorem isCO_prodLev (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (P : Finset (Pl D.host.E)) {n' : P → ℕ}
    (h : ∀ w, n' w = V.rank) (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (hK : ∀ w, OpenBdd (K w)) :
    IsCO V (prodLev β P h K) :=
  have ho := ProdOpen.isOpen_comap_prodLev V β P h K fun w => (hK w).1
  ⟨ho, GlobalTheory.ProdLevCompactC.isCompact_levA V β P h K (fun w => (hK w).2) ho⟩

variable (W : G.Weil) {U : Set T} (S : GridChoice W U) (t : T) (Φ : G.Datum)

theorem openBdd_pr (β : CosFam G t) (w : locPl G t) (j : ℕ) (h0 : 0 < j) (hj : j < D.R.m) :
    OpenBdd ((S.term t Φ β w).pr j h0 hj) := by
  obtain ⟨ho, hb⟩ := openBdd_conjLevel t w.1 ((repsAt G t w).elt (β w)) h0 hj
  exact SymImageC.symPr_open_bounded _ ho hb

namespace GridChoice

theorem isCO_levTop (β : CosFam G t) {j : ℕ} (hj : j < D.R.m) : IsCO (G.V (.top j)) (S.levTop t Φ β j hj) := by
  rcases j with _ | j
  · exact congLev_open_compact _ (isV_Xp G).sd.1 (G.pl.modul_ne_bot sc)
  · exact isCO_prodLev _ _ _ _ _ fun w => openBdd_pr W S t Φ β w (j + 1) j.succ_pos hj

theorem isCO_levRow {i : ℕ} (hi : i ≤ D.R.m) : IsCO (G.V (.grid i D.R.m)) (S.levRow t i hi) :=
  isCO_prodLev _ _ _ _ _ fun w => openBdd_givenLevel t w.1 i

end GridChoice

variable (G) in

theorem posDef_top {j : ℕ} (hj : j ≤ D.R.m) (φ : D.host.E →+* ℂ) : ((G.V (.top j)).gram.map φ).PosDef := by
  have h := G.isV (X := .top j) hj (fun _ e => by cases e)
  have := h.sigOK φ
  rw [h.sig φ] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem posDef_grid {μ₀ : T} (hL : L.Is μ₀) {i : ℕ} (hi : i ≤ D.R.m) (φ : D.host.E →+* ℂ) :
    ((G.V (.grid i D.R.m)).gram.map φ).PosDef := by
  have h := node_isV G hL (X := .grid i D.R.m) ⟨hi, le_rfl⟩
  have := h.sigOK φ
  rw [h.sig φ] at this
  simp only [Node.neg, Nat.sub_self, Nat.zero_div, Nat.sub_zero] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem readOK {n : ℕ} (σ : D.what₂.Tau → DomWeight n) : ReadOK σ := by
  obtain ⟨φ, h, -⟩ := funForm (K := ℂ) σ
  exact readOK_of_equiv σ φ fun F => (h F _).2 rfl

namespace GridChoice

theorem sumOK_classes {μ₀ : T} (hL : L.Is μ₀) :
    (∀ β, Finite (S.Classes t Φ β)) ∧ (∀ β (c : S.Classes t Φ β), S.invGam c ≠ 0) ∧
    (∀ i, i < D.R.m → WtOK G (.top t i) ∧ WtOK G (.chi i D.R.m)) ∧
    (∀ τ, Formalism.L2.Col.Br.Interlace G.sp.topDec.rank.symm (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ) ∧
      Formalism.L2.Col.Br.SameShift (wt G (.top D.R.m) τ) (listedWt G (.grid D.R.m D.R.m) τ)) ∧
    (ReadOK (listedWt G (.grid 0 D.R.m)) ∧ ReadOK (listedWt G (.grid D.R.m D.R.m))) := by
  have hT : ∀ β (j : Fin D.R.m), Finite (FinCl _ (S.levTop t Φ β j j.2)) ∧ ∀ x, gamOrd _ (S.levTop t Φ β j j.2) x ≠ 0 :=
    fun β j => ClassFin.finite_finCl_and_gamOrd _ _ (posDef_top G j.2.le) (isCO_levTop W S t Φ β j.2)
  have hR : ∀ i : Fin (D.R.m + 1), Finite (FinCl _ (S.levRow t i (Nat.le_of_lt_succ i.2))) ∧
      ∀ x, gamOrd _ (S.levRow t i (Nat.le_of_lt_succ i.2)) x ≠ 0 :=
    fun i => ClassFin.finite_finCl_and_gamOrd _ _ (posDef_grid hL (Nat.le_of_lt_succ i.2)) (isCO_levRow W S t (Nat.le_of_lt_succ i.2))
  refine ⟨fun β => ?_, fun β c => ?_, fun i hi => ⟨wtOK_of_defPair G (.top t i) hi, wtOK_of_defPair G (.chi i D.R.m) ⟨hi, rfl⟩⟩,
    GlobalTheory.WtInterlaceC.weights_top_grid G, readOK _, readOK _⟩
  · have := fun j => (hT β j).1
    have := fun i => (hR i).1
    exact inferInstance
  · unfold GridChoice.invGam
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => inv_ne_zero (Nat.cast_ne_zero.2 ((hT β j).2 _)))
      (Finset.prod_ne_zero_iff.2 fun i _ => inv_ne_zero (Nat.cast_ne_zero.2 ((hR i).2 _)))

end GridChoice

end GlobalTheory.FunObj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordsAndSymplecticIntegralOnPlaceLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.AdelicU GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.LatticeAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def Gd (v : HeightOneSpectrum (𝓞 F)) (x : AF F) : Prop :=
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) x ∧ evFin F v x ∈ v.adicCompletionIntegers F

theorem gd_zero (v : HeightOneSpectrum (𝓞 F)) : Gd v (0 : AF F) :=
  ⟨fun u _ => smul_zero u, by rw [map_zero]; exact zero_mem _⟩

theorem gd_add {v : HeightOneSpectrum (𝓞 F)} {x y : AF F} (hx : Gd v x) (hy : Gd v y) : Gd v (x + y) :=
  ⟨fun u hu => by rw [smul_add, hx.1 u hu, hy.1 u hu, add_zero], by rw [map_add]; exact add_mem hx.2 hy.2⟩

theorem gd_neg {v : HeightOneSpectrum (𝓞 F)} {x : AF F} (hx : Gd v x) : Gd v (-x) :=
  ⟨fun u hu => by rw [smul_neg, hx.1 u hu, neg_zero], by rw [map_neg]; exact neg_mem hx.2⟩

theorem gd_mul {v : HeightOneSpectrum (𝓞 F)} {x y : AF F} (hx : Gd v x)
    (hy : evFin F v y ∈ v.adicCompletionIntegers F) : Gd v (x * y) :=
  ⟨fun u hu => by rw [← smul_mul_assoc, hx.1 u hu, zero_mul], by rw [map_mul]; exact mul_mem hx.2 hy⟩

theorem ev_alg (v : HeightOneSpectrum (𝓞 F)) (y : F) :
    evFin F v (algebraMap F (AF F) y) = algebraMap F (Fv F v) y := AlgHom.commutes _ y

def bil (σ : E →ₐ[F] E) {n d : ℕ} (ξ : E) (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin d) (Fin d) E) :
    LinearMap.BilinForm (AF F) (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) :=
  LinearMap.mk₂ (AF F) (symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY))
    (fun x x' y => by
      simp only [symp, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add])
    (fun a x y => by
      simp only [symp, hTens, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm, map_smul])
    (fun x y y' => by
      simp only [symp, hTens, Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add, map_add])
    (fun a x y => by
      simp only [symp, hTens, Matrix.smul_apply, smul_mul_assoc, ← Finset.smul_sum, mul_smul_comm, map_smul])

theorem symp_incM (σ : E →ₐ[F] E) {n d : ℕ} (ξ : E) (JX : Matrix (Fin n) (Fin n) E)
    (JY : Matrix (Fin d) (Fin d) E) (x y : Matrix (Fin n) (Fin d) E) :
    symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F y) = algebraMap F (AF F) (symp σ ξ JX JY x y) := by
  have ht : ∀ e : E, Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) (inclR (F := F) (AF F) e) =
      algebraMap F (AF F) (Algebra.trace F E e) := fun e => by
    show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
    rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]
  have hc : ∀ e : E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [symp, symp, ← ht]
  simp only [hTens, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hc, map_mul, map_sum]

end GlobalTheory.LatticeAtPlace

namespace GlobalTheory.LatticeAtPlace

theorem coords_symp_integral : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin d) (Fin d) E) (ξ : E) (v : HeightOneSpectrum (𝓞 F))
    (co : (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F))
    (T₀ : Set (Matrix (Fin n) (Fin d) E)) (yf zf : Matrix (Fin n) (Fin d) E → Fin n × Fin d → F),
    (∀ x, co (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (yf x k), fun k => algebraMap F (AF F) (zf x k))) →
    (∀ t ∈ T₀, ∀ k, algebraMap F (Fv F v) (yf t k) ∈ v.adicCompletionIntegers F ∧
      algebraMap F (Fv F v) (zf t k) ∈ v.adicCompletionIntegers F) →
    (∀ t ∈ T₀, ∀ t' ∈ T₀, algebraMap F (Fv F v) (GlobalTheory.WeilM.symp σ ξ JX JY t t') ∈ v.adicCompletionIntegers F) →
    ∀ γ ∈ AddSubgroup.closure {z | ∃ a : AF F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
        ∃ t ∈ T₀, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t},
      (∀ k, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co γ).1 k) ∧ evFin F v ((co γ).1 k) ∈ v.adicCompletionIntegers F ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) ((co γ).2 k) ∧ evFin F v ((co γ).2 k) ∈ v.adicCompletionIntegers F) ∧
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ)
                   (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY) γ γ) ∧
        evFin F v (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) ξ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JX)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F JY) γ γ) ∈ v.adicCompletionIntegers F) := by
  intro F E _ _ _ _ _ σ n d JX JY ξ v co T₀ yf zf hco hyz hs γ hγ
  set S : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)) := {z | ∃ a : AF F,
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) a ∧ evFin F v a ∈ v.adicCompletionIntegers F ∧
      ∃ t ∈ T₀, z = a • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t} with hS
  have hcoord : ∀ z ∈ AddSubgroup.closure S, ∀ k, Gd v ((co z).1 k) ∧ Gd v ((co z).2 k) := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha1, ha2, t, ht, rfl⟩ := hz
      intro k
      rw [map_smul, hco]
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      exact ⟨gd_mul ⟨ha1, ha2⟩ (by rw [ev_alg]; exact (hyz t ht k).1),
        gd_mul ⟨ha1, ha2⟩ (by rw [ev_alg]; exact (hyz t ht k).2)⟩
    | zero =>
      intro k
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
      exact ⟨gd_zero v, gd_zero v⟩
    | add x y _ _ hx hy =>
      intro k
      simp only [map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply]
      exact ⟨gd_add (hx k).1 (hy k).1, gd_add (hx k).2 (hy k).2⟩
    | neg x _ hx =>
      intro k
      simp only [map_neg, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]
      exact ⟨gd_neg (hx k).1, gd_neg (hx k).2⟩
  have hgen : ∀ x ∈ S, ∀ y ∈ S, Gd v (bil σ ξ JX JY x y) := by
    rintro _ ⟨a, ha1, ha2, t, ht, rfl⟩ _ ⟨b, -, hb2, t', ht', rfl⟩
    rw [LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    have e : bil σ ξ JX JY (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F t') =
        algebraMap F (AF F) (symp σ ξ JX JY t t') := symp_incM σ ξ JX JY t t'
    rw [e]
    refine gd_mul ⟨ha1, ha2⟩ ?_
    rw [map_mul, ev_alg]
    exact mul_mem hb2 (hs t ht t' ht')
  have hpair : ∀ x ∈ AddSubgroup.closure S, ∀ y ∈ AddSubgroup.closure S, Gd v (bil σ ξ JX JY x y) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem y hy => exact hgen x hx y hy
      | zero => rw [map_zero]; exact gd_zero v
      | add y y' _ _ h h' => rw [map_add]; exact gd_add h h'
      | neg y _ h => rw [map_neg]; exact gd_neg h
    | zero => intro y _; rw [map_zero, LinearMap.zero_apply]; exact gd_zero v
    | add x x' _ _ h h' => intro y hy; rw [map_add, LinearMap.add_apply]; exact gd_add (h y hy) (h' y hy)
    | neg x _ h => intro y hy; rw [map_neg, LinearMap.neg_apply]; exact gd_neg (h y hy)
  have hp := hpair γ hγ γ hγ
  exact ⟨fun k => ⟨(hcoord γ hγ k).1.1, (hcoord γ hγ k).1.2, (hcoord γ hγ k).2.1, (hcoord γ hγ k).2.2⟩, hp.1, hp.2⟩

end GlobalTheory.LatticeAtPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverRectangularAdelicMatricesShrunkCompact
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

theorem cover_rect_adMat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ j m : ℕ, ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin m) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (m * μ i) ∧ ∀ x : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), ∃ x₀ : Matrix (Fin j) (Fin m) E, ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω) := by
  intro F E _ _ _ _ _ σ hσ j m
  classical
  obtain ⟨Ω, C, hΩ, h⟩ := GlobalTheory.GodementSectionReduction.cover_adele F E σ hσ
  choose Y hY h using h
  refine ⟨Ω, (C ^ m) ^ j, hΩ, fun μ =>
    ⟨Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin m => Y (μ i), ?_, fun x => ?_⟩⟩
  · have h1 : (Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin m => Y (μ i)).card = ∏ i, (Y (μ i)).card ^ m := by
      simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine (Nat.cast_le.2 h1.le).trans ?_
    push_cast
    refine (Finset.prod_le_prod (fun _ _ => by positivity) fun i _ =>
      pow_le_pow_left₀ (Nat.cast_nonneg _) (hY (μ i)) m).trans (le_of_eq ?_)
    simp only [bse, mul_pow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul _ (μ _), mul_comm m]
  · choose x₀ y hy ω hω e using fun i k => h (μ i) (x i k)
    refine ⟨Matrix.of x₀, Matrix.of y, Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 (hy i), Matrix.of ω,
      fun i k => hω i k, ?_⟩
    ext i k
    rw [Matrix.add_apply, Matrix.add_apply, ← add_assoc]
    simp only [tor, GlobalTheory.Eis.Conv.dg, Matrix.diagonal_mul, adMat, Matrix.map_apply, Matrix.of_apply, zpow_natCast,
      Units.val_pow_eq_pow_val]
    exact e i k

end GlobalTheory.SphEis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverSkewHermitianAdelicMatricesShrunkCompact
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SkewAdCover

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_sigR (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, sig_sig σ h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sigR_inclR (σ : E →ₐ[F] E) (e : E) : sigR (AF F) σ (inclR (F := F) (AF F) e) = inclR (AF F) (σ e) := by
  simp [sigR, inclR]

theorem sigR_alg (σ : E →ₐ[F] E) (c : F) :
    sigR (AF F) σ (algebraMap F (AF F ⊗[F] E) c) = algebraMap F (AF F ⊗[F] E) c :=
  (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ).commutes c

theorem inclR_alg (c : F) : inclR (F := F) (AF F) (algebraMap F E c) = algebraMap F (AF F ⊗[F] E) c :=
  (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).commutes c

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR (AF F) σ) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [sigR]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [this]
  exact IsModuleTopology.continuous_of_linearMap _

theorem cT_apply {A : Type} [CommRing A] (s : A →+* A) {m p : Type} (M : Matrix m p A) (i : p) (k : m) :
    cT s M i k = s (M k i) := rfl

theorem cover (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) (j : ℕ) : ∃ (Ω : Set (AF F ⊗[F] E)) (B : ℝ), IsCompact Ω ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ (j * μ i) ∧ (∀ y ∈ Y, cT (sigR (AF F) σ) y = -y) ∧ ∀ x : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) x = -x → ∃ x₀ : Matrix (Fin j) (Fin j) E, cT (σ : E →+* E) x₀ = -x₀ ∧ ∃ y ∈ Y, ∃ ω : Matrix (Fin j) (Fin j) (AF F ⊗[F] E), cT (sigR (AF F) σ) ω = -ω ∧ (∀ i k, ω i k ∈ Ω) ∧ x = adMat F x₀ + (y + (tor F E fun i => (μ i : ℤ)).1 * ω * cT (sigR (AF F) σ) (tor F E fun i => (μ i : ℤ)).1) := by
  classical
  haveI := hσ.1
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact F
  obtain ⟨Ω, C, hΩ, h⟩ := GlobalTheory.T.skewHermitian_adelic_cover_of_adele_cover F E σ hσ _ _ _ hΩ₀ hcov j
  set s := sigR (AF F) σ with hs_def
  set hh : AF F ⊗[F] E := algebraMap F (AF F ⊗[F] E) 2⁻¹ with hh_def
  have h2 : hh * 2 = 1 := by
    rw [hh_def, ← map_ofNat (algebraMap F (AF F ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
  have hsh : s hh = hh := sigR_alg σ _
  have hss : ∀ z, s (s z) = z := sigR_sigR σ hσ
  have hsi : ∀ e, s (inclR (F := F) (AF F) e) = inclR (AF F) (σ e) := sigR_inclR σ
  let sk : Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin j) (Fin j) (AF F ⊗[F] E) :=
    fun z => Matrix.of fun i k => hh * (z i k - s (z k i))
  have sk_skew : ∀ z, cT s (sk z) = -sk z := fun z => by
    ext i k
    simp only [cT_apply, sk, Matrix.of_apply, Matrix.neg_apply, map_mul, map_sub, hsh, hss]
    ring
  have hcont : Continuous fun p : (AF F ⊗[F] E) × (AF F ⊗[F] E) => hh * (p.1 - s p.2) :=
    continuous_const.mul (continuous_fst.sub ((continuous_sigR σ).comp continuous_snd))
  refine ⟨_, C, (hΩ.prod hΩ).image hcont, fun μ => ?_⟩
  obtain ⟨Y, hY, hc⟩ := h μ
  have hd : ∀ i, s ((GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i) = (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := fun i => by
    rw [map_pow, hs_def, GlobalTheory.Eis.Conv.sigR_halfE]
  have htor : (tor F E fun i => (μ i : ℤ)).1 = Matrix.diagonal fun i => (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := by
    simp [tor, GlobalTheory.Eis.Conv.dg]
  have htor' : cT s (tor F E fun i => (μ i : ℤ)).1 = Matrix.diagonal fun i => (GlobalTheory.Eis.Conv.halfE F E).1 ^ μ i := by
    rw [htor]
    ext i k
    rw [cT_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hik : i = k
    · subst hik; simp [hd]
    · simp [hik, Ne.symm hik]
  refine ⟨Y.image sk, (Nat.cast_le.mpr Finset.card_image_le).trans (hY.trans (le_of_eq ?_)), ?_, fun x hx => ?_⟩
  · simp only [bse, ← pow_mul, mul_comm _ 2, show (4 : ℝ) = 2 ^ 2 by norm_num]
  · intro y hy
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.1 hy
    exact sk_skew z
  · obtain ⟨S₀, y, hy, ω, hω, e⟩ := hc x hx
    set c : E := algebraMap F E 2⁻¹ with hc_def
    have hσc : σ c = c := σ.commutes _
    refine ⟨Matrix.of fun i k => c * (S₀ i k - σ (S₀ k i)), ?_, sk y, Finset.mem_image_of_mem _ hy, sk ω, sk_skew ω,
      fun i k => ⟨(ω i k, ω k i), ⟨hω i k, hω k i⟩, rfl⟩, ?_⟩
    · ext i k
      simp only [cT_apply, Matrix.of_apply, Matrix.neg_apply, AlgHom.coe_toRingHom, map_mul, map_sub, hσc,
        sig_sig σ hσ]
      ring
    · rw [htor', htor]
      ext i k
      have hx1 : s (x k i) = - x i k := by
        have := congrFun (congrFun hx i) k
        rwa [cT_apply, Matrix.neg_apply] at this
      have e1 := congrFun (congrFun e i) k
      have e2 := congrArg s (congrFun (congrFun e k) i)
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, map_add, map_mul,
        hsi, hd] at e1 e2
      rw [hx1] at e2
      simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, adMat, Matrix.map_apply,
        Matrix.of_apply, sk, map_mul, map_sub, inclR_alg]
      rw [hc_def, inclR_alg, ← hh_def]
      linear_combination hh * e1 - hh * e2 - x i k * h2
end GlobalTheory.SkewAdCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumTieNumberFieldPointStatement
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.PDivGroup Matrix TensorProduct NumberField CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datum_tie_number_field_point : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E)) (ε : PreTilt O p) (h : ℕ) (D : Datum ε h (ℤ_[p] ⊗[ℤ] 𝓞 E)) (φ : P.V ≃ₗ[C] (Fin h → C)), IsPrimitiveRoot (root ε).untilt p → IsTie P D (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom φ → (⨆ σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O, eig C (actT D) σ) = ⊤ ∧ (⨆ σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O, eig C (actH D) σ) = ⊤ ∧ (∀ σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O, ∃ ψ : E →+* C, σ.comp (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom = embO P.integers ψ) ∧ ∀ (σ : ℤ_[p] ⊗[ℤ] 𝓞 E →+* O) (ψ : E →+* C), σ.comp (Algebra.TensorProduct.includeRight : 𝓞 E →ₐ[ℤ] ℤ_[p] ⊗[ℤ] 𝓞 E).toRingHom = embO P.integers ψ → (P.eigV (embO P.integers ψ)).map (φ : P.V →ₗ[C] (Fin h → C)) = eig C (actT D) σ ∧ (P.wRec (embO P.integers ψ)).map ((φ : P.V →ₗ[C] (Fin h → C)).restrictScalars O) = lieSub C D σ ∧ (open Classical in P.latTQuot (σ := fun φ' : E →+* C => embO P.integers φ') (isSplitting_embO P.integers) ψ).map ((φ : P.V →ₗ[C] (Fin h → C)).restrictScalars O) = eigPart C (actT D) σ ⊤ ∧ D.lieRank σ = Module.finrank C (P.eigW (embO P.integers ψ)) := by
  first | exact @GlobalTheory.DetInv.PadicInclusionHoms.eig_lattices_of_isTie | exact GlobalTheory.DetInv.PadicInclusionHoms.eig_lattices_of_isTie | (intros; apply GlobalTheory.DetInv.PadicInclusionHoms.eig_lattices_of_isTie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImageBirationalLinearSystemEqSelfIntStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_image_birational_linearSystem_eq_selfInt : Quoted → ∀ (F : Type) [Field F] [NumberField F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → 0 < S.del ∧ (hilbertDegree S.imageIdeal : ℤ) = S.del ∧ ringKrullDim (MvPolynomial (Fin S.N) F ⧸ S.imageIdeal) = (S.D + 1 : ℕ) := by
  first | exact @GlobalTheory.ImageDegree.degree_image_eq_topSelf | exact GlobalTheory.ImageDegree.degree_image_eq_topSelf | (intros; apply GlobalTheory.ImageDegree.degree_image_eq_topSelf <;> assumption)
end

