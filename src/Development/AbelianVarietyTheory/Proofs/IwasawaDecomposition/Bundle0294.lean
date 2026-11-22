import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0271
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneWeightSpaceStable
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdBlockSymbolDetPow
section
set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.BlockTop

section General

variable {α : Type} [Fintype α] [DecidableEq α]

def graph (w : Equiv.Perm α) : α × α →₀ ℕ := ∑ a, Finsupp.single (a, w a) 1

def tc (P : MvPolynomial (α × α) ℂ) : ℂ :=
  ∑ w : Equiv.Perm α, ((Equiv.Perm.sign w : ℤ) : ℂ) * coeff (graph w) P

theorem topCoeff_eq_tc {n : ℕ} (P : MvPolynomial (Fin n × Fin n) ℂ) : GlobalTheory.GoodMetric.topCoeff P = tc P := rfl

theorem tc_sum {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (α × α) ℂ) :
    tc (∑ i ∈ s, f i) = ∑ i ∈ s, tc (f i) := by
  simp only [tc, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem tc_monomial (u : α × α →₀ ℕ) (c : ℂ) : tc (monomial u c) = c * tc (monomial u 1) := by
  simp only [tc, coeff_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> ring

theorem graph_apply (w : Equiv.Perm α) (a b : α) : graph w (a, b) = if w a = b then 1 else 0 := by
  rw [graph, Finsupp.finset_sum_apply, Finset.sum_eq_single a (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

theorem tc_rename_equiv {β : Type} [Fintype β] [DecidableEq β] (e : α ≃ β) (P : MvPolynomial (α × α) ℂ) :
    tc (rename (Prod.map e e) P) = tc P := by
  unfold tc
  rw [← (Equiv.permCongr e).sum_comp]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hg : graph (e.permCongr v) = Finsupp.mapDomain (Prod.map e e) (graph v) := by
    unfold graph
    rw [Finsupp.mapDomain_finset_sum]
    simp only [Finsupp.mapDomain_single]
    rw [← e.sum_comp]
    simp [Equiv.permCongr_apply]
  have hinj : Function.Injective (Prod.map e e) := fun x y h => by
    simp only [Prod.map, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    exact Prod.ext h.1 h.2
  rw [hg, coeff_rename_mapDomain _ hinj, Equiv.Perm.sign_permCongr]

theorem prod_monomial' {κ : Type} (s : Finset κ) (f : κ → α × α →₀ ℕ) (c : κ → ℂ) :
    ∏ i ∈ s, (monomial (f i) (c i) : MvPolynomial (α × α) ℂ) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, ih, monomial_mul, Finset.sum_insert ha, Finset.prod_insert ha]

end General

section Blocks

variable {ι γ : Type} [Fintype ι] [DecidableEq ι] [Fintype γ] [DecidableEq γ]

def emb (τ : ι) (v : γ × γ) : (ι × γ) × (ι × γ) := ((τ, v.1), (τ, v.2))

theorem emb_injective (τ : ι) : Function.Injective (emb (γ := γ) τ) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [emb, Prod.mk.injEq, true_and] at h
  simp [h]

def glue (D : ι → (γ × γ →₀ ℕ)) : (ι × γ) × (ι × γ) →₀ ℕ := ∑ τ, (D τ).mapDomain (emb τ)

theorem glue_emb (D : ι → (γ × γ →₀ ℕ)) (τ : ι) (v : γ × γ) : glue D (emb τ v) = D τ v := by
  unfold glue
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply (emb_injective τ) _ _
  · intro τ' _ hτ'
    apply Finsupp.mapDomain_notin_range
    rintro ⟨u, hu⟩
    simp only [emb, Prod.mk.injEq] at hu
    exact hτ' hu.1.1
  · simp

theorem glue_off (D : ι → (γ × γ →₀ ℕ)) (a b : ι × γ) (h : a.1 ≠ b.1) : glue D (a, b) = 0 := by
  unfold glue
  rw [Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun τ _ => Finsupp.mapDomain_notin_range _ _ ?_
  rintro ⟨u, hu⟩
  simp only [emb, Prod.mk.injEq] at hu
  exact h (by rw [← hu.1, ← hu.2])

theorem glue_injective : Function.Injective (glue (ι := ι) (γ := γ)) := by
  intro D D' h
  funext τ
  ext v
  rw [← glue_emb, h, glue_emb]

theorem graph_prodCongrRight (σ : ι → Equiv.Perm γ) :
    graph (Equiv.prodCongrRight σ) = glue fun τ => graph (σ τ) := by
  unfold glue graph
  simp only [Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_single]
  rw [Fintype.sum_prod_type]
  rfl

theorem exists_prodCongrRight (w : Equiv.Perm (ι × γ)) (hw : ∀ a, (w a).1 = a.1) :
    ∃ σ : ι → Equiv.Perm γ, Equiv.prodCongrRight σ = w := by
  have hw' : ∀ b, (w.symm b).1 = b.1 := fun b => by
    have := hw (w.symm b)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have li : ∀ τ x, (w.symm (τ, (w (τ, x)).2)).2 = x := fun τ x => by
    have e1 : (τ, (w (τ, x)).2) = w (τ, x) := Prod.ext (hw (τ, x)).symm rfl
    rw [e1, Equiv.symm_apply_apply]
  have ri : ∀ τ x, (w (τ, (w.symm (τ, x)).2)).2 = x := fun τ x => by
    have e1 : (τ, (w.symm (τ, x)).2) = w.symm (τ, x) := Prod.ext (hw' (τ, x)).symm rfl
    rw [e1, Equiv.apply_symm_apply]
  refine ⟨fun τ => Equiv.mk (fun x => (w (τ, x)).2) (fun x => (w.symm (τ, x)).2) (li τ) (ri τ), ?_⟩
  ext ⟨τ, x⟩
  · simp [hw]
  · simp

theorem prodCongrRight_injective :
    Function.Injective (fun σ : ι → Equiv.Perm γ => (Equiv.prodCongrRight σ : Equiv.Perm (ι × γ))) := by
  intro σ σ' h
  funext τ
  ext x
  have := congrArg (fun w : Equiv.Perm (ι × γ) => (w (τ, x)).2) h
  simpa using this

theorem tc_monomial_glue (D : ι → (γ × γ →₀ ℕ)) :
    tc (monomial (glue D) (1 : ℂ)) = ∏ τ, tc (monomial (D τ) (1 : ℂ)) := by
  simp only [tc, coeff_monomial]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  set F : Equiv.Perm (ι × γ) → ℂ := fun w => ((Equiv.Perm.sign w : ℤ) : ℂ) * if glue D = graph w then 1 else 0 with hF
  have h1 : ∑ w, F w = ∑ w ∈ Finset.univ.image (fun σ : ι → Equiv.Perm γ => Equiv.prodCongrRight σ), F w := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun w _ hw => ?_).symm
    simp only [hF]
    rw [if_neg, mul_zero]
    intro hg
    apply hw
    have hb : ∀ a, (w a).1 = a.1 := by
      intro a
      by_contra hne
      have e1 := glue_off D a (w a) (Ne.symm hne)
      rw [hg, graph_apply, if_pos rfl] at e1
      exact one_ne_zero e1
    obtain ⟨σ, hσ⟩ := exists_prodCongrRight w hb
    exact Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, hσ⟩
  rw [h1, Finset.sum_image fun x _ y _ h => prodCongrRight_injective h]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [hF, graph_prodCongrRight, glue_injective.eq_iff, Equiv.Perm.sign_prodCongrRight]
  rw [Finset.prod_mul_distrib]
  push_cast
  congr 1
  by_cases hD : D = fun τ => graph (σ τ)
  · rw [if_pos hD]
    symm
    exact Finset.prod_eq_one fun τ _ => if_pos (congrFun hD τ)
  · rw [if_neg hD]
    obtain ⟨τ, hτ⟩ : ∃ τ, D τ ≠ graph (σ τ) := by
      by_contra hall
      push_neg at hall
      exact hD (funext hall)
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)

theorem tc_prod_rename (f : ι → MvPolynomial (γ × γ) ℂ) :
    tc (∏ τ, rename (emb τ) (f τ)) = ∏ τ, tc (f τ) := by
  have hL : ∏ τ, rename (emb τ) (f τ) = ∑ x ∈ Fintype.piFinset fun τ => (f τ).support,
      monomial (glue x) (∏ τ, coeff (x τ) (f τ)) := by
    calc ∏ τ, rename (emb τ) (f τ)
        = ∏ τ, ∑ d ∈ (f τ).support, monomial (d.mapDomain (emb τ)) (coeff d (f τ)) := by
          refine Finset.prod_congr rfl fun τ _ => ?_
          conv_lhs => rw [(f τ).as_sum]
          rw [map_sum]
          simp only [rename_monomial]
      _ = _ := by
          rw [Finset.prod_univ_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [prod_monomial']
          rfl
  have hR : ∀ τ, tc (f τ) = ∑ d ∈ (f τ).support, coeff d (f τ) * tc (monomial d (1 : ℂ)) := by
    intro τ
    conv_lhs => rw [(f τ).as_sum]
    rw [tc_sum]
    exact Finset.sum_congr rfl fun d _ => tc_monomial _ _
  rw [hL, tc_sum]
  simp_rw [hR]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tc_monomial, tc_monomial_glue, Finset.prod_mul_distrib]

end Blocks

end GlobalTheory.BlockTop

namespace GlobalTheory.BlockTop

def symMat (p q : ℕ) : Matrix (Fin p) (Fin p) (MvPolynomial ((Fin p × Fin q) × (Fin p × Fin q)) ℂ) :=
  Matrix.of fun i j => ∑ b : Fin q, X ((i, b), (j, b))

theorem det_map_rename {σ' : Type} (p q : ℕ) (g : (Fin p × Fin q) × (Fin p × Fin q) → σ') :
    ((symMat p q).map (rename (R := ℂ) g)).det = rename g (symMat p q).det :=
  (AlgHom.map_det (rename g) _).symm

theorem blockSym_eq {ι : Type} [Fintype ι] {p q n : ℕ} (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι) :
    GlobalTheory.DomainDens.blockSym h τ = (symMat p q).map
      (rename (Prod.map (Fintype.equivFinOfCardEq h) (Fintype.equivFinOfCardEq h) ∘ emb τ)) := by
  ext i j
  simp [GlobalTheory.DomainDens.blockSym, symMat, map_sum, rename_X, emb]

end GlobalTheory.BlockTop

open GlobalTheory.BlockTop in

theorem GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow : ∀ (ι : Type) [Fintype ι] (p q n : ℕ)
    (h : Fintype.card (ι × Fin p × Fin q) = n) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q),
    GlobalTheory.GoodMetric.topCoeff (∏ τ, (GlobalTheory.DomainDens.blockSym h τ).det ^ q) =
      GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) ^ Fintype.card ι := by
  intro ι _ p q n h h1
  classical
  set e := Fintype.equivFinOfCardEq h
  set e1 := Fintype.equivFinOfCardEq h1
  have hL : ∏ τ, (GlobalTheory.DomainDens.blockSym h τ).det ^ q =
      rename (Prod.map e e) (∏ τ, rename (emb τ) ((symMat p q).det ^ q)) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [blockSym_eq, det_map_rename, rename_rename, map_pow]
  set e' : Fin p × Fin q ≃ Fin (p * q) := (Equiv.punitProd (Fin p × Fin q)).symm.trans e1
  have hR : (GlobalTheory.DomainDens.blockSym h1 ()).det ^ q = rename (Prod.map e' e') ((symMat p q).det ^ q) := by
    rw [blockSym_eq, det_map_rename, map_pow]
    rfl
  rw [hL, hR, topCoeff_eq_tc, topCoeff_eq_tc, tc_rename_equiv, tc_rename_equiv, tc_prod_rename,
    Finset.prod_const, Finset.card_univ]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCongruenceConjContainsCongruence
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.CongConjugate

open ReciprocityTheory.Aut Formalism.AUTREP

theorem congConj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), principalLevelFrame.CongConj L n := by
  intro L _ _ _ n h N hN
  obtain ⟨d, hd, hdh⟩ := GlobalTheory.FinTypCount.exists_denom_matrix
    (((h.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)))
  obtain ⟨e, he, heh⟩ := GlobalTheory.FinTypCount.exists_denom_matrix
    ((((h⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)))
  refine ⟨N * d * e, Nat.mul_pos (Nat.mul_pos hN hd) he, fun κ hκ => ?_⟩
  choose Y hY eY using hκ.2
  set H : Matrix (Fin n) (Fin n) (AL L) := ((h.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hH
  set Hi : Matrix (Fin n) (Fin n) (AL L) := (((h⁻¹).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hHi
  have hHH : Hi * H = 1 := by
    rw [hHi, hH, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hK : ((κ.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      1 + ((N * d * e : ℕ) : AL L) • Matrix.of Y := by
    ext a b
    have := eY a b
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    rw [← this]; ring
  have hprod : (((h⁻¹ * κ * h).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      Hi * (1 + ((N * d * e : ℕ) : AL L) • Matrix.of Y) * H := by
    rw [← hK]; simp [hHi, hH, Subgroup.coe_mul, Units.val_mul]
  set Z : Matrix (Fin n) (Fin n) (AL L) := ((e : AL L) • Hi) * Matrix.of Y * ((d : AL L) • H) with hZ
  have hZint : ∀ i j, Z i j ∈ ALint L := by
    intro i j
    rw [hZ, Matrix.mul_apply]
    refine Subring.sum_mem _ fun b _ => Subring.mul_mem _ ?_ ?_
    · rw [Matrix.mul_apply]
      refine Subring.sum_mem _ fun a _ => Subring.mul_mem _ ?_ (hY a b)
      simpa [Matrix.smul_apply, smul_eq_mul] using heh i a
    · simpa [Matrix.smul_apply, smul_eq_mul] using hdh b j
  have hdiff : Hi * (1 + ((N * d * e : ℕ) : AL L) • Matrix.of Y) * H - 1 = (N : AL L) • Z := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hHH, add_sub_cancel_left, hZ]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, smul_smul]
    congr 1
    push_cast; ring
  have hentry : ∀ i j, (((h⁻¹ * κ * h).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j -
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * Z i j := by
    intro i j
    rw [hprod]
    have h2 := congrFun (congrFun hdiff i) j
    simpa [Matrix.sub_apply, Matrix.smul_apply] using h2
  refine ⟨fun i j => ?_, fun i j => ⟨Z i j, hZint i j, hentry i j⟩⟩
  have h3 : (((h⁻¹ * κ * h).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j =
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j + (N : AL L) * Z i j := by
    rw [← hentry]; ring
  rw [h3]
  refine add_mem ?_ (Subring.mul_mem _ (natCast_mem _ _) (hZint i j))
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

end GlobalTheory.CongConjugate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRootExchangeMirrorIdentity
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootExch.Mirror

open GlobalTheory.BesselCompare (mt_mul mt_one hA_add hA_smul hA_smul_right hA_vec cA_inc hD_swap_zero)

variable {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}

theorem suppAt_of_isK {ε a : AE D} {v y : Fin B.rank → AE D} {k : GA D B} (hk : IsK B v y k) (hy : a • y = y)
    (h1 : (ε + cA D ε) * a = a) (h2 : (ε + cA D ε) * cA D a = cA D a) : SuppAt ε B k := by
  rw [suppAt_iff_vec]
  intro x
  have e1 : (ε + cA D ε) * hA B x y = hA B x y := by
    rw [← hy, hA_smul_right, ← mul_assoc, h2]
  have e2 : (ε + cA D ε) • y = y := by
    conv_lhs => rw [← hy]
    rw [smul_smul, h1, hy]
  have e : (mt B k).mulVec x - x = hA B x y • v - hA B x v • y := by rw [hk x]; abel
  rw [e, smul_sub, smul_smul, e1, smul_comm, e2]

def fixGrp (B : HSp D) (x : Fin B.rank → AE D) : Subgroup (GA D B) where
  carrier := {g | (mt B g).mulVec x = x}
  one_mem' := by show _ = _; rw [mt_one, Matrix.one_mulVec]
  mul_mem' := fun {g h} hg hh => by
    show _ = _
    rw [mulVec_mul, show (mt B h).mulVec x = x from hh, show (mt B g).mulVec x = x from hg]
  inv_mem' := fun {g} hg => by
    show _ = _
    conv_lhs => rw [← show (mt B g).mulVec x = x from hg]
    rw [mulVec_inv_cancel]

theorem fix_of_isK (d : BesselDatum A B ι) {i l : Fin (d.ρ + 1)} (h : l ≠ i) {t} {g : GA D B}
    (hg : IsK B (vecA B (dual d i)) (iA ι t) g) : g ∈ fixGrp B (vecA B (d.aux l)) := by
  show _ = _
  rw [hg, hA_vec_iA (besselDatum_auxiliaryVector_orthogonal_image d l), hA_vec, (GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d).1, if_neg h]
  simp

theorem fix_of_ExGe (d : BesselDatum A B ι) {ε : AE D} (he : IsSplitIdem D ε) {p : ℕ} {l : Fin (d.ρ + 1)} (h : l.1 < p)
    {g : GA D B} (hg : g ∈ ExGe d ε p) : g ∈ fixGrp B (vecA B (d.aux l)) := by
  refine (Subgroup.closure_le _).2 (Set.iUnion_subset fun i => Set.iUnion_subset fun hi u hu => ?_) hg
  obtain ⟨t, -, ht⟩ := (GlobalTheory.T.mem_besselExchangeGroup_iff_rootExchange D A B ι d ε he i u).1 (Subgroup.subset_closure hu)
  exact fix_of_isK d (fun e => by rw [e] at h; omega) ht

theorem basis_castSucc (d : BesselDatum A B ι) (l : Fin d.ρ) : d.aux l.castSucc = d.e l := by
  unfold BesselDatum.aux; rw [Fin.snoc_castSucc]

theorem hD_basis_e (d : BesselDatum A B ι) (m) (j : Fin d.ρ) : B.hD (d.aux m) (d.e j) = 0 := by
  unfold BesselDatum.aux
  refine Fin.lastCases ?_ (fun l => ?_) m
  · rw [Fin.snoc_last]; exact hD_swap_zero (d.ez j)
  · rw [Fin.snoc_castSucc]; exact d.ee l j

theorem hD_basis_succ_f (d : BesselDatum A B ι) (i : Fin d.ρ) : B.hD (d.aux i.succ) (d.f i) = 0 := by
  have key : ∀ m : Fin (d.ρ + 1), m.1 = i.1 + 1 → B.hD (d.aux m) (d.f i) = 0 := by
    intro m
    unfold BesselDatum.aux
    refine Fin.lastCases (fun _ => ?_) (fun l hl => ?_) m
    · rw [Fin.snoc_last]; exact hD_swap_zero (d.fz i)
    · rw [Fin.snoc_castSucc, d.ef, if_neg]
      rintro rfl
      simp at hl
  exact key _ rfl

theorem conj_apply {v y : Fin B.rank → AE D} {k c : GA D B} (hk : IsK B v y k) (hc : c ∈ fixGrp B v)
    {x : Fin B.rank → AE D} (hx : hA B x v = 0) :
    (mt B (c * k * c⁻¹)).mulVec x = x + hA B ((mt B c⁻¹).mulVec x) y • v := by
  have hc' : (mt B c).mulVec v = v := hc
  have h0 : hA B ((mt B c⁻¹).mulVec x) v = 0 := by rw [hA_mt_left, inv_inv, hc', hx]
  rw [mulVec_mul, mulVec_mul, hk, h0, zero_smul, sub_zero, Matrix.mulVec_add, Matrix.mulVec_smul, hc', mulVec_cancel_inv]

theorem sum_single (d : BesselDatum A B ι) (j : Fin d.ρ) (a : AE D) :
    ∑ l, (if l = j then a else 0) • vecA B (d.e l) = a • vecA B (d.e j) := by
  simp [ite_smul]

theorem mirror : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (ε : AE D), IsSplitIdem D ε → ∀ (j : Fin d.ρ) (t₀ t : Fin A.rank → AE D) (b₀ k : GA D B), ε • t₀ = t₀ → cA D ε • t = t → IsK B (vecA B (dual d j.succ)) (iA ι t₀) b₀ → IsK B (vecA B (d.e j)) (iA ι t) k → SuppAt ε B k ∧ ∀ b ∈ ExGe d ε (j.1 + 2), b * (b₀ * k * b₀⁻¹) * b⁻¹ ∈ d.N ∧ SuppAt ε B (b * (b₀ * k * b₀⁻¹) * b⁻¹) ∧ d.psiN ψ (b * (b₀ * k * b₀⁻¹) * b⁻¹) = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D d.θ * hA A t₀ t)) := by
  intro D A B ι d ψ ε he j t₀ t b₀ k ht₀ ht hb₀ hk
  have h1 : ε * ε = ε := he.1
  have h2 : ε * cA D ε = 0 := he.2.1
  have h3 : cA D ε * cA D ε = cA D ε := by rw [← RingHom.map_mul, h1]
  have a1 : (ε + cA D ε) * ε = ε := by rw [add_mul, h1, mul_comm, h2, add_zero]
  have a2 : (ε + cA D ε) * cA D ε = cA D ε := by rw [add_mul, h2, h3, zero_add]
  have sk : SuppAt ε B k := suppAt_of_isK (a := cA D ε) hk (by rw [← iA_smul, ht]) a2 (by rw [cA_cA, a1])
  have sb : SuppAt ε B b₀ := suppAt_of_isK (a := ε) hb₀ (by rw [← iA_smul, ht₀]) a1 a2
  refine ⟨sk, fun b hb => ?_⟩
  have sb' := suppAt_of_mem_ExGe hb
  have hn : b * (b₀ * k * b₀⁻¹) * b⁻¹ = (b * b₀) * k * (b * b₀)⁻¹ := by group
  have hfix : ∀ l : Fin d.ρ, l ≤ j → b * b₀ ∈ fixGrp B (vecA B (d.e l)) := by
    intro l hl
    have hl' : l.1 ≤ j.1 := hl
    rw [← basis_castSucc]
    refine mul_mem (fix_of_ExGe d he (by simp; omega) hb) (fix_of_isK d (fun e => ?_) hb₀)
    have := congrArg Fin.val e
    simp at this; omega
  have hact : ∀ x : B.V, B.hD x (d.e j) = 0 → actV B (b * (b₀ * k * b₀⁻¹) * b⁻¹) x =
      vecA B x + hA B ((mt B (b * b₀)⁻¹).mulVec (vecA B x)) (iA ι t) • vecA B (d.e j) := by
    intro x hx
    rw [hn]
    exact conj_apply hk (hfix j le_rfl) (by rw [hA_vec, hx, map_zero])
  refine ⟨Subgroup.subset_closure ⟨fun i => ?_, fun x hx => ?_⟩,
    suppAt_mul (suppAt_mul sb' (suppAt_mul (suppAt_mul sb sk) (suppAt_inv sb))) (suppAt_inv sb'), ?_⟩
  · refine ⟨_, fun l hl => ?_, by rw [hact _ (d.ee i j), ← sum_single]⟩
    split_ifs with h
    · subst h
      rw [show (mt B (b * b₀)⁻¹).mulVec (vecA B (d.e i)) = _ from inv_mem (hfix i hl), hA_vec_iA (d.eA i)]
    · rfl
  · exact ⟨_, by rw [hact _ (hx j), ← sum_single]⟩
  · unfold BesselDatum.psiN BesselDatum.simpleSum
    congr 3
    have e : ∀ i : Fin d.ρ, hA B (actV B (b * (b₀ * k * b₀⁻¹) * b⁻¹) (d.aux i.succ)) (vecA B (d.f i)) =
        if j = i then hA B ((mt B (b * b₀)⁻¹).mulVec (vecA B (d.aux i.succ))) (iA ι t) else 0 := by
      intro i
      rw [hact _ (hD_basis_e d _ j), hA_add, hA_smul, hA_vec, hA_vec, hD_basis_succ_f, d.ef]
      split_ifs <;> simp
    simp only [e, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hb' : (mt B b⁻¹).mulVec (vecA B (d.aux j.succ)) = vecA B (d.aux j.succ) :=
      inv_mem (fix_of_ExGe d he (by simp) hb)
    have p1 : hA B (iA ι t) (vecA B (dual d j.succ)) = 0 := by
      rw [← hA_herm, hA_vec_iA (dual_perp d _), map_zero]
    rw [_root_.mul_inv_rev, mulVec_mul, hb', hA_mt_left, inv_inv, hb₀, p1, zero_smul, sub_zero, hA_add_right,
      hA_vec_iA (besselDatum_auxiliaryVector_orthogonal_image d _), zero_add, hA_smul_right, hA_herm, hA_vec, (GlobalTheory.T.besselDatum_adelicVector_decomposition D A B ι d).1, if_pos rfl,
      map_one, mul_one, hA_iA d.isom]

end GlobalTheory.RootExch.Mirror

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneDirectSumOfComplStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_direct_sum_of_compl : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (S T : Submodule ℂ V) (hS : IsSubWD a S) (hT : IsSubWD a T), IsCompl S T → WD.mk a = (WD.mk (restrict a S hS)).lpSum (WD.mk (restrict a T hT)) := by
  first | exact @GlobalTheory.WeilDeligne.PrimDecomp.sumiso | exact GlobalTheory.WeilDeligne.PrimDecomp.sumiso | (intros; apply GlobalTheory.WeilDeligne.PrimDecomp.sumiso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneWeightSpaceStableStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_weight_space_stable : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V), (∀ (k : ℤ) (σ : Weil h), ∀ v ∈ wtSpace a k, a.ρ σ v ∈ wtSpace a k) ∧ ∀ (k : ℤ), ∀ v ∈ wtSpace a k, a.N v ∈ wtSpace a (k + 2) := by
  first | exact @GlobalTheory.WeilDeligne.PrimDecomp.wtSpace_stable | exact GlobalTheory.WeilDeligne.PrimDecomp.wtSpace_stable | (intros; apply GlobalTheory.WeilDeligne.PrimDecomp.wtSpace_stable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilTiedEqOfEqTied
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem weilTiedEq_of_eqTied : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (W : WeilTied D X T), WeilThetaCompatibility W → WeilCompatibleEquivariance W :=
  fun _ _ _ _ h => ⟨h.range, h.Heisenberg₂, h.aut, h.cont, h.unit, h.split, ⟨h.twW, h.twV⟩, h.th⟩

end GlobalTheory.Mem.Th
end

