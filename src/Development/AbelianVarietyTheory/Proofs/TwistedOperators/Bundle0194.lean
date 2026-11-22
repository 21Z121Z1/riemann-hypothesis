import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittExtensionHomMulEmbeddedAnisotropic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.JacHom

variable {D : D7}

section Inv

variable {S T : HSp D}

theorem symplOH_mul_mt (a b : WO S T) (g : GA D S) :
    symplOH S T (a ⬝ mt S g) (b ⬝ mt S g) = symplOH S T a b := by
  have h1 : mt S g ⬝ mt S g⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  rw [mt_inv] at h1
  have key : mt S g ⬝ (giA S ⬝ adj (mt S g)) = giA S := by
    have e : mt S g ⬝ (giA S ⬝ adj (mt S g)) = mt S g ⬝ (giA S ⬝ (adj (mt S g) ⬝ gA S)) ⬝ giA S := by
      simp only [Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one]
    rw [e, h1, Matrix.one_mul]
  rw [symplOH_eq, symplOH_eq, hO_eq_trace, hO_eq_trace, adj_mul]
  have e2 : giA S ⬝ (adj (mt S g) ⬝ adj b ⬝ (gA T ⬝ (a ⬝ mt S g))) =
      (giA S ⬝ adj (mt S g) ⬝ adj b ⬝ gA T ⬝ a) ⬝ mt S g := by simp only [Matrix.mul_assoc]
  have e3 : mt S g ⬝ (giA S ⬝ adj (mt S g) ⬝ adj b ⬝ gA T ⬝ a) =
      (mt S g ⬝ (giA S ⬝ adj (mt S g))) ⬝ (adj b ⬝ (gA T ⬝ a)) := by simp only [Matrix.mul_assoc]
  rw [e2, Matrix.trace_mul_comm, e3, key]

theorem symplOH_mul_mt_right (a b : WO S T) (g : GA D S) :
    symplOH S T a (b ⬝ mt S g) = symplOH S T (a ⬝ mt S g⁻¹) b := by
  conv_lhs => rw [← symplOH_mul_mt a (b ⬝ mt S g) g⁻¹]
  rw [Matrix.mul_assoc b, ← mt_mul, mul_inv_cancel, mt_one, Matrix.mul_one]

end Inv

section FinalTheorems

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ)

theorem extX_mul (n : GA D S) : d.extX T x ⬝ mt S n =
    d.extX T (d.extX T x ⬝ mt S n ⬝ d.jX) + d.ext0 T (ptS d T x n) + d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY) := by
  rw [HypDec.extX_apply, HypDec.matrixExtendByZero_apply, HypDec.extY_apply, HypDec.extX_apply, ptS, HypDec.extX_apply]
  conv_lhs => rw [← Matrix.mul_one (x ⬝ d.pX ⬝ mt S n), ← d.sum_eq_one]
  simp only [Matrix.mul_add, Matrix.mul_assoc]

variable {T x}

theorem extX_mul_jX (hx : ∀ u ∈ UX D ρ, x ⬝ u.1 = x) {n : GA D S} (hn : n ∈ flagN d) :
    d.extX T x ⬝ mt S n ⬝ d.jX = x := by
  obtain ⟨M, b, hM, h1, -⟩ := exists_blocks d hn
  have htri : (1 + M).BlockTriangular id := fun i j (h : j < i) => by
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt h), hM i j (le_of_lt h), add_zero]
  have hdiag : ∀ i, (1 + M) i i = 1 := fun i => by rw [Matrix.add_apply, Matrix.one_apply_eq, hM i i le_rfl, add_zero]
  have hu : IsUnit (1 + M) := (Matrix.isUnit_iff_isUnit_det _).2 (by
    rw [Matrix.det_of_upperTriangular htri]; simp only [hdiag, Finset.prod_const_one]; exact isUnit_one)
  have hmem : hu.unit ∈ UX D ρ := fun i j => by
    refine ⟨fun h => ?_, ?_⟩
    · change (1 + M) i j = 0; exact htri h
    · change (1 + M) i i = 1; exact hdiag i
  have e : d.extX T x ⬝ mt S n ⬝ d.jX = x ⬝ (1 + M) := by
    rw [HypDec.extX_apply, Matrix.mul_assoc, Matrix.mul_assoc, h1, Matrix.mul_add, ← Matrix.mul_assoc d.pX, d.pX_jX,
      Matrix.one_mul]
  rw [e]
  exact hx _ hmem

end FinalTheorems

section Flag

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {T : HSp D} {x : Mx D T.rank ρ}
  (hx : ∀ u ∈ UX D ρ, x ⬝ u.1 = x)
include hx

theorem extX_mul_flag {n : GA D S} (hn : n ∈ flagN d) : d.extX T x ⬝ mt S n =
    d.extX T x + d.ext0 T (ptS d T x n) + d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY) := by
  have h := extX_mul d T x n
  rwa [extX_mul_jX d hx hn] at h

theorem ptS_mul {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    ptS d T x (n * n') = ptS d T x n + ptS d T x n' := by
  obtain ⟨M, b, -, -, h2⟩ := exists_blocks d hn'
  have e : ptS d T x (n * n') = d.extX T x ⬝ mt S n ⬝ (mt S n' ⬝ d.j0) := by
    rw [ptS, mt_mul, Matrix.mul_assoc (d.extX T x), Matrix.mul_assoc (d.extX T x), Matrix.mul_assoc]
  rw [e, extX_mul_flag d hx hn, h2]
  have e' : ptS d T x n' = d.extX T x ⬝ (d.j0 + d.jX ⬝ b) := by rw [ptS, Matrix.mul_assoc, h2]
  rw [e']
  simp only [HypDec.extX_apply, HypDec.matrixExtendByZero_apply, HypDec.extY_apply, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    d.pX_j0, d.p0_j0, d.pY_j0, d.p0_jX, d.pY_jX, cancel₂ d.p0_jX, cancel₂ d.pY_jX, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, add_zero, zero_add]

end Flag

section Flag2

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {T : HSp D} {x : Mx D T.rank ρ}

theorem symplOH_neg_left' {A B : HSp D} (a b : WO A B) : symplOH A B (-a) b = -symplOH A B a b := by
  rw [eq_neg_iff_add_eq_zero, ← GlobalTheory.OrientedHeis.symplOH_add_left, neg_add_cancel, symplOH_zero_left]

theorem ptS_one : ptS d T x 1 = 0 := by
  rw [ptS, mt_one, Matrix.mul_one, HypDec.extX_apply, Matrix.mul_assoc, d.pX_j0, Matrix.mul_zero]

variable (hx : ∀ u ∈ UX D ρ, x ⬝ u.1 = x)
include hx

theorem ptS_inv {n : GA D S} (hn : n ∈ flagN d) : ptS d T x n⁻¹ = -ptS d T x n := by
  have h := ptS_mul d hx (inv_mem hn) hn
  rw [inv_mul_cancel, ptS_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem cenS_flag {n : GA D S} (hn : n ∈ flagN d) :
    cenS d T x n = symplOH S T (d.extX T x) (d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY)) := by
  conv_lhs => rw [cenS, extX_mul_flag d hx hn]
  rw [GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_self, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, zero_add, zero_add]

theorem cenS_mul {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    cenS d T x (n * n') = cenS d T x n + cenS d T x n' + symplOH S₀ T (ptS d T x n) (ptS d T x n') := by
  have hi : n'⁻¹ ∈ flagN d := inv_mem hn'
  have h0 : symplOH S T (d.extX T x) (d.ext0 T (ptS d T x n) ⬝ mt S n') =
      symplOH S₀ T (ptS d T x n) (ptS d T x n') := by
    rw [symplOH_mul_mt_right, extX_mul_flag d hx hi, GlobalTheory.OrientedHeis.symplOH_add_left,
      GlobalTheory.OrientedHeis.symplOH_add_left, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, HypDec.wittDecomp_sympl_extAnisotropic_extAnisotropic, HypDec.wittDecomp_sympl_extDual_extAnisotropic,
      ptS_inv d hx hn', symplOH_neg_left', symplOH_skew S₀ T (ptS d T x n), neg_neg, zero_add, add_zero]
  have hY : symplOH S T (d.extX T x) (d.extY T (d.extX T x ⬝ mt S n ⬝ d.jY) ⬝ mt S n') = cenS d T x n := by
    rw [symplOH_mul_mt_right, extX_mul_flag d hx hi, GlobalTheory.OrientedHeis.symplOH_add_left,
      GlobalTheory.OrientedHeis.symplOH_add_left, symplOH_skew S T (d.extY T _) (d.ext0 T _), HypDec.wittDecomp_sympl_extDual_extAnisotropic,
      HypDec.symplOH_extY_extY, neg_zero, add_zero, add_zero, cenS_flag d hx hn]
  have e : cenS d T x (n * n') = symplOH S T (d.extX T x) (d.extX T x ⬝ mt S n ⬝ mt S n') := by
    rw [cenS, mt_mul, Matrix.mul_assoc]
  rw [e, extX_mul_flag d hx hn, Matrix.add_mul, Matrix.add_mul, GlobalTheory.OrientedHeis.symplOH_add_right,
    GlobalTheory.OrientedHeis.symplOH_add_right, h0, hY, ← cenS]
  ring

variable (ψ : AddChar (AF D.host.F) ℂ)

theorem jacS_mul {n n' : GA D S} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) (f : WO S₀ T → ℂ) :
    jacS ψ d T x (n * n') f = jacS ψ d T x n (jacS ψ d T x n' f) := by
  funext w
  simp only [jacS, ptS_mul d hx hn hn', cenS_mul d hx hn hn', Pi.smul_apply, smul_eq_mul, heisO,
    GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem jacS_mul_levi (n : GA D S) {u : GL (Fin ρ) (AE D)} (hu : u ∈ UX D ρ) :
    jacS ψ d T x (n * d.levi u) = jacS ψ d T x n := by
  have hL : d.extX T x ⬝ mt S (d.levi u)⁻¹ = d.extX T x := by
    rw [← map_inv, HypDec.extX_levi, hx _ (inv_mem hu)]
  have hpt : ptS d T x (n * d.levi u) = ptS d T x n := by
    rw [ptS, ptS, mt_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ (mt S (d.levi u)), d.wittDecomp_levi_inclAnisotropic]
  have hcen : cenS d T x (n * d.levi u) = cenS d T x n := by
    rw [cenS, cenS, mt_mul, ← Matrix.mul_assoc, symplOH_mul_mt_right, hL]
  funext f
  simp only [jacS, hpt, hcen]

end Flag2

section Conj

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {T : HSp D} (x : Mx D T.rank ρ)

theorem witt_extension_hom_mul_embedded_anisotropic (g : GA D S₀) : d.extX T x ⬝ mt S (d.emb0 g) = d.extX T x := by
  rw [HypDec.extX_apply, Matrix.mul_assoc, d.wittDecomp_projX_anisotropicEmbedding]

theorem extX_conj (n : GA D S) (g : GA D S₀) :
    d.extX T x ⬝ mt S (d.emb0 g * n * (d.emb0 g)⁻¹) = d.extX T x ⬝ mt S n ⬝ mt S (d.emb0 g⁻¹) := by
  rw [← map_inv, mt_mul, mt_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, witt_extension_hom_mul_embedded_anisotropic]

theorem ptS_conj (n : GA D S) (g : GA D S₀) :
    ptS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S₀ T g 1 (ptS d T x n) := by
  rw [ptS, ptS, extX_conj, actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc (d.extX T x ⬝ mt S n), d.wittDecomp_anisotropicEmbedding_inclAnisotropic]
  exact (Matrix.mul_assoc _ _ _).symm

theorem cenS_conj (n : GA D S) (g : GA D S₀) :
    cenS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = cenS d T x n := by
  rw [cenS, cenS, extX_conj, symplOH_mul_mt_right, ← map_inv, inv_inv, witt_extension_hom_mul_embedded_anisotropic]

end Conj

theorem jacS_hom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (x : Mx D T.rank ρ), (∀ u ∈ UX D ρ, x ⬝ u.1 = x) → (∀ b c, cenS d T x (d.nB b * d.nC c) = d.qS T c x) ∧
    (∀ n ∈ flagN d, ∀ n' ∈ flagN d, ptS d T x (n * n') = ptS d T x n + ptS d T x n' ∧
      cenS d T x (n * n') = cenS d T x n + cenS d T x n' + symplOH S₀ T (ptS d T x n) (ptS d T x n') ∧
      ∀ f, jacS ψ d T x (n * n') f = jacS ψ d T x n (jacS ψ d T x n' f)) ∧
    (∀ n ∈ flagN d, ∀ u ∈ UX D ρ, jacS ψ d T x (n * d.levi u) = jacS ψ d T x n) ∧
    ∀ n g, ptS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S₀ T g 1 (ptS d T x n) ∧
      cenS d T x (d.emb0 g * n * (d.emb0 g)⁻¹) = cenS d T x n := by
  intro D ψ S S₀ T ρ d x hx
  refine ⟨fun b c => ?_, fun n hn n' hn' => ⟨ptS_mul d hx hn hn', cenS_mul d hx hn hn', jacS_mul d hx ψ hn hn'⟩,
    fun n _ u hu => jacS_mul_levi d hx ψ n hu, fun n g => ⟨ptS_conj d x n g, cenS_conj d x n g⟩⟩
  have hB : d.nB b ∈ flagN d := d.nB_mem_NFlag b
  have hC : d.nC c ∈ flagN d := d.nC_mem_NFlag c
  have hpC : ptS d T x (d.nC c) = 0 := by
    rw [ptS, Matrix.mul_assoc, d.nC_j0, HypDec.extX_apply, Matrix.mul_assoc, d.pX_j0, Matrix.mul_zero]
  have e : pairS T x (x ⬝ (half D • (b ⬝ plus S₀ b))) = half D * hO S₀ T (x ⬝ b) (x ⬝ b) := by
    rw [← pairS_plus]
    simp only [pairS, Matrix.mul_smul, adj_smul, cA_half, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have h2 : symplOH S T (d.extX T x) (d.extY T (x ⬝ (half D • (b ⬝ plus S₀ b)))) = 0 := by
    refine eq_of_add_self (F := D.host.F) ?_
    rw [HypDec.symplOH_extX_extY, e, trHalf_half, ← symplOH_eq, GlobalTheory.OrientedHeis.symplOH_self, add_zero]
  have hcB : cenS d T x (d.nB b) = 0 := by
    have h1 : symplOH S T (d.extX T x) (d.extX T x ⬝ mt S (d.nB b)) +
        symplOH S T (d.extX T x) (d.extY T (x ⬝ (half D • (b ⬝ plus S₀ b)))) = 0 := by
      rw [← GlobalTheory.OrientedHeis.symplOH_add_right, HypDec.extX_nB, sub_add_cancel, GlobalTheory.OrientedHeis.symplOH_add_right,
        GlobalTheory.OrientedHeis.symplOH_self, HypDec.wittDecomp_sympl_extIsotropic_extAnisotropic, add_zero]
    rw [h2, add_zero] at h1
    exact h1
  rw [cenS_mul d hx hB hC, hcB, cenS_nC, hpC, symplOH_zero_right, zero_add, add_zero]

end GlobalTheory.JacHom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskySegmentClassExistsForEveryPlacing
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
open scoped TensorProduct

namespace GlobalTheory.SegmentClass

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def rangeEquiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) : ρ.Equiv f.range.toRepresentation :=
  .mk (LinearEquiv.ofInjective f.toLinearMap hf) fun g =>
    LinearMap.ext fun v => Subtype.ext (by change f (ρ g v) = σ g (f v); rw [f.isIntertwining])

def subIncl {ρ : Representation ℂ G V} (S : Subrepresentation ρ) : S.toRepresentation.IntertwiningMap ρ :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem subIncl_injective {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    Function.Injective (subIncl S) := Subtype.val_injective

theorem nonempty_equiv_of_eq {ρ : Representation ℂ G V} {S T : Subrepresentation ρ} (h : S = T) :
    Nonempty (S.toRepresentation.Equiv T.toRepresentation) := by
  subst h; exact ⟨.refl _⟩

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cuspRep (Δ : Segment k) : IrrRep (GL (Fin Δ.d) k) := Δ.cusp.choose

theorem cuspRep_cl (Δ : Segment k) : (cuspRep Δ).cl = Δ.start := Δ.cusp.choose_spec.1

theorem cuspRep_isCuspidal (Δ : Segment k) : IsCuspidal (cuspRep Δ).ρ := Δ.cusp.choose_spec.2

theorem nonempty_prod_equiv (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start)
    (e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d)) :
    Nonempty ((multiProd e (segTerm σ.ρ Δ.len)).Equiv
      (multiProd (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segTerm (cuspRep Δ).ρ Δ.len))) := by
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 (hσ.trans (cuspRep_cl Δ).symm)
  obtain ⟨ψ⟩ := (Placing.parInd_jac_placing k (Fin Δ.len) (Fin (Δ.len * Δ.d)) (fun _ => Fin Δ.d) e
    (GlobalTheory.Published.consecBlocks Δ.len Δ.d) _).1 (piTensor (segTerm (cuspRep Δ).ρ Δ.len))
  exact ⟨(GlobalTheory.LocGL.multiProdEquiv e (π := segTerm σ.ρ Δ.len) (σ := segTerm (cuspRep Δ).ρ Δ.len)
    fun a => GlobalTheory.LocGL.twistEquiv φ _).trans ψ⟩

theorem nonempty_piTensor_equiv (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start) :
    Nonempty ((piTensor (segTerm (cuspRep Δ).ρ Δ.len)).Equiv (piTensor (segTerm σ.ρ Δ.len))) := by
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 ((cuspRep_cl Δ).trans hσ.symm)
  exact ⟨GlobalTheory.LocGL.piTensorEquiv (ρ := segTerm (cuspRep Δ).ρ Δ.len) (σ := segTerm σ.ρ Δ.len)
    fun a => GlobalTheory.LocGL.twistEquiv φ _⟩

section Published

variable (h : GlobalTheory.Published.SegmentRepresentation)
include h

def segSub (Δ : Segment k) :
    Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segTerm (cuspRep Δ).ρ Δ.len)) :=
  (h k Δ.d Δ.len Δ.d_pos Δ.len_pos (cuspRep Δ) (cuspRep_isCuspidal Δ)).choose

theorem segSub_spec (Δ : Segment k) :
    (segSub h Δ).toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segTerm (cuspRep Δ).ρ Δ.len)),
        S'.toRepresentation.IsIrreducible → S' = segSub h Δ) ∧
      Nonempty ((jac (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segSub h Δ).toRepresentation).Equiv
        (piTensor (segTerm (cuspRep Δ).ρ Δ.len))) :=
  (h k Δ.d Δ.len Δ.d_pos Δ.len_pos (cuspRep Δ) (cuspRep_isCuspidal Δ)).choose_spec

def segIrr (Δ : Segment k) : IrrRep (GL (Fin (Δ.len * Δ.d)) k) where
  V := (segSub h Δ).toSubmodule
  ρ := (segSub h Δ).toRepresentation
  smooth := IsSubquotient.isSmooth ⟨segSub h Δ, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  irr := (segSub_spec h Δ).1

theorem embeds_iff (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start)
    (e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d)) (π : IrrRep (GL (Fin (Δ.len * Δ.d)) k)) :
    (∃ φ : π.ρ.IntertwiningMap (multiProd e (segTerm σ.ρ Δ.len)), Function.Injective φ) ↔
      Nonempty (π.ρ.Equiv (segIrr h Δ).ρ) := by
  obtain ⟨Φ⟩ := nonempty_prod_equiv Δ σ hσ e
  constructor
  · rintro ⟨φ, hφ⟩
    let f := Φ.toIntertwiningMap.comp φ
    have hf : Function.Injective f := Φ.toLinearEquiv.injective.comp hφ
    have hR : f.range.toRepresentation.IsIrreducible :=
      GlobalTheory.Parabolic.isIrreducible_of_equiv (rangeEquiv f hf) π.irr
    obtain ⟨ψ⟩ := nonempty_equiv_of_eq ((segSub_spec h Δ).2.1 _ hR)
    exact ⟨(rangeEquiv f hf).trans ψ⟩
  · rintro ⟨ψ⟩
    exact ⟨Φ.symm.toIntertwiningMap.comp ((subIncl (segSub h Δ)).comp ψ.toIntertwiningMap),
      Φ.symm.toLinearEquiv.injective.comp ((subIncl_injective _).comp ψ.toLinearEquiv.injective)⟩

theorem jac_iff (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start)
    (e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d)) (π : IrrRep (GL (Fin (Δ.len * Δ.d)) k)) :
    Nonempty ((jac e π.ρ).Equiv (piTensor (segTerm σ.ρ Δ.len))) ↔ Nonempty (π.ρ.Equiv (segIrr h Δ).ρ) := by
  constructor
  · rintro ⟨ψ⟩
    obtain ⟨f, hf⟩ := (Model.evalOne_bijective e π.smooth (piTensor (segTerm σ.ρ Δ.len))).2
      ψ.toIntertwiningMap
    refine (embeds_iff h Δ σ hσ e π).1 ⟨f, ?_⟩
    haveI := π.irr
    refine (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right fun h0 => ?_
    haveI : Nontrivial (⨂[ℂ] _ : Fin Δ.len, σ.V) :=
      GlobalTheory.ProdSupport.nontrivial_piTensor _ fun _ => Model.nontrivial_of_isIrreducible σ.irr
    obtain ⟨y, hy⟩ := exists_ne (0 : ⨂[ℂ] _ : Fin Δ.len, σ.V)
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (ψ.symm y)
    have h1 : ψ (Submodule.Quotient.mk v) = (f v).1.1 1 :=
      (congrArg (fun F => F (Submodule.Quotient.mk v)) hf).symm
    rw [h0, hv] at h1
    exact hy ((ψ.apply_symm_apply y).symm.trans h1)
  · rintro ⟨ψ⟩
    obtain ⟨A⟩ := (Placing.parInd_jac_placing k (Fin Δ.len) (Fin (Δ.len * Δ.d)) (fun _ => Fin Δ.d) e
      (GlobalTheory.Published.consecBlocks Δ.len Δ.d) _).2 (segSub h Δ).toRepresentation
    obtain ⟨B⟩ := (segSub_spec h Δ).2.2
    obtain ⟨C⟩ := nonempty_piTensor_equiv Δ σ hσ
    exact ⟨(Exponents.jacEquiv e ψ).trans (A.trans (B.trans C))⟩

theorem exists_isSegmentClass : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∃ Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k), IsSegmentClass k Z := by
  intro k _ _ _ _
  refine ⟨fun Δ => (segIrr h Δ).cl, fun Δ σ hσ e π => ⟨?_, ?_⟩⟩
  · rw [IrrRep.cl_eq_iff]; exact (embeds_iff h Δ σ hσ e π).symm
  · rw [IrrRep.cl_eq_iff]; exact (jac_iff h Δ σ hσ e π).symm

end Published

end GlobalTheory.SegmentClass

theorem GlobalTheory.segmentClass_exists : GlobalTheory.Published.SegmentRepresentation → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∃ Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k), IsSegmentClass k Z :=
  fun h => GlobalTheory.SegmentClass.exists_isSegmentClass h

end
end

