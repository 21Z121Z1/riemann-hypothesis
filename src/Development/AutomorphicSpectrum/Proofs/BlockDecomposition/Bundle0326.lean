import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriTraceOfBorelCasselman
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0318
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedTwoCharactersNotScalar
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SplitFrob

section Proj

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}

theorem isCompl_toSubmodule {S S' : Subrepresentation π} (h : IsCompl S S') :
    IsCompl S.toSubmodule S'.toSubmodule := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff, ← Subrepresentation.toSubmodule_inf, disjoint_iff.mp h.1]
    try rfl
  · rw [codisjoint_iff, ← Subrepresentation.toSubmodule_sup, codisjoint_iff.mp h.2]
    try rfl

def proj {S S' : Subrepresentation π} (h : IsCompl S S') : V →ₗ[ℂ] V :=
  S.toSubmodule.subtype ∘ₗ
    Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h)

theorem proj_left {S S' : Subrepresentation π} (h : IsCompl S S') {v : V} (hv : v ∈ S.toSubmodule) :
    proj h v = v := by
  show S.toSubmodule.subtype
    (Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h) v) = v
  simp only [Submodule.projectionOnto_apply_of_mem_left _ hv, Submodule.subtype_apply]

theorem proj_right {S S' : Subrepresentation π} (h : IsCompl S S') {v : V}
    (hv : v ∈ S'.toSubmodule) : proj h v = 0 := by
  show S.toSubmodule.subtype
    (Submodule.projectionOnto S.toSubmodule S'.toSubmodule (isCompl_toSubmodule h) v) = 0
  simp only [Submodule.projectionOnto_apply_of_mem_right _ hv, map_zero]

theorem proj_comm {S S' : Subrepresentation π} (h : IsCompl S S') (g : G) (v : V) :
    proj h (π g v) = π g (proj h v) := by
  have htop : S.toSubmodule ⊔ S'.toSubmodule = ⊤ := (isCompl_toSubmodule h).sup_eq_top
  have hv : v ∈ S.toSubmodule ⊔ S'.toSubmodule := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  simp only [map_add, proj_left h hx, proj_right h hy, proj_left h (S.apply_mem_toSubmodule g hx),
    proj_right h (S'.apply_mem_toSubmodule g hy), add_zero]

end Proj

section Induced

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {X : Type} [AddCommGroup X] [Module ℂ X]

def ev (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) : IndSp e ρ →ₗ[ℂ] X where
  toFun f := f.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ev_unip (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) {u : GL n k}
    (hu : u ∈ unipRad k e) (f : IndSp e ρ) : ev e ρ (parInd e ρ u f) = ev e ρ f := by
  obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hu
  rw [MonoidHom.mem_ker] at hp
  have h := f.1.2 p 1
  rw [MonoidHom.comp_apply, hp, map_one, Module.End.one_apply, mul_one] at h
  show f.1.1 (1 * ((parab k e).subtype p)) = f.1.1 1
  rw [one_mul]
  exact h

theorem ev_levi (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) (g : Levi k m)
    (f : IndSp e ρ) :
    ev e ρ (parInd e ρ (leviEmb k e g) f) = (deltaHalf k m g : ℂ) • ρ g (ev e ρ f) := by
  have hmem := leviEmb_mem_parab k e g
  have h := f.1.2 ⟨leviEmb k e g, hmem⟩ 1
  rw [mul_one, MonoidHom.comp_apply, leviProj_leviEmb] at h
  show f.1.1 (1 * leviEmb k e g) = (deltaHalf k m g : ℂ) • ρ g (f.1.1 1)
  rw [one_mul]
  exact h

theorem exists_ev_ne (e : (Σ a, m a) ≃ n) (ρ : Representation ℂ (Levi k m) X) {f : IndSp e ρ}
    (hf : f ≠ 0) : ∃ g, ev e ρ (parInd e ρ g f) ≠ 0 := by
  by_contra hcon
  apply hf
  apply Subtype.ext
  apply Subtype.ext
  funext g
  by_contra hg
  exact hcon ⟨g, by
    change f.1.1 (1 * g) ≠ 0
    rw [one_mul]
    exact hg⟩

variable {e : (Σ a, m a) ≃ n} {ρ : Representation ℂ (Levi k m) X}

def lam {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') : IndSp e ρ →ₗ[ℂ] X :=
  ev e ρ ∘ₗ proj h

theorem lam_apply {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (f : IndSp e ρ) :
    lam h f = ev e ρ (proj h f) := rfl

theorem lam_twKer {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') :
    twKer (parInd e ρ) (unipRad k e) 1 ≤ LinearMap.ker (lam h) := by
  unfold GlobalTheory.PRep.twKer
  refine Submodule.span_le.mpr ?_
  rintro w ⟨u, v, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, MonoidHom.one_apply, Units.val_one, one_smul,
    lam_apply, lam_apply, proj_comm, ev_unip e ρ u.2, sub_self]

def frob {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') :
    (jac e (parInd e ρ)).IntertwiningMap ρ where
  toLinearMap := (twKer (parInd e ρ) (unipRad k e) 1).liftQ (lam h) (lam_twKer h)
  isIntertwining' g := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show (twKer (parInd e ρ) (unipRad k e) 1).liftQ (lam h) (lam_twKer h)
        (jac e (parInd e ρ) g (Submodule.Quotient.mk v)) = ρ g (lam h v)
    rw [jac_mk, ← Submodule.Quotient.mk_smul, Submodule.liftQ_apply, map_smul, lam_apply, proj_comm,
      ev_levi, lam_apply, smul_smul]
    simp

theorem frob_mk {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (v : IndSp e ρ) :
    (frob h).toLinearMap (Submodule.Quotient.mk v) = lam h v := rfl

theorem exists_lam_ne {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (hS : S ≠ ⊥) :
    ∃ v ∈ S.toSubmodule, lam h v ≠ 0 := by
  have hS0 : S.toSubmodule ≠ ⊥ := by
    intro h0
    apply hS
    apply Subrepresentation.ext
    rw [h0]
    try rfl
  obtain ⟨f, hfS, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  obtain ⟨g, hg⟩ := exists_ev_ne e ρ hf0
  refine ⟨parInd e ρ g f, S.apply_mem_toSubmodule g hfS, ?_⟩
  rw [lam_apply, proj_left h (S.apply_mem_toSubmodule g hfS)]
  exact hg

theorem not_dichotomy {S S' : Subrepresentation (parInd e ρ)} (h : IsCompl S S') (hS : S ≠ ⊥)
    (hS' : S' ≠ ⊥) :
    ¬ (∀ φ ψ : (jac e (parInd e ρ)).IntertwiningMap ρ,
      φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro hd
  obtain ⟨v, hvS, hv⟩ := exists_lam_ne h hS
  obtain ⟨w, hwS', hw⟩ := exists_lam_ne h.symm hS'
  rcases hd (frob h) (frob h.symm) with h0 | ⟨c, hc⟩
  · apply hv
    rw [← frob_mk h v, h0, LinearMap.zero_apply]
  · have e1 : lam h.symm v = c • lam h v := by
      rw [← frob_mk h.symm v, hc, LinearMap.smul_apply, frob_mk]
    rw [lam_apply, proj_right h.symm hvS, map_zero] at e1
    rcases smul_eq_zero.mp e1.symm with hc0 | hc0
    · apply hw
      rw [← frob_mk h.symm w, hc, hc0, zero_smul, LinearMap.zero_apply]
    · exact hv hc0

end Induced

theorem not_dichotomy_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ) (W W' : Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))), IsCompl W W' → W ≠ ⊥ → W' ≠ ⊥ → ¬ (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ W W' h hW hW'
  exact not_dichotomy h hW hW'

end GlobalTheory.CompanionTheory.SplitFrob
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct ValuativeRel

namespace GlobalTheory.CompanionTheory.IwahoriDatumGL

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

theorem isClosed_entries (P : Fin n → Fin n → Prop) (c : Fin n → Fin n → k) :
    IsClosed {g : GL (Fin n) k | ∀ i j, P i j → g.val i j = c i j} := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have : {g : GL (Fin n) k | ∀ i j, P i j → g.val i j = c i j} =
      ⋂ i, ⋂ j, ⋂ _ : P i j, {g : GL (Fin n) k | g.val i j = c i j} := by
    ext g; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (Units.continuous_val.matrix_elem i j) continuous_const

theorem isClosed_unipB' : IsClosed (unipB k (Fin n) : Set (GL (Fin n) k)) := by
  convert isClosed_entries k n (fun i j => j ≤ i) (fun i j => (1 : Matrix (Fin n) (Fin n) k) i j) using 1
  ext g
  simp only [SetLike.mem_coe, mem_unipB, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases hij.lt_or_eq with h | rfl
    · rw [h1 i j h, one_apply_ne h.ne']
    · rw [h2, one_apply_eq]
  · intro h
    exact ⟨fun i j hij => by rw [h i j hij.le, one_apply_ne hij.ne'],
      fun i => by rw [h i i le_rfl, one_apply_eq]⟩

theorem isClosed_unipBLower' : IsClosed (unipBLower k (Fin n) : Set (GL (Fin n) k)) := by
  convert isClosed_entries k n (fun i j => i ≤ j) (fun i j => (1 : Matrix (Fin n) (Fin n) k) i j) using 1
  ext g
  simp only [SetLike.mem_coe, GlobalTheory.IwahoriTraceProof.mem_unipBLower, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases hij.lt_or_eq with h | rfl
    · rw [h1 i j h, one_apply_ne h.ne]
    · rw [h2, one_apply_eq]
  · intro h
    exact ⟨fun i j hij => by rw [h i j hij.le, one_apply_ne hij.ne],
      fun i => by rw [h i i le_rfl, one_apply_eq]⟩

theorem mem_range_diagT_iff (g : GL (Fin n) k) :
    g ∈ (diagT k (Fin n)).range ↔ ∀ i j, i ≠ j → g.val i j = 0 := by
  constructor
  · rintro ⟨t, rfl⟩ i j hij
    rw [val_diagT, diagonal_apply_ne _ hij]
  · intro h
    have hd : ∀ i, g.val i i ≠ 0 := by
      intro i hi
      have h1 : (g.val * (g⁻¹).val) i i = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_apply_eq]
      rw [Matrix.mul_apply, Finset.sum_eq_single i (fun j _ hj => by rw [h i j hj.symm, zero_mul])
        (by simp), hi, zero_mul] at h1
      exact zero_ne_one h1
    refine ⟨fun i => Units.mk0 _ (hd i), Units.ext ?_⟩
    rw [val_diagT]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [diagonal_apply_ne _ hij, h i j hij]

theorem isClosed_diagT : IsClosed ((diagT k (Fin n)).range : Set (GL (Fin n) k)) := by
  convert isClosed_entries k n (fun i j => i ≠ j) (fun _ _ => 0) using 1
  ext g
  exact mem_range_diagT_iff k n g

theorem fact_up' {x : GL (Fin n) k} (hx : x ∈ iwahori k (Fin n)) :
    ∃ c ∈ iwahori k (Fin n) ⊓ unipB k (Fin n), ∃ b ∈ iwahori k (Fin n) ⊓ (diagT k (Fin n)).range,
      ∃ a ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n), x = c * b * a := by
  obtain ⟨u, hu, d, hd, c, hc, rfl⟩ := GlobalTheory.IwahoriTraceProof.iwahori_factorisation hx
  exact ⟨u, ⟨(GlobalTheory.IwahoriTraceProof.mem_unipO_iff hu.1).2 hu, hu.1⟩, _,
    ⟨diagT_mem_iwahori hd, ⟨d, rfl⟩⟩, c, ⟨KOne_le_iwahori k (Fin n) hc.2, hc.1⟩, rfl⟩

theorem fact_low' {x : GL (Fin n) k} (hx : x ∈ iwahori k (Fin n)) :
    ∃ a ∈ iwahori k (Fin n) ⊓ unipBLower k (Fin n), ∃ b ∈ iwahori k (Fin n) ⊓ (diagT k (Fin n)).range,
      ∃ c ∈ iwahori k (Fin n) ⊓ unipB k (Fin n), x = a * b * c := by
  obtain ⟨c, hc, b, hb, a, ha, e⟩ := fact_up' k n (inv_mem hx)
  refine ⟨a⁻¹, inv_mem ha, b⁻¹, inv_mem hb, c⁻¹, inv_mem hc, ?_⟩
  rw [← _root_.inv_inj, e]
  group

def iwahoriCass : CassData (GL (Fin n) k) where
  N := unipB k (Fin n)
  Nm := unipBLower k (Fin n)
  T := (diagT k (Fin n)).range
  J := iwahori k (Fin n)
  isOpen_J := IwahoriOnto.isOpen_iwahori k (Fin n)
  isCompact_J := IwahoriOnto.isCompact_iwahori k (Fin n)
  isClosed_N := isClosed_unipB' k n
  isClosed_Nm := isClosed_unipBLower' k n
  isClosed_alt := isClosed_diagT k n
  norm_N := by
    rintro _ ⟨t, rfl⟩
    exact leviEmb_mem_normalizer k (points (Fin n)) _
  norm_Nm := by
    rintro _ ⟨t, rfl⟩
    exact leviEmb_mem_normalizer_lower k (points (Fin n)) _
  fact_low _ hx := fact_low' k n hx
  fact_up _ hx := fact_up' k n hx

theorem iwahoriGL : PositivityTheory.SphericalProduct.IwahoriGL := fun k _ _ _ _ n =>
  ⟨iwahoriCass k n, rfl, rfl, rfl, rfl⟩

end GlobalTheory.CompanionTheory.IwahoriDatumGL

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerSCShortExact
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.CompanionTheory.GE.KerSeq

variable {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}

abbrev sumN (M : ℕ → X.Modules) (k d e : ℕ) : X.Modules := ⨁ fun _ : Fin k => M (d + e)

def sumMap (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : sumN M k d e ⟶ M (d + e + 1) :=
  biproduct.desc fun i => T i (d + e)

def diagOp (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    sumN M k d e ⟶ sumN M k d (e + 1) :=
  biproduct.map fun _ => T j (d + e)

abbrev kerSeq (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : X.Modules := kernel (sumMap T d e)

theorem diagOp_sumMap (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    diagOp T d j e ≫ sumMap T d (e + 1) = sumMap T d e ≫ T j (d + e + 1) := by
  apply biproduct.hom_ext'
  intro i
  simp only [diagOp, sumMap, biproduct.ι_map_assoc, biproduct.ι_desc, biproduct.ι_desc_assoc]
  exact hc j i (d + e)

def kerOp (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    kerSeq T d e ⟶ kerSeq T d (e + 1) :=
  kernel.lift _ (kernel.ι _ ≫ diagOp T d j e) (by
    rw [Category.assoc, diagOp_sumMap T hc, kernel.condition_assoc, zero_comp])

@[reassoc (attr := simp)]
theorem kerOp_ι (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (j : Fin k) (e : ℕ) :
    kerOp T hc d j e ≫ kernel.ι _ = kernel.ι _ ≫ diagOp T d j e :=
  kernel.lift_ι _ _ _

theorem diagOp_comm (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (i j : Fin k) (e : ℕ) :
    diagOp T d i e ≫ diagOp T d j (e + 1) = diagOp T d j e ≫ diagOp T d i (e + 1) := by
  apply biproduct.hom_ext
  intro l
  simp only [diagOp, Category.assoc, biproduct.map_π, biproduct.map_π_assoc]
  exact biproduct.π _ l ≫= hc i j (d + e)

theorem kerOp_comm (T : Fin k → ∀ e, M e ⟶ M (e + 1))
    (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (d : ℕ) (i j : Fin k) (e : ℕ) :
    kerOp T hc d i e ≫ kerOp T hc d j (e + 1) = kerOp T hc d j e ≫ kerOp T hc d i (e + 1) := by
  rw [← cancel_mono (kernel.ι _)]
  simp only [Category.assoc, kerOp_ι, kerOp_ι_assoc]
  rw [diagOp_comm T hc]

def kerSC (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (kernel.ι (sumMap T d e)) (sumMap T d e) (kernel.condition _)

theorem kerSC_shortExact (T : Fin k → ∀ e, M e ⟶ M (e + 1)) (d e : ℕ) [Epi (sumMap T d e)] :
    (kerSC T d e).ShortExact where
  exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  mono_f := by dsimp [kerSC]; infer_instance
  epi_g := by dsimp [kerSC]; infer_instance

end GlobalTheory.CompanionTheory.GE.KerSeq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethIsoProperSmooth
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue

variable {K : Type} [Field K]

def topResEquiv (hT : TopRes) {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C)
    (hU : ∀ T, U T) (n : ℕ) : CH.H F n ≃ₗ[K] CH.H (U.ι ⋙ F) n :=
  LinearEquiv.ofBijective ((CH.Mor.restrict F U.ι).pull n)
    (CrystallineSemistableComparison.P.mapH_bij (CH.Mor.restrict F U.ι).hom (fun m => (hT K C F U ⊥ hU m).1) n)

theorem cls_congr' {R : Type} [CommRing R] {L : Cx.{1} R} {n : ℕ} {x y : L.X n} (e : x = y) (hx : L.d n x = 0)
    (hy : L.d n y = 0) : L.cls x hx = L.cls y hy := by
  subst e
  rfl

theorem XD.pr_restrict (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) {a a' c p q n : ℕ} (ha : a + a' = c)
    (h : p + q = n) (x : CH.Cn (E.F₁ a) p) (y : CH.Cn (E.F₂ a') q) :
    (E.pr U₁ U₂ U₃ h₁ h₂ ha).μ h ((CH.Mor.restrict (E.F₁ a) U₁.ι).pullC p x)
        ((CH.Mor.restrict (E.F₂ a') U₂.ι).pullC q y) =
      (CH.Mor.restrict (E.F₃ c) U₃.ι).pullC n
        ((E.μ ha).cupC h ((E.m₁ a).pullC p x) ((E.m₂ a').pullC q y)) := by
  funext s
  rfl

theorem XD.kun_cup (hT : TopRes) (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂)
    (U₃ : ObjectProperty E.D) (hU₁ : ∀ T, U₁ T) (hU₂ : ∀ T, U₂ T) (hU₃ : ∀ T, U₃ T)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) {c n : ℕ}
    (e : (⨁ t : Idx c n, (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) ≃ₗ[K]
      (CH.cx (U₃.ι ⋙ E.F₃ c)).H n)
    (he : ∀ (t : Idx c n) (x : (CH.cx (U₁.ι ⋙ E.F₁ t.a)).X t.i) (y : (CH.cx (U₂.ι ⋙ E.F₂ t.a')).X t.j)
      (hx : (CH.cx (U₁.ι ⋙ E.F₁ t.a)).d t.i x = 0) (hy : (CH.cx (U₂.ι ⋙ E.F₂ t.a')).d t.j y = 0)
      (hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d n ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h x y) = 0),
      e (DirectSum.lof K _ (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) t
        ((CH.cx (U₁.ι ⋙ E.F₁ t.a)).cls x hx ⊗ₜ (CH.cx (U₂.ι ⋙ E.F₂ t.a')).cls y hy)) =
        (CH.cx (U₃.ι ⋙ E.F₃ c)).cls ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h x y) hz)
    (t : Idx c n) (u : CH.H (E.F₁ t.a) t.i) (v : CH.H (E.F₂ t.a') t.j) :
    topResEquiv hT (E.F₃ c) U₃ hU₃ n
        ((E.μ t.ha).cup t.h ((E.m₁ t.a).pull t.i u) ((E.m₂ t.a').pull t.j v)) =
      e (DirectSum.lof K _ (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j) t
        (topResEquiv hT (E.F₁ t.a) U₁ hU₁ t.i u ⊗ₜ topResEquiv hT (E.F₂ t.a') U₂ hU₂ t.j v)) := by
  obtain ⟨x, hx, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj u
  obtain ⟨y, hy, rfl⟩ := CrystallineSemistableComparison.CechClassBoundaries.clsSurj v
  have hx₁ := CrystallineSemistableComparison.CechClassBoundaries.cyc (E.m₁ t.a).hom x hx
  have hy₁ := CrystallineSemistableComparison.CechClassBoundaries.cyc (E.m₂ t.a').hom y hy
  obtain ⟨hc, ec⟩ := CrystallineSemistableComparison.P.cup_cls (E.μ t.ha) t.h _ _ hx₁ hy₁
  have hx₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₁ t.a) U₁.ι).hom x hx
  have hy₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₂ t.a') U₂.ι).hom y hy
  have hc₂ := CrystallineSemistableComparison.CechClassBoundaries.cyc (CH.Mor.restrict (E.F₃ c) U₃.ι).hom _ hc
  have hz : (CH.cx (U₃.ι ⋙ E.F₃ c)).d n ((E.pr U₁ U₂ U₃ h₁ h₂ t.ha).μ t.h
      ((CH.Mor.restrict (E.F₁ t.a) U₁.ι).pullC t.i x) ((CH.Mor.restrict (E.F₂ t.a') U₂.ι).pullC t.j y)) = 0 := by
    rw [XD.pr_restrict]
    exact hc₂
  have key := he t _ _ hx₂ hy₂ hz
  refine Eq.trans ?_ key.symm |>.trans rfl
  change (CH.Mor.restrict (E.F₃ c) U₃.ι).pull n ((E.μ t.ha).cup t.h ((CH.cx _).cls _ hx₁) ((CH.cx _).cls _ hy₁)) = _
  rw [ec]
  exact cls_congr' (XD.pr_restrict E U₁ U₂ U₃ h₁ h₂ t.ha t.h x y).symm hc₂ hz

def sliceMap {A₀ B₀ A B : Type*} [AddCommGroup A₀] [Module K A₀] [AddCommGroup B₀] [Module K B₀] [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] (r₁ : A₀ ≃ₗ[K] A) (r₂ : B₀ ≃ₗ[K] B) (φ : Module.Dual K A₀) :
    A ⊗[K] B →ₗ[K] B₀ :=
  (TensorProduct.lid K B₀).toLinearMap ∘ₗ TensorProduct.map (φ ∘ₗ r₁.symm.toLinearMap) r₂.symm.toLinearMap

theorem sliceMap_tmul {A₀ B₀ A B : Type*} [AddCommGroup A₀] [Module K A₀] [AddCommGroup B₀] [Module K B₀] [AddCommGroup A]
    [Module K A] [AddCommGroup B] [Module K B] (r₁ : A₀ ≃ₗ[K] A) (r₂ : B₀ ≃ₗ[K] B) (φ : Module.Dual K A₀) (u : A₀) (v : B₀) :
    sliceMap r₁ r₂ φ (r₁ u ⊗ₜ r₂ v) = φ u • v := by
  simp [sliceMap]

def compMap {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) : A →ₗ[K] W :=
  g ∘ₗ DirectSum.component K ι N t₀ ∘ₗ e.symm.toLinearMap ∘ₗ ρ.toLinearMap

theorem compMap_self {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) (x : A) (w : N t₀)
    (hx : ρ x = e (DirectSum.lof K ι N t₀ w)) : compMap N ρ e t₀ g x = g w := by
  simp only [compMap, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, LinearEquiv.symm_apply_apply]
  rw [DirectSum.component.lof_self]

theorem compMap_ne {ι : Type*} [DecidableEq ι] (N : ι → Type*) [∀ t, AddCommGroup (N t)] [∀ t, Module K (N t)]
    {A T W : Type*} [AddCommGroup A] [Module K A] [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (ρ : A ≃ₗ[K] T) (e : (⨁ t, N t) ≃ₗ[K] T) (t₀ : ι) (g : N t₀ →ₗ[K] W) (x : A) (t : ι) (w : N t) (ht : t ≠ t₀)
    (hx : ρ x = e (DirectSum.lof K ι N t w)) : compMap N ρ e t₀ g x = 0 := by
  simp only [compMap, LinearMap.comp_apply, LinearEquiv.coe_coe, hx, LinearEquiv.symm_apply_apply]
  rw [DirectSum.component.of, dif_neg ht, map_zero]

theorem XD.slant (hT : TopRes) (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂)
    (U₃ : ObjectProperty E.D) (hU₁ : ∀ T, U₁ T) (hU₂ : ∀ T, U₂ T) (hU₃ : ∀ T, U₃ T)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (hK : E.Kun U₁ U₂ U₃ h₁ h₂)
    (a i a' j c n : ℕ) (ha : a + a' = c) (h : i + j = n) (φ : Module.Dual K (CH.H (E.F₁ a) i)) :
    ∃ sl : CH.H (E.F₃ c) n →ₗ[K] CH.H (E.F₂ a') j,
      (∀ u v, sl ((E.μ ha).cup h ((E.m₁ a).pull i u) ((E.m₂ a').pull j v)) = φ u • v) ∧
      ∀ (b i' b' j' : ℕ) (hb : b + b' = c) (h' : i' + j' = n), (b, i') ≠ (a, i) →
        ∀ (u : CH.H (E.F₁ b) i') (v : CH.H (E.F₂ b') j'),
          sl ((E.μ hb).cup h' ((E.m₁ b).pull i' u) ((E.m₂ b').pull j' v)) = 0 := by
  obtain ⟨e, he⟩ := hK c n
  have kc := XD.kun_cup hT E U₁ U₂ U₃ hU₁ hU₂ hU₃ h₁ h₂ e he
  refine ⟨compMap (fun t : Idx c n => (CH.cx (U₁.ι ⋙ E.F₁ t.a)).H t.i ⊗[K] (CH.cx (U₂.ι ⋙ E.F₂ t.a')).H t.j)
    (topResEquiv hT (E.F₃ c) U₃ hU₃ n) e ⟨a, i, a', j, ha, h⟩
    (sliceMap (topResEquiv hT (E.F₁ a) U₁ hU₁ i) (topResEquiv hT (E.F₂ a') U₂ hU₂ j) φ), ?_, ?_⟩
  · intro u v
    exact (compMap_self _ _ e _ _ _ _ (kc ⟨a, i, a', j, ha, h⟩ u v)).trans (sliceMap_tmul _ _ φ u v)
  · intro b i' b' j' hb h' hne u v
    refine compMap_ne _ _ e _ _ _ ⟨b, i', b', j', hb, h'⟩ _ ?_ (kc ⟨b, i', b', j', hb, h'⟩ u v)
    intro hh
    exact hne (by rw [show b = a from congrArg Idx.a hh, show i' = i from congrArg Idx.i hh])

theorem slant_of_kun : TopRes → SiteLaws → (∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂) → Slant := by
  intro hT hS hK K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP a i a' j c n ha h φ
  have top₁ : ∀ T, inU q ⊤ T := fun T => (hS K X X X q (𝟙 X) (𝟙 X)).2.2.1 T
  have top₂ : ∀ T, inU q' ⊤ T := fun T => (hS K X' X' X' q' (𝟙 X') (𝟙 X')).2.2.1 T
  have topP : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T := by
    have e : p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤ = ⊤ := by simp
    rw [e]
    exact fun T => (hS K P P P (p₁ ≫ q) (𝟙 P) (𝟙 P)).2.2.1 T
  have h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T) :=
    fun T _ => top₁ _
  have h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T) :=
    fun T _ => top₂ _
  exact XD.slant hT (hodgeXD q q' p₁ p₂ hP.w.symm) (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤))
    top₁ top₂ topP h₁ h₂ (hK K X X' P q q' p₁ p₂ hP h₁ h₂) a i a' j c n ha h φ

end GlobalTheory.CompanionTheory.KunGlue
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBAlgebraMapFieldStatement
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_toB_algebraMap_field : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (a : K) (y : (per l K).P), (y : (per l K).B) = (per l K).o a → (lev h k).toB y = algebraMap K (lev h k).B a := by
  first | exact @GlobalTheory.CompanionTheory.LatC.toB_on_K | exact GlobalTheory.CompanionTheory.LatC.toB_on_K | (intros; apply GlobalTheory.CompanionTheory.LatC.toB_on_K <;> assumption)
end

