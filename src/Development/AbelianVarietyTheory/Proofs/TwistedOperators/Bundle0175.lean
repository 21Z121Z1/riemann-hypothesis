import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
section
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.IwahoriInj ValuativeRel

namespace GlobalTheory.JacInj

section Abstract

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π₁ : Representation ℂ G V} {π : Representation ℂ G W}

theorem map_apply' (f : π₁.IntertwiningMap π) (g : G) (v : V) : f (π₁ g v) = π g (f v) := by
  have h := LinearMap.congr_fun (f.isIntertwining' g) v
  simpa using h

theorem map_mem_twKer (f : π₁.IntertwiningMap π) {H : Subgroup G} {v : V} (hv : v ∈ twKer π₁ H 1) :
    f v ∈ twKer π H 1 := by
  have hle : twKer π₁ H 1 ≤ (twKer π H 1).comap f.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, w, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, map_sub, map_smul]
    refine Submodule.subset_span ⟨h, f w, ?_⟩
    simp [map_apply']
  exact hle hv

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem mem_twKer_of_map (f : π₁.IntertwiningMap π) (hπ : IsSmooth π) (hf : Function.Injective f)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) {v : V} (hv : f v ∈ twKer π H 1) :
    v ∈ twKer π₁ H 1 := by
  have h₁ : IsSmooth π₁ := by
    intro w
    have hset : {g : G | π₁ g w = w} = {g : G | π g (f w) = f w} := by
      ext g
      simp only [Set.mem_ofPred_eq, ← map_apply' f g w]
      exact hf.eq_iff.symm
    rw [hset]
    exact hπ (f w)
  obtain ⟨U, -, hU, hUv⟩ := GlobalTheory.LocGL.exists_normal_fix h₁ hH v
  letI : Fintype (H ⧸ U) := U.fintypeQuotientOfFiniteIndex
  have hUf : ∀ u ∈ U, π (u : H) (f v) = f v := fun u hu => by rw [← map_apply', hUv u hu]
  rw [← GlobalTheory.LocGL.idem_eq_zero_iff h₁ hH]
  apply hf
  rw [map_zero, GlobalTheory.LocGL.idem_eq_cosetSum h₁ hH U hUv, map_smul, map_sum]
  simp only [map_apply']
  rw [← GlobalTheory.LocGL.idem_eq_cosetSum hπ hH U hUf]
  exact (GlobalTheory.LocGL.idem_eq_zero_iff hπ hH).2 hv

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

def wt (e : (Σ a, m a) ≃ n) (M : ℕ) (i j : n) : ℤ :=
  M * (((Finset.univ.filter (· < blk e i)).card : ℤ) - (Finset.univ.filter (· < blk e j)).card)

theorem conc_wt (e : (Σ a, m a) ≃ n) (M : ℕ) : Conc (wt e M) := by
  unfold GlobalTheory.IwahoriInj.Conc
  refine ⟨fun i => by simp [wt], fun i j l => le_of_eq ?_⟩
  simp only [wt]
  ring

private theorem eventually_valuation_le_uniformizer_pow_of_mem_unipRad (e : (Σ a, m a) ≃ n) {g : GL n k} (hg : g ∈ unipRad k e) (i j : n) :
    ∀ᶠ M : ℕ in Filter.atTop, valuation k ((g : Matrix n n k) i j) ≤ uniformizer k ^ wt e M i j := by
  obtain ⟨hP, hD⟩ := mem_unipRad.1 hg
  rw [mem_parab] at hP
  have hmono : ∀ a b : ℤ, a ≤ b → uniformizer k ^ b ≤ uniformizer k ^ a := by
    intro a b hab
    exact zpow_le_zpow_right_of_le_one₀ uniformizer_pos uniformizer_lt_one.le hab
  rcases lt_trichotomy (blk e i) (blk e j) with h | h | h
  ·
    obtain ⟨N, hN⟩ := MulArchimedean.arch (valuation k ((g : Matrix n n k) i j))
      ((one_lt_inv₀ uniformizer_pos).2 uniformizer_lt_one)
    have hss : Finset.univ.filter (· < blk e i) ⊂ Finset.univ.filter (· < blk e j) := by
      refine (Finset.ssubset_iff_of_subset (fun x hx => ?_)).2 ⟨blk e i, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact hx.trans h
      · simp [h]
      · simp
    have hlt := Finset.card_lt_card hss
    filter_upwards [Filter.eventually_ge_atTop N] with M hM
    have hM' : (N : ℤ) ≤ M := by exact_mod_cast hM
    have hd : ((Finset.univ.filter (· < blk e i)).card : ℤ) -
        (Finset.univ.filter (· < blk e j)).card ≤ -1 := by omega
    have hw : wt e M i j ≤ -(N : ℤ) := by
      simp only [wt]
      nlinarith
    refine hN.trans (le_trans (le_of_eq ?_) (hmono _ _ hw))
    rw [zpow_neg, zpow_natCast, inv_pow]
  ·
    refine Filter.Eventually.of_forall fun M => ?_
    have hw : wt e M i j = 0 := by simp [wt, h]
    rw [hw, zpow_zero]
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at h
    cases h
    rw [hD _ i' j', Matrix.one_apply]
    split_ifs <;> simp
  ·
    exact Filter.Eventually.of_forall fun M => by
      rw [hP i j h, map_zero]
      exact zero_le'

theorem eventually_mem_grp (e : (Σ a, m a) ≃ n) {u : GL n k} (hu : u ∈ unipRad k e) :
    ∀ᶠ M : ℕ in Filter.atTop, u ∈ grp k (conc_wt e M) := by
  unfold GlobalTheory.IwahoriInj.grp
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  unfold GlobalTheory.IwahoriInj.Deep
  have hu' : u⁻¹ ∈ unipRad k e := inv_mem hu
  exact (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_uniformizer_pow_of_mem_unipRad e hu i j).and
    (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_valuation_le_uniformizer_pow_of_mem_unipRad e hu' i j)

private theorem t2Space_localField : T2Space k := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  refine ⟨{y | valuation k y < valuation k x}, ?_, fun h => lt_irrefl (valuation k x) (by simpa using h)⟩
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  exact ⟨Units.mk0 _ ((valuation k).ne_zero_iff.2 hx), fun y hy => by simpa using hy⟩

theorem isClosed_unipRad (e : (Σ a, m a) ≃ n) : IsClosed (unipRad k e : Set (GL n k)) := by
  have : T2Space k := t2Space_localField
  have hv : Continuous fun g : GL n k => (g : Matrix n n k) := Units.continuous_val
  have hc : ∀ i j, Continuous fun g : GL n k => (g : Matrix n n k) i j := fun i j => hv.matrix_elem i j
  have hset : (unipRad k e : Set (GL n k)) =
      {g : GL n k | ∀ i j, blk e j < blk e i → (g : Matrix n n k) i j = 0} ∩
        {g : GL n k | ∀ a (i j : m a), (g : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) = (1 : Matrix (m a) (m a) k) i j} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipRad, mem_parab, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [hset]
  refine IsClosed.inter ?_ ?_
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (hc i j) continuous_const
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (hc _ _) continuous_const

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem eventually_mem_twKer_inf (e : (Σ a, m a) ≃ n) {π : Representation ℂ (GL n k) V} {v : V}
    (hv : v ∈ twKer π (unipRad k e) 1) :
    ∀ᶠ M : ℕ in Filter.atTop, v ∈ twKer π (grp k (conc_wt e M) ⊓ unipRad k e) 1 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, w, rfl⟩ := hx
    filter_upwards [eventually_mem_grp e u.2] with M hM
    exact Submodule.subset_span ⟨⟨u, hM, u.2⟩, w, rfl⟩
  | zero => exact Filter.Eventually.of_forall fun _ => Submodule.zero_mem _
  | add x y _ _ hx hy =>
    filter_upwards [hx, hy] with M h₁ h₂
    exact Submodule.add_mem _ h₁ h₂
  | smul c x _ hx =>
    filter_upwards [hx] with M h
    exact Submodule.smul_mem _ c h

private theorem twKer_one_mono' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} {H K : Subgroup G} (hHK : H ≤ K) : twKer ρ H 1 ≤ twKer ρ K 1 := by
  refine Submodule.span_mono ?_
  rintro _ ⟨h, w, rfl⟩
  exact ⟨⟨h, hHK h.2⟩, w, rfl⟩

theorem jacMap_injective (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (α n : Type) (m : α → Type) [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL n k) V) (π : Representation ℂ (GL n k) W)
    (f : π₁.IntertwiningMap π) (hπ : IsSmooth π) (hf : Function.Injective f) :
    Function.Injective (jacMap e f) := by
  intro x y hxy
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hmk : ∀ u : V, jacMap e f (Submodule.Quotient.mk u) = Submodule.Quotient.mk (f u) :=
    fun _ => rfl
  rw [hmk, hmk, Submodule.Quotient.eq, ← map_sub] at hxy
  rw [Submodule.Quotient.eq]
  obtain ⟨M, hM⟩ := (eventually_mem_twKer_inf e hxy).exists
  have hcpt : IsCompact ((grp k (conc_wt e M) ⊓ unipRad k e : Subgroup (GL n k)) : Set (GL n k)) := by
    rw [Subgroup.coe_inf]
    exact (isCompact_grp (conc_wt e M)).inter_right (isClosed_unipRad e)
  exact twKer_one_mono' inf_le_right (mem_twKer_of_map f hπ hf hcpt hM)

end GlobalTheory.JacInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
section
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents ValuativeRel Matrix

namespace GlobalTheory.SmGL.EmptyBlocks

section General

variable {F G H V W : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem jhMult_comp_surjective (φ : H →* G) (hφ : Function.Surjective φ) (σ : Representation F G W)
    (ρ : Representation F G V) :
    jhMult (σ.comp φ : Representation F H W) (ρ.comp φ : Representation F H V) = jhMult σ ρ := by
  have : ∀ r, OccursTimes (σ.comp φ : Representation F H W) (ρ.comp φ : Representation F H V) r ↔
      OccursTimes σ ρ r := fun r => by
    constructor
    · rintro ⟨S, T, h1, h2, h3⟩
      let up : Subrepresentation (ρ.comp φ : Representation F H V) → Subrepresentation ρ := fun S =>
        ⟨S.toSubmodule, fun g v hv => by
          obtain ⟨h, rfl⟩ := hφ g
          exact S.apply_mem_toSubmodule h hv⟩
      refine ⟨fun i => up (S i), fun i => up (T i), h1, h2, fun i => (h3 i).map fun ψ =>
        .mk ψ.toLinearEquiv fun g => ?_⟩
      obtain ⟨h, rfl⟩ := hφ g
      exact ψ.isIntertwining' h
    · rintro ⟨S, T, h1, h2, h3⟩
      let down : Subrepresentation ρ → Subrepresentation (ρ.comp φ : Representation F H V) := fun S =>
        ⟨S.toSubmodule, fun h v hv => S.apply_mem_toSubmodule (φ h) hv⟩
      exact ⟨fun i => down (S i), fun i => down (T i), h1, h2, fun i => (h3 i).map fun ψ =>
        .mk ψ.toLinearEquiv fun h => ψ.isIntertwining' (φ h)⟩
  simp only [jhMult, this]

end General

section Blocks

variable (R : Type) [CommRing R] {β n : Type} [Fintype β] [LinearOrder β] [Fintype n] [DecidableEq n]
  {c : β → Type} [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)] (f : (Σ j, c j) ≃ n)

def torusToLevi : (n → Rˣ) →* Levi R c :=
  (leviProj R f).comp ((diagT R n).codRestrict (parab R f) fun t => mem_parab.2 fun i j h => by
    rw [val_diagT, diagonal_apply_ne]
    rintro rfl
    exact lt_irrefl _ h)

theorem val_torusToLevi (t : n → Rˣ) (j : β) :
    (torusToLevi R f t j : Matrix (c j) (c j) R) = diagonal fun x => (t (f ⟨j, x⟩) : R) := by
  ext x y
  show (diagT R n t : Matrix n n R) (f ⟨j, x⟩) (f ⟨j, y⟩) = _
  rw [val_diagT]
  simp [diagonal_apply]

theorem leviEmb_torusToLevi (t : n → Rˣ) : leviEmb R f (torusToLevi R f t) = diagT R n t := by
  ext i j
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective j
  by_cases h : a = b
  · subst h
    rw [leviEmb_apply_same]
    rfl
  · rw [leviEmb_apply_ne R f _ h, val_diagT, diagonal_apply_ne]
    intro h'
    exact h (congrArg Sigma.fst (f.injective h'))

theorem det_torusToLevi (t : n → Rˣ) (j : β) :
    GeneralLinearGroup.det (torusToLevi R f t j) = ∏ x, t (f ⟨j, x⟩) := by
  ext
  simp [val_torusToLevi]

theorem prod_det_torusToLevi (χ : β → Rˣ →* ℂˣ) (t : n → Rˣ) :
    ∏ j, χ j (GeneralLinearGroup.det (torusToLevi R f t j)) = ∏ i, χ (blk f i) (t i) := by
  rw [← f.prod_comp, Fintype.prod_sigma]
  simp [det_torusToLevi]

theorem torusToLevi_surjective (hf : Function.Injective (blk f)) :
    Function.Surjective (torusToLevi R f) := by
  intro g
  refine ⟨fun i => GeneralLinearGroup.det (g (blk f i)), funext fun j => ?_⟩
  ext x y
  have hs : ∀ u v : c j, u = v := fun u v => by
    have : f ⟨j, u⟩ = f ⟨j, v⟩ := hf (by simp)
    simpa using this
  obtain rfl := hs x y
  haveI : Unique (c j) := ⟨⟨x⟩, fun u => hs _ _⟩
  rw [val_torusToLevi, diagonal_apply_eq, blk_apply, GeneralLinearGroup.val_det_apply,
    det_unique, hs default x]

omit [LinearOrder β] [DecidableEq n] [∀ j, DecidableEq (c j)] in

theorem sum_card_blocks (P : β → Prop) [DecidablePred P] :
    ∑ b with P b, (Fintype.card (c b) : ℤ) = ∑ i with P (blk f i), (1 : ℤ) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← f.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [blk_apply]
  split_ifs <;> simp

variable [LinearOrder n]

omit [DecidableEq n] [∀ j, DecidableEq (c j)] in

theorem modExp_blk (hf : StrictMono (blk f)) (i : n) :
    modExp c (blk f i) = modExp (fun _ : n => Unit) i := by
  unfold modExp
  rw [sum_card_blocks f, sum_card_blocks f]
  simp [hf.lt_iff_lt]

theorem unipRad_eq (hf : StrictMono (blk f)) : unipRad R f = unipB R n := by
  ext g
  rw [mem_unipRad, mem_unipB, mem_parab]
  simp only [hf.lt_iff_lt]
  refine and_congr Iff.rfl ⟨fun h i => ?_, fun h a x y => ?_⟩
  · obtain ⟨⟨a, x⟩, rfl⟩ := f.surjective i
    simpa using h a x x
  · have : f ⟨a, x⟩ = f ⟨a, y⟩ := hf.injective (by simp)
    obtain rfl : x = y := by simpa using this
    simpa using h _

end Blocks

theorem jhMult_jac_eq_jacB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (β n : Type) [Fintype β] [LinearOrder β] [Fintype n]
    [DecidableEq n] [LinearOrder n] (c : β → Type) [∀ j, Fintype (c j)] [∀ j, DecidableEq (c j)]
    (f : (Σ j, c j) ≃ n) (hf : StrictMono (blk f)) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL n k) V) (χ : β → kˣ →* ℂˣ) :
    jhMult (ofChar (leviChar c χ)) (jac f π) =
      jhMult (ofChar (torusChar fun i => χ (blk f i))) (jacB π) := by
  have h1 : ((ofChar (leviChar c χ)).comp (torusToLevi k f) : Representation ℂ (n → kˣ) ℂ) =
      ofChar (torusChar fun i => χ (blk f i)) := by
    refine MonoidHom.ext fun t => LinearMap.ext fun y => ?_
    show ofChar _ _ y = _
    rw [ofChar_apply, ofChar_apply, leviChar_apply, torusChar_apply, prod_det_torusToLevi]
  have h2 : ∀ t, deltaHalf k c (torusToLevi k f t) =
      deltaHalf k (fun _ : n => Unit) (leviTorus k n t) := fun t => by
    have hd : ∀ i, GeneralLinearGroup.det (leviTorus k n t i) = t i :=
      congrFun ((leviTorus k n).left_inv t)
    rw [deltaHalf_apply, deltaHalf_apply,
      prod_det_torusToLevi k f fun a => absPow k ((modExp c a : ℂ) / 2)]
    simp only [hd, modExp_blk f hf]
  have h3 : twKer π (unipRad k f) 1 = twKer π (unipB k n) 1 := by rw [unipRad_eq k f hf]
  rw [← jhMult_comp_surjective (torusToLevi k f) (torusToLevi_surjective k f hf.injective), h1]
  refine jhMult_congr_right _ (.mk (Submodule.quotEquivOfEq _ _ h3) fun t => ?_)
  refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
  show Submodule.quotEquivOfEq _ _ h3 (jac f π (torusToLevi k f t) (Submodule.Quotient.mk v)) =
    jac (points n) π (leviTorus k n t) (Submodule.Quotient.mk v)
  rw [jac_mk, jac_mk, map_smul, h2, leviEmb_torusToLevi]
  rfl

end GlobalTheory.SmGL.EmptyBlocks
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
section
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.SmGL.UnramFixed

theorem occursTimes_of_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ τ : Representation ℂ G V} {δ θ η : G →* ℂˣ} (h : ∀ g v, τ g v = (δ g : ℂ) • ρ g v)
    (hη : ∀ g, η g = θ g * δ g) {r : ℕ} (hr : OccursTimes (ofChar θ) ρ r) :
    OccursTimes (ofChar η) τ r := by
  obtain ⟨S, T, h1, h2, h3⟩ := hr
  have hst : ∀ (P : Subrepresentation ρ) (g : G) (v : V), v ∈ P.toSubmodule → τ g v ∈ P.toSubmodule :=
    fun P g v hv => by
      rw [h]
      exact P.toSubmodule.smul_mem _ (P.apply_mem_toSubmodule g hv)
  refine ⟨fun i => ⟨(S i).toSubmodule, hst (S i)⟩, fun i => ⟨(T i).toSubmodule, hst (T i)⟩,
    fun i => h1 i, fun i j hij => h2 i j hij, fun i => ?_⟩
  obtain ⟨f, hsurj, hint, hker⟩ := step_iff.1 (h3 i)
  refine step_iff.2 ⟨f, hsurj, fun g v hv => ?_, hker⟩
  have e := hint g v hv
  rw [ofChar_apply] at e
  show f (τ g v) = ofChar η g (f v)
  rw [h, map_smul, e, ofChar_apply, hη, Units.val_mul, smul_eq_mul]
  ring

theorem jhMult_of_twist {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ τ : Representation ℂ G V} {δ : G →* ℂˣ} (θ : G →* ℂˣ)
    (h : ∀ g v, τ g v = (((δ g)⁻¹ : ℂˣ) : ℂ) • ρ g v) :
    jhMult (ofChar θ) τ = jhMult (ofChar (θ * δ)) ρ := by
  have key : ∀ r, OccursTimes (ofChar θ) τ r ↔ OccursTimes (ofChar (θ * δ)) ρ r := fun r =>
    ⟨occursTimes_of_twist (δ := δ)
        (fun g v => by rw [h, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul])
        (fun g => MonoidHom.mul_apply θ δ g),
      occursTimes_of_twist (δ := δ⁻¹) (fun g v => by rw [MonoidHom.inv_apply]; exact h g v)
        (fun g => by rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_cancel_right])⟩
  simp only [jhMult, key]

private lemma pres_iterate_zero {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {θ : G →* ℂˣ} (hθ : ∀ t ∈ H, θ t = 1) (S : Subrepresentation ρ)
    (f : V →ₗ[ℂ] ℂ) (hf : ∀ g, ∀ v ∈ S.toSubmodule, f (ρ g v) = ofChar θ g (f v)) (v : V)
    (hv : v ∈ S.toSubmodule) : ∃ u ∈ fixed ρ H, u ∈ S.toSubmodule ∧ f u = f v := by

  obtain ⟨U, -, hU, hUv⟩ := GlobalTheory.LocGL.exists_normal_fix hρ hH v
  haveI : U.FiniteIndex := hU
  letI : Fintype (H ⧸ U) := Subgroup.fintypeQuotientOfFiniteIndex
  refine ⟨GlobalTheory.LocGL.idem hρ hH v, GlobalTheory.LocGL.idem_mem hρ hH v, ?_, ?_⟩
  · rw [GlobalTheory.LocGL.idem_eq_cosetSum hρ hH U hUv]
    exact S.toSubmodule.smul_mem _ (S.toSubmodule.sum_mem fun q _ => S.apply_mem_toSubmodule _ hv)
  · rw [GlobalTheory.LocGL.idem_eq_cosetSum hρ hH U hUv, map_smul, map_sum]
    have hq : ∀ q : H ⧸ U, f (ρ (q.out : H) v) = f v := fun q => by
      rw [hf _ v hv, ofChar_apply, hθ _ (q.out).2, Units.val_one, one_mul]
    have hc : (Fintype.card (H ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [hq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem jhMult_onFixed {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (hn : ∀ g, MonoidHom.id G g ∈ Subgroup.normalizer (H : Set G))
    {θ : G →* ℂˣ} (hθ : ∀ t ∈ H, θ t = 1) :
    jhMult (ofChar θ) ρ = jhMult (ofChar θ) (onFixed ρ H (MonoidHom.id G) hn) := by
  let ι : (onFixed ρ H (MonoidHom.id G) hn).IntertwiningMap ρ :=
    { toLinearMap := (fixed ρ H).subtype
      isIntertwining' := fun g => by ext v; rfl }
  have hι : Function.Injective ι := Subtype.val_injective
  have key : ∀ r, OccursTimes (ofChar θ) ρ r ↔
      OccursTimes (ofChar θ) (onFixed ρ H (MonoidHom.id G) hn) r := by
    intro r
    constructor
    · rintro ⟨S, T, h1, h2, h3⟩
      refine ⟨fun i => subComap ι (S i), fun i => subComap ι (T i), fun i => subComap_mono ι (h1 i),
        fun i j hij => subComap_mono ι (h2 i j hij), fun i => ?_⟩
      obtain ⟨f, hsurj, hint, hker⟩ := step_iff.1 (h3 i)
      refine step_iff.2 ⟨f ∘ₗ (fixed ρ H).subtype, fun w => ?_, fun g u hu => hint g u.1 hu,
        fun u hu => hker u.1 hu⟩
      obtain ⟨v, hv, rfl⟩ := hsurj w
      obtain ⟨u, huF, huS, hfu⟩ := pres_iterate_zero hρ hH hθ (S i) f hint v hv
      exact ⟨⟨u, huF⟩, huS, hfu⟩
    · rintro ⟨S, T, h1, h2, h3⟩
      exact ⟨fun i => subMap ι (S i), fun i => subMap ι (T i), fun i => subMap_mono ι (h1 i),
        fun i j hij => subMap_mono ι (h2 i j hij),
        fun i => step_iff.2 (step_map ι hι (step_iff.1 (h3 i)))⟩
  simp only [jhMult, key]

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isCompact_unitsO : IsCompact {x : kˣ | valuation k (x : k) = 1} := by
  haveI : T1Space k := IsTopologicalAddGroup.t1Space k (by
    first
      | exact isClosed_singleton
      | (convert (Valuation.isClosed_sphere (v := valuation k) 0) using 1
         ext x
         simp))
  have hS : IsCompact (((valuation k).integer.toSubmonoid : Submonoid k) : Set k) :=
    IsNonarchimedeanLocalField.isCompact_closedBall k 1
  convert Submonoid.units_isCompact hS using 1
  ext x
  have h0 : valuation k (x : k) ≠ 0 := by simp
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submonoid.mem_units_iff, Subring.mem_toSubmonoid,
    Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · intro hx
    simp [hx]
  · rintro ⟨h1, h2⟩
    rw [inv_le_one₀ (zero_lt_iff.2 h0)] at h2
    exact le_antisymm h1 h2

theorem isCompact_torusO (n : Type) : IsCompact (torusO k n : Set (n → kˣ)) :=
  isCompact_pi_infinite fun _ => isCompact_unitsO k

theorem deltaHalf_torusO {n : Type} [Fintype n] [LinearOrder n] {t : n → kˣ} (ht : t ∈ torusO k n) :
    deltaHalf k (fun _ : n => Unit) (leviTorus k n t) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  have hdet : Matrix.GeneralLinearGroup.det (leviTorus k n t a) = t a :=
    congrFun ((leviTorus k n).symm_apply_apply t) a
  have hv : valuation k (t a : k) = 1 := (show ∀ i, valuation k (t i : k) = 1 from ht) a
  apply Units.ext
  rw [hdet, val_absPow, nabs_eq_one k hv, Units.val_one]
  simp

variable {k} {n V : Type} [Fintype n] [DecidableEq n] [LinearOrder n] [AddCommGroup V] [Module ℂ V]

theorem jacB_apply (π : Representation ℂ (GL n k) V) (g : n → kˣ) (v : Jacquet π (unipB k n)) :
    jacB π g v = (((((deltaHalf k fun _ : n => Unit).comp
      (leviTorus k n).toMonoidHom) g)⁻¹ : ℂˣ) : ℂ) • jacBU π g v := by
  first
    | exact twist_apply (jacU (points n) π) (deltaHalf k fun _ : n => Unit)⁻¹ (leviTorus k n g) v
    | (show twist (jacU (points n) π) (deltaHalf k fun _ : n => Unit)⁻¹ (leviTorus k n g) v = _
       rw [twist_apply]
       rfl)

theorem jhMult_jacBU_eq_expMult {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π)
    {θ : (n → kˣ) →* ℂˣ} (hθ : ∀ t ∈ torusO k n, θ t = 1) :
    jhMult (ofChar θ) (jacBU π) = expMult π θ := by
  unfold expMult jacBUFixed
  exact jhMult_onFixed (isSmooth_jacBU hπ) (isCompact_torusO k n) _ hθ

theorem jhMult_jacB_eq_expMult : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → ∀ θ : (Fin n → kˣ) →* ℂˣ, (∀ t ∈ torusO k (Fin n), θ t = 1) → jhMult (ofChar θ) (jacB π) = expMult π (θ * (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) := by
  intro k _ _ _ _ n V _ _ π hπ θ hθ
  rw [jhMult_of_twist θ (fun g v => jacB_apply π g v)]
  refine jhMult_jacBU_eq_expMult hπ fun t ht => ?_
  rw [MonoidHom.mul_apply, hθ t ht, one_mul]
  exact deltaHalf_torusO k ht

end GlobalTheory.SmGL.UnramFixed
end
end

