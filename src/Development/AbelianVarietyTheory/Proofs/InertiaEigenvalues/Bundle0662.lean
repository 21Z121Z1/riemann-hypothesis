import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarizableComplexRepOfSupercuspidalUnitaryCentralCharacter
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

noncomputable section

namespace GlobalTheory.SupercuspUnitary

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def scal (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) : Subgroup G where
  carrier := {h | ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ y, l (ρ h y) = c * l y}
  mul_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    refine ⟨c * d, by rw [norm_mul, hc, hd, one_mul], fun y => ?_⟩
    rw [map_mul, Module.End.mul_apply, ha, hb, mul_assoc]
  one_mem' := ⟨1, by simp, fun y => by simp⟩
  inv_mem' := by
    rintro a ⟨c, hc, ha⟩
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    refine ⟨c⁻¹, by rw [norm_inv, hc, inv_one], fun y => ?_⟩
    have h := ha (ρ a⁻¹ y)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

def term (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (g : G) : ℂ :=
  l (ρ g⁻¹ v) * starRingEnd ℂ (l (ρ g⁻¹ w))

theorem term_mul {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (v w : V) (g : G) {h : G}
    (hh : h ∈ scal ρ l) : term ρ l v w (g * h) = term ρ l v w g := by
  obtain ⟨c, hc, hl⟩ := (scal ρ l).inv_mem hh
  have h1 : c * starRingEnd ℂ c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  simp only [term, mul_inv_rev, map_mul, Module.End.mul_apply, hl]
  linear_combination (l (ρ g⁻¹ v) * starRingEnd ℂ (l (ρ g⁻¹ w))) * h1

theorem term_inv_mul (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (x g : G) :
    term ρ l v w (x⁻¹ * g) = term ρ l (ρ x v) (ρ x w) g := by
  simp only [term, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

def qterm (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (q : G ⧸ scal ρ l) : ℂ :=
  term ρ l v w q.out

theorem qterm_mk (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (g : G) :
    qterm ρ l v w (g : G ⧸ scal ρ l) = term ρ l v w g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (scal ρ l) g
  rw [qterm, hh, term_mul v w g h.2]

theorem center_le_scal {ρ : Representation ℂ G V} (l : Module.Dual ℂ V)
    (hz : ∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) :
    Subgroup.center G ≤ scal ρ l := fun z hz' => by
  obtain ⟨c, hc, h⟩ := hz z hz'
  exact ⟨c, hc, fun y => by rw [h, map_smul, smul_eq_mul]⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isOpen_scal {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (hl : l ∈ smoothPart ρ.dual) :
    IsOpen (scal ρ l : Set G) := by
  refine (scal ρ l).isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((show IsOpen
    {g : G | ρ.dual g l = l} from hl).mem_nhds (by
      simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply])) fun g hg => ⟨1, by simp, fun y => ?_⟩)
  have h1 : (ρ.dual g l) (ρ g y) = l (ρ g y) := by rw [show ρ.dual g l = l from hg]
  rw [Representation.dual_apply] at h1
  simp only [Module.Dual.transpose_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply] at h1
  rw [one_mul, h1]

theorem exists_finset {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (hl : l ∈ smoothPart ρ.dual)
    (hsc : IsSupercuspidal ρ) (hz : ∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v)
    (v : V) : ∃ s : Finset (G ⧸ scal ρ l), ∀ g : G, l (ρ g⁻¹ v) ≠ 0 → (g : G ⧸ scal ρ l) ∈ s := by
  obtain ⟨C, hC, hCz⟩ := hsc.2 v l hl
  haveI := QuotientGroup.discreteTopology (isOpen_scal hl)
  have hD : ((fun c : G => ((c⁻¹ : G) : G ⧸ scal ρ l)) '' C).Finite :=
    (hC.image (by fun_prop)).finite_of_discrete
  refine ⟨hD.toFinset, fun g hg => ?_⟩
  obtain ⟨z, hz', c, hc, e⟩ := hCz g⁻¹ hg
  rw [Set.Finite.mem_toFinset]
  refine ⟨c, hc, QuotientGroup.eq.2 ?_⟩
  have h2 : (c⁻¹)⁻¹ * g = z⁻¹ := by rw [← inv_inv g, e]; group
  rw [h2]
  exact center_le_scal l hz (inv_mem hz')

end GlobalTheory.SupercuspUnitary

namespace GlobalTheory

open GlobalTheory.SupercuspUnitary in

theorem isUnitarisable_of_isSupercuspidal : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (l : Module.Dual ℂ V), l ∈ smoothPart ρ.dual →
    l ≠ 0 → ρ.IsIrreducible → IsSupercuspidal ρ →
    (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) → IsUnitarisable ρ := by
  intro G V _ _ _ _ _ ρ l hl hl0 hirr hsc hz
  have hfin : ∀ v w, (Function.support (qterm ρ l v w)).Finite := fun v w => by
    obtain ⟨s, hs⟩ := exists_finset hl hsc hz v
    refine s.finite_toSet.subset fun q hq => ?_
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [Function.mem_support, qterm_mk] at hq
      exact hs g (left_ne_zero_of_mul hq)

  have hadd1 : ∀ v v' w q, qterm ρ l (v + v') w q = qterm ρ l v w q + qterm ρ l v' w q := by
    intro v v' w q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_add, add_mul]
  have hsmul1 : ∀ (a : ℂ) v w q, qterm ρ l (a • v) w q = a * qterm ρ l v w q := by
    intro a v w q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_smul, smul_eq_mul, mul_assoc]
  have hadd2 : ∀ v w w' q, qterm ρ l v (w + w') q = qterm ρ l v w q + qterm ρ l v w' q := by
    intro v w w' q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_add, mul_add]
  have hsmul2 : ∀ (a : ℂ) v w q, qterm ρ l v (a • w) q = starRingEnd ℂ a * qterm ρ l v w q := by
    intro a v w q
    induction q using QuotientGroup.induction_on with
    | H g =>
      simp only [qterm_mk, term, map_smul, smul_eq_mul, map_mul]
      ring
  have hconj : ∀ v w q, qterm ρ l w v q = starRingEnd ℂ (qterm ρ l v w q) := by
    intro v w q
    induction q using QuotientGroup.induction_on with
    | H g =>
      simp only [qterm_mk, term, map_mul, Complex.conj_conj]
      ring
  have hinv : ∀ (x : G) v w q, qterm ρ l (ρ x v) (ρ x w) q = qterm ρ l v w (x⁻¹ • q) := by
    intro x v w q
    induction q using QuotientGroup.induction_on with
    | H g => rw [MulAction.Quotient.smul_mk, smul_eq_mul, qterm_mk, qterm_mk, term_inv_mul]
  let B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => ∑ᶠ q, qterm ρ l v w q)
    (fun v v' w => by simp only [hadd1]; exact finsum_add_distrib (hfin v w) (hfin v' w))
    (fun a v w => by simp only [hsmul1, RingHom.id_apply, smul_eq_mul, mul_finsum])
    (fun v w w' => by simp only [hadd2]; exact finsum_add_distrib (hfin v w) (hfin v w'))
    (fun a v w => by simp only [hsmul2, smul_eq_mul, mul_finsum])
  have hB : ∀ v w, B v w = ∑ᶠ q, qterm ρ l v w q := fun v w => LinearMap.mk₂'ₛₗ_apply _ _ _
  refine ⟨B, fun v w => ?_, fun v hv => ?_, fun x v w => ?_⟩
  · rw [hB, hB, map_finsum _ (hfin v w)]
    exact finsum_congr fun q => hconj v w q
  · have hex : ∃ g : G, l (ρ g v) ≠ 0 := by
      by_contra! h0
      let U : Subrepresentation ρ :=
        { toSubmodule := ⨅ g : G, LinearMap.ker (l ∘ₗ (ρ g : V →ₗ[ℂ] V))
          apply_mem_toSubmodule := fun g y hy => by
            simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hy ⊢
            intro g'
            rw [← Module.End.mul_apply, ← map_mul]
            exact hy _ }
      haveI := hirr
      rcases eq_bot_or_eq_top U with hU | hU
      · have hvU : v ∈ U.toSubmodule := by
          simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
          exact h0
        rw [hU] at hvU
        exact hv ((Submodule.mem_bot ℂ).1 hvU)
      · refine hl0 (LinearMap.ext fun y => ?_)
        have hyU : y ∈ U.toSubmodule := by rw [hU]; exact Submodule.mem_top
        simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hyU
        simpa using hyU 1
    obtain ⟨g, hg⟩ := hex
    rw [hB, finsum_eq_sum _ (hfin v v), Complex.re_sum]
    refine Finset.sum_pos' (fun q _ => ?_) ⟨((g⁻¹ : G) : G ⧸ scal ρ l), ?_, ?_⟩
    · induction q using QuotientGroup.induction_on with
      | H g' =>
        rw [qterm_mk, term, Complex.mul_conj, Complex.ofReal_re]
        exact Complex.normSq_nonneg _
    · rw [Set.Finite.mem_toFinset, Function.mem_support, qterm_mk, term, inv_inv, Complex.mul_conj]
      exact_mod_cast (Complex.normSq_pos.2 hg).ne'
    · rw [qterm_mk, term, inv_inv, Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_pos.2 hg
  · rw [hB, hB]
    simp only [hinv]
    exact finsum_comp_equiv (MulAction.toPerm (x⁻¹ : G) : Equiv.Perm (G ⧸ scal ρ l))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetProUnipotentRadicalFixedVectorsLift
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix Topology Filter

namespace GlobalTheory.LocGL.ProRadOnto

section Abstract

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]

theorem exists_fixed_mk_eq {π : Representation ℂ G V} (hπ : IsAdmissible π) {I N : Subgroup G}
    (ho : IsOpen (I : Set G)) (hc : IsCompact (I : Set G)) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) (M₀ : Subgroup M) (hM₀ : ∀ d ∈ M₀, s d ∈ I)
    (C : Set G) (hfac : ∀ g ∈ I, ∃ d ∈ M₀, ∃ x ∈ N, ∃ c ∈ C, g = s d * x * c)
    (hcon : ∀ U ∈ 𝓝 (1 : G), ∃ t : M, (∀ d ∈ M₀, d * t = t * d) ∧ ∀ c ∈ C, (s t)⁻¹ * c * s t ∈ U)
    (y : Jacquet π N) (hy : y ∈ fixed (jacquet π N s hs) M₀) :
    ∃ v ∈ fixed π I, (twKer π N 1).mkQ v = y := by
  set p := (twKer π N 1).mkQ with hp
  set σ := jacquet π N s hs with hσ
  have hps : ∀ m v, p (π (s m) v) = σ m (p v) := fun _ _ => rfl
  have hpN : ∀ x ∈ N, ∀ v, p (π x v) = p v := fun x hx v =>
    (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨x, hx⟩, v, by simp⟩)
  obtain ⟨u, rfl⟩ : ∃ u, p u = y := Submodule.mkQ_surjective _ y
  obtain ⟨t, htc, ht⟩ := hcon _ ((ho.inter (hπ.1 u)).mem_nhds ⟨one_mem I, by simp⟩)
  set Y := (fixed π I).map p with hY
  haveI := hπ.2 I ho hc
  have key : ∀ w, (∀ c ∈ C, π ((s t)⁻¹ * c * s t) w = w) → (∀ d ∈ M₀, σ d (p w) = p w) →
      σ t (p w) ∈ Y := by
    intro w h1 h2
    refine IwahoriOnto.exists_fixed_map_eq hπ.1 hc p (π (s t) w) fun g hg => ?_
    obtain ⟨d, hd, x, hx, c, hcC, rfl⟩ := hfac g hg
    have h3 : π c (π (s t) w) = π (s t) w := by
      conv_rhs => rw [← h1 c hcC]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h3, hps, hpN x hx, hps,
      ← Module.End.mul_apply, ← map_mul, htc d hd, map_mul, Module.End.mul_apply, h2 d hd]
  have hinj : Function.Injective (σ t) := by
    intro a b hab
    have := congrArg (σ t⁻¹) hab
    simpa [← Module.End.mul_apply, ← map_mul] using this
  have hst : ∀ z ∈ Y, σ t z ∈ Y := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : ∀ g ∈ I, π g w = w := fun g hg => by simpa using hw ⟨g, hg⟩
    exact key w (fun c hcC => hw' _ (ht c hcC).1) fun d hd => by rw [← hps, hw' _ (hM₀ d hd)]
  have hsurj : Function.Surjective ((σ t).restrict hst) :=
    LinearMap.surjective_of_injective fun a b hab => Subtype.ext (hinj (congrArg Subtype.val hab))
  obtain ⟨z, hz⟩ := hsurj ⟨_, key u (fun c hcC => (ht c hcC).2) fun d hd => by simpa using hy ⟨d, hd⟩⟩
  have : (z : Jacquet π N) = p u := hinj (congrArg Subtype.val hz)
  exact this ▸ z.2

end Abstract

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n]

theorem jMinus_contract (e : (Σ a, m a) ≃ n) : ∀ U ∈ 𝓝 (1 : GL n k), ∃ t : Levi k m,
    (∀ d : Levi k m, d * t = t * d) ∧ ∀ c ∈ jMinus k e, (leviEmb k e t)⁻¹ * c * leviEmb k e t ∈ U := by
  intro U hU
  let r : α → ℕ := fun a => (Finset.univ.filter fun b => b < a).card
  have hr : ∀ a b, b < a → r b < r a := fun a b hab =>
    Finset.card_lt_card ⟨fun l hl => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
      exact hl.trans hab, fun hs => by simpa using hs (show b ∈ _ by simpa using hab)⟩
  let S : kˣ → Levi k m := fun x a => Units.map (Matrix.scalar (m a)).toMonoidHom (x ^ r a)⁻¹
  let T : kˣ → n → kˣ := fun x i => (x ^ r (blk e i))⁻¹
  have hST : ∀ x, leviEmb k e (S x) = diagT k n (T x) := by
    intro x
    ext i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    rw [val_diagT, diagonal_apply]
    by_cases h : a = b
    · subst h
      rw [leviEmb_apply_same]
      simp [S, T, Matrix.scalar_apply, diagonal_pow, diagonal_apply, inv_pow]
    · rw [leviEmb_apply_ne k e _ h, if_neg fun h' => h (congrArg Sigma.fst (e.injective h'))]
  have hcomm : ∀ x (d : Levi k m), d * S x = S x * d := fun x d => funext fun a => Units.ext
    ((Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq).symm
  let F : Filter (kˣ × jMinus k e) := (comap (fun x : kˣ => (x : k)) (𝓝 0)) ×ˢ ⊤
  have hent : ∀ (x : kˣ) (c : GL n k) i j, ((diagT k n (T x))⁻¹ * c * diagT k n (T x)).val i j =
      (x : k) ^ r (blk e i) * c.val i j * ((x : k) ^ r (blk e j))⁻¹ := by
    intro x c i j
    rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, mul_diagonal, diagonal_mul]
    simp [T]
  have hT : Tendsto (fun p : kˣ × jMinus k e => (diagT k n (T p.1))⁻¹ * p.2.1 * diagT k n (T p.1)) F
      (𝓝 1) := by
    rw [SplitFlip.isEmbedding_val_GL.tendsto_nhds_iff]
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    simp only [Function.comp_def, hent]
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    simp only [blk_apply, Units.val_one]
    rcases lt_trichotomy a b with hab | rfl | hab
    · have h0 : ∀ p : kˣ × jMinus k e, (p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := fun p =>
        (mem_parabLower_iff k).1 ((mem_unipRadLower k).1 p.2.2.1).1 a b i j hab
      simp only [h0, mul_zero, zero_mul, IwahoriFactor.one_ne e hab.ne]
      exact tendsto_const_nhds
    · have h1 : ∀ p : kˣ × jMinus k e, (p.1 : k) ^ r a * (p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) *
          ((p.1 : k) ^ r a)⁻¹ = (1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨a, j⟩) := fun p => by
        rw [((mem_unipRadLower k).1 p.2.2.1).2 a i j, IwahoriFactor.one_same, mul_comm, ← mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero _ p.1.ne_zero), one_mul]
      simp only [h1]
      exact tendsto_const_nhds
    · rw [IwahoriFactor.one_ne e hab.ne', (IsValuativeTopology.hasBasis_nhds_zero k).tendsto_right_iff]
      intro γ _
      have h1 : {x : k | valuation k x < γ} ∈ 𝓝 (0 : k) :=
        (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, fun _ h => h⟩
      have h2 : {x : k | valuation k x < 1} ∈ 𝓝 (0 : k) :=
        (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun _ h => h⟩
      filter_upwards [prod_mem_prod (preimage_mem_comap (inter_mem h1 h2)) univ_mem] with p hp
      obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_lt (hr a b hab)
      have hint : valuation k ((p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩)) ≤ 1 := by
        have := StepData.mem_KOne.1 p.2.2.2 (e ⟨a, i⟩) (e ⟨b, j⟩)
        rw [Matrix.sub_apply, IwahoriFactor.one_ne e hab.ne', sub_zero] at this
        exact this.le
      have : (p.1 : k) ^ r a * (p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩) * ((p.1 : k) ^ r b)⁻¹ =
          p.1 * (p.1 ^ l * (p.2.1 : Matrix n n k) (e ⟨a, i⟩) (e ⟨b, j⟩)) := by
        rw [hl]; field_simp; ring
      show valuation k _ < _
      rw [this, map_mul, map_mul, map_pow]
      exact (mul_le_of_le_one_right' (mul_le_one' (pow_le_one' hp.1.2.le _) hint)).trans_lt hp.1.1
  haveI : (comap (fun x : kˣ => (x : k)) (𝓝 0)).NeBot := by
    refine comap_neBot fun s hs => ?_
    obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff s).1 hs
    obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : ValueGroupWithZero k, δ ≠ 0 ∧ δ < γ :=
      ⟨uniformizer k * γ, by simp, mul_lt_of_lt_one_left γ.zero_lt uniformizer_lt_one⟩
    obtain ⟨x, rfl⟩ := valuation_surjective δ
    exact ⟨Units.mk0 x (by simpa using hδ0), hγ hδ⟩
  obtain ⟨x, hx⟩ := Filter.nonempty_of_mem (mem_prod_top.1 (hT hU))
  exact ⟨S x, hcomm x, fun c hc => by rw [hST]; exact hx ⟨c, hc⟩⟩

end Local

end GlobalTheory.LocGL.ProRadOnto

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel in

theorem GlobalTheory.LocGL.ProRadOnto.exists_proRad_fixed_mk_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α n : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), IsAdmissible π → ∀ y : Jacquet π (unipRad k e), y ∈ fixed (jacU e π) (leviKOne k m) → ∃ v ∈ fixed π (proRad k e), (Submodule.Quotient.mk v : Jacquet π (unipRad k e)) = y := by
  intro k _ _ _ _ α n _ _ m _ _ _ _ e V _ _ π hπ y hy
  obtain ⟨v, hv, h⟩ := ProRadOnto.exists_fixed_mk_eq hπ (isOpen_levelPre _) (isCompact_levelPre _) (leviEmb k e)
    (N := unipRad k e) (leviEmb_mem_normalizer k e) (leviKOne k m)
    (fun d hd => jLevi_le_proRad e ⟨d, hd, rfl⟩) (jMinus k e) (fun g hg => by
      obtain ⟨d, ⟨d', hd', rfl⟩, u, hu, c, hc, rfl⟩ := IwahoriFactor.levi_plus_minus e hg
      exact ⟨d', hd', u, hu.1, c, hc, rfl⟩)
    (fun U hU => by
      obtain ⟨t, ht, h⟩ := ProRadOnto.jMinus_contract e U hU
      exact ⟨t, fun d _ => ht d, h⟩) y hy
  exact ⟨v, hv, h⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsClassificationUnitary
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.LocGL

theorem exists_isL_of_unitary_twists (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (hS : GlobalTheory.Published.StandardCosocleGL)
    (hP : ∀ (δ δ' : IrrGL k) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y)
    (𝔫 : Multiset (Segment k))
    (h𝔫 : ∀ Δ ∈ 𝔫, ∃ (δ : IrrGL k) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)) : ∃ y : IrrGL k, IsL 𝔫 y.rep := by
  classical
  have h' : ∀ Δ ∈ 𝔫, ∃ (t : ℝ) (δ : IrrGL k) (Γ : Segment k), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ) := fun Δ h =>
    let ⟨δ, Γ, t, h⟩ := h𝔫 Δ h
    ⟨t, δ, Γ, h⟩
  choose! t ht using h'
  let r : Segment k → Segment k → Prop := fun a b => t b ≤ t a
  haveI : IsTrans (Segment k) r := ⟨fun a b c h1 h2 => le_trans h2 h1⟩
  haveI : Std.Total r := ⟨fun a b => le_total _ _⟩
  obtain ⟨l, hl, hs⟩ : ∃ l : List (Segment k), (l : Multiset (Segment k)) = 𝔫 ∧ l.Pairwise r :=
    ⟨𝔫.toList.insertionSort r,
      (Multiset.coe_eq_coe.2 (List.perm_insertionSort r _)).trans (Multiset.coe_toList 𝔫),
      List.pairwise_insertionSort r _⟩
  have hm : ∀ i : Fin l.length, l.get i ∈ 𝔫 := fun i => by
    rw [← hl]; exact List.get_mem l i
  choose δ Γ hL hU hE using fun i : Fin l.length => ht _ (hm i)
  have hF : LFactors 𝔫 (fun i : Fin l.length => (δ i).nu (t (l.get i))) := by
    refine ⟨fun i => (Γ i).nu (t (l.get i)), ⟨?_, fun i j hij h => ?_⟩, fun i => ?_⟩
    · rw [← hl, ← funext hE]
      simp
    · have h1 : t (l.get j) ≤ t (l.get i) := List.pairwise_iff_get.1 hs i j hij
      have := hP _ _ _ _ (hL i) (hU i) (hL j) (hU j) _ _ h
      linarith
    · exact ((hL i).tw _ (isSmoothChar_absPow _)).of_equiv ((δ i).twEquiv _ _)
  obtain ⟨π, hπ⟩ := hS k 𝔫 _ _ _ rfl hF
  exact ⟨IrrGL.of π.ρ π.smooth π.irr, _, _, rfl, hF, hπ.of_equiv (IrrGL.equivOf _ _ _) (.refl _)⟩

end GlobalTheory.LocGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsQuotientOfSpehTypeProductIsL
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

noncomputable section

namespace GlobalTheory

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem segment_nu_nu (Δ : Segment k) (a b : ℂ) : (Δ.nu a).nu b = Δ.nu (a + b) :=
  Segment.ext_first (show (Δ.first.nu a).nu b = Δ.first.nu (a + b) from IrrGL.nu_nu _ _ _) rfl

theorem isLSeg_nu {Δ : Segment k} {x : IrrGL k} (h : IsLSeg Δ x.rep) (s : ℂ) : IsLSeg (Δ.nu s) (x.nu s).rep :=
  (h.tw _ _).of_equiv (x.twEquiv _ _)

theorem univ_map_speh_segments (d m : ℕ) (Δ : Fin m → Segment k) (s : Fin m → ℝ) :
    Finset.univ.val.map (fun p : Fin (d * m) => ((Δ (finProdFinEquiv.symm p).2).nu (s (finProdFinEquiv.symm p).2)).nu
      ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)) = ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) := by
  rw [Fin.univ_val_map]
  congr 1
  rw [List.ofFn_mul, List.flatMap_def, ← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map]
  congr 1
  refine List.ofFn_inj.2 (funext fun i => ?_)
  rw [Function.comp_apply, List.map_ofFn]
  refine List.ofFn_inj.2 (funext fun j => ?_)
  have : ∀ h, finProdFinEquiv.symm (⟨i * m + j, h⟩ : Fin (d * m)) = (i, j) := fun h => by
    rw [Equiv.symm_apply_eq]; ext; simp [finProdFinEquiv_apply_val]; ring
  simp only [Function.comp, this]

end SlopeTestRemainingChoices

theorem speh_quotient_isL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    GlobalTheory.Published.StandardCosocleGL → (∀ (δ δ' : IrrGL k) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y) → (∀ (d h : ℕ) (y : Fin d → Fin h → IrrGL k) (N : Fin d → ℕ) (M : ℕ) (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM'))) →
    ∀ (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin a) k) V)
    (m : ℕ) (δ : Fin m → IrrGL k) (Δ : Fin m → Segment k) (s : Fin m → ℝ), (∀ j, IsLSeg (Δ j) (δ j).rep) →
      (∀ j, IsUnitarisable (δ j).rep) → (∀ j, |s j| < 1 / 2) → ∀ hd : ∑ j, ((δ j).nu (s j)).1 = a,
      Nonempty (σ.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) →
    ∀ (d n : ℕ) (hdn : ∑ _ : Fin d, a = n) (W : Type) [AddCommGroup W] [Module ℂ W]
      (σ' : Representation ℂ (GL (Fin n) k) W), σ'.IsIrreducible →
      (∃ f : (multiProd (stdBlocks (fun _ : Fin d => a) hdn) fun i : Fin d =>
        twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).IntertwiningMap σ',
        Function.Surjective f) →
      IsL ↑((List.range d).flatMap fun i : ℕ =>
        (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ)) σ' := by
  intro k _ _ _ _ _ hLM hprec hstage a V _ _ σ m δ Δ s hΔ hδu hs hd hσ d n hdn W _ _ σ' hirr hf
  obtain ⟨φ⟩ := hσ
  obtain ⟨f, hfs⟩ := hf
  let y : Fin d → Fin m → IrrGL k := fun i j => ((δ j).nu (s j)).nu (((d : ℂ) - 1) / 2 - (i : ℕ))
  have hN : ∀ i, ∑ j, (y i j).1 = a := fun _ => hd
  let Y : Fin (d * m) → IrrGL k := fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  have hM' : ∑ p, (Y p).1 = n := by
    rw [← hdn, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Y, Equiv.symm_apply_apply]
    exact hN i
  let e1 : ∀ i : Fin d, (twist σ (detChar (Fin a) (absPow k (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (prodIrr (y i) (hN i)) :=
    fun i => (twistEquiv φ _).trans (prodIrrTwistEquiv _ hd _ (isSmoothChar_absPow _))
  obtain ⟨e2⟩ := hstage d m y (fun _ => a) n hN hdn hM'
  let E := (multiProdEquiv _ e1).trans e2
  let Γs : Fin (d * m) → Segment k := fun p =>
    ((Δ (finProdFinEquiv.symm p).2).nu (s (finProdFinEquiv.symm p).2)).nu
      ((((d : ℝ) - 1) / 2 - ((finProdFinEquiv.symm p).1 : ℕ) : ℝ) : ℂ)
  have hcast : ∀ i : ℕ, (((((d : ℝ) - 1) / 2 - i : ℝ)) : ℂ) = ((d : ℂ) - 1) / 2 - (i : ℕ) := fun i => by
    push_cast; ring
  have hL : ∀ p, IsLSeg (Γs p) (Y p).rep := fun p => by
    simp only [Γs, Y, y, hcast]
    exact isLSeg_nu (isLSeg_nu (hΔ _) _) _
  have hord : ∀ p p' : Fin (d * m), p < p' → ¬ (Γs p).Precedes (Γs p') := by
    intro p p' hpp' hP
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective p
    obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective p'
    have hii : (i : ℕ) ≤ i' := by
      by_contra hlt
      have h1 : (i' : ℕ) + 1 ≤ i := by omega
      have h2 := Nat.mul_le_mul_left m h1
      have h3 := Fin.lt_def.1 hpp'
      simp only [finProdFinEquiv_apply_val] at h3
      have := j.2
      have := j'.2
      nlinarith
    simp only [Γs, Equiv.symm_apply_apply, segment_nu_nu] at hP
    have key := hprec (δ j) (δ j') (Δ j) (Δ j') (hΔ j) (hδu j) (hΔ j') (hδu j')
      (s j + (((d : ℝ) - 1) / 2 - (i : ℕ))) (s j' + (((d : ℝ) - 1) / 2 - (i' : ℕ))) (by push_cast at hP ⊢; exact hP)
    have hi : ((i : ℕ) : ℝ) ≤ (i' : ℕ) := by exact_mod_cast hii
    have := abs_lt.1 (hs j)
    have := abs_lt.1 (hs j')
    linarith
  have hLF : LFactors (↑((List.range d).flatMap fun i : ℕ =>
      (List.ofFn fun j => (Δ j).nu (s j)).map fun Γ => Γ.nu ((((d : ℝ) - 1) / 2 - i : ℝ) : ℂ))) Y :=
    ⟨Γs, ⟨univ_map_speh_segments d m Δ s, hord⟩, hL⟩
  obtain ⟨π, hπ⟩ := hLM k _ (d * m) n Y hM' hLF
  obtain ⟨ψ⟩ := hπ.equiv_of_surjective hirr (f.comp E.symm.toIntertwiningMap)
    (hfs.comp E.symm.toLinearEquiv.surjective)
  exact ⟨d * m, Y, hM', hLF, hπ.of_equiv ψ.symm (.refl _)⟩

end GlobalTheory
end
end

