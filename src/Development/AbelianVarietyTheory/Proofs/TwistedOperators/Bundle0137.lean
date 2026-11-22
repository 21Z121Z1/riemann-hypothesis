import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Formalism.LocalRingCardinality.Bundle0005
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParIffStepGap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingIntegralJointHarmonicPos
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdditiveFamilyFunctionDeterminedConstituents
section
noncomputable section

open scoped TensorProduct
open GlobalTheory.PRep GlobalTheory.JHMult

namespace GlobalTheory.SmGL

namespace AdditiveExpand

variable {G : Type} [Group G] [TopologicalSpace G]

open Classical in

theorem jhMult_rep_rep (c d : IrrCl G) : jhMult c.rep.ρ d.rep.ρ = if c = d then 1 else 0 := by
  split_ifs with h
  · subst h; exact jhMult_self c.rep.irr
  · by_contra h0
    obtain ⟨φ⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv c.rep.irr d.rep.irr
    exact h (c.cl_rep.symm.trans ((IrrRep.cl_eq_iff.2 ⟨φ.symm⟩).trans d.cl_rep))

variable (φ : SmRep G → ℕ∞) (h0 : ∀ B : SmRep G, Subsingleton B.V → φ B = 0)
  (hadd : ∀ (B B₁ B₂ : SmRep G) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ),
    Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) →
      (∀ v, p v = 0 → ∃ u, ι u = v) → φ B = φ B₁ + φ B₂)

variable [IsTopologicalGroup G]

def sub (B : SmRep G) (S : Subrepresentation B.ρ) : SmRep G :=
  ⟨S.toSubmodule, S.toRepresentation,
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ B.smooth⟩

def quo (B : SmRep G) (S T : Subrepresentation B.ρ) : SmRep G :=
  ⟨_, subQuot S T, IsSubquotient.isSmooth
    ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩ B.smooth⟩

include h0 hadd

theorem congr_equiv {B B' : SmRep G} (e : B.ρ.Equiv B'.ρ) : φ B = φ B' := by
  have hs : Subsingleton (sub B ⊥).V := inferInstanceAs (Subsingleton (⊥ : Submodule ℂ B.V))
  have := hadd B (sub B ⊥) B' ⟨Submodule.subtype _, fun _ => rfl⟩ e.toIntertwiningMap
    Subtype.val_injective e.surjective
    (fun u => by rw [Subsingleton.elim u 0, map_zero, map_zero])
    (fun v hv => ⟨0, by
      rw [map_zero]
      exact (e.injective (hv.trans (map_zero e).symm)).symm⟩)
  rw [this, h0 _ hs, zero_add]

theorem one_coord₂ (B : SmRep G) (h : HasFiniteLength B.ρ) (T : Finset (IrrCl G))
    (hT : ∀ c ∉ T, jhMult c.rep.ρ B.ρ = 0) :
    φ B = ∑ c ∈ T, jhMult c.rep.ρ B.ρ * φ (SmRep.ofIrr c.rep) := by
  classical
  have ψ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := B.ρ)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  have : WellFoundedGT (Subrepresentation B.ρ) := ψ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation B.ρ) := ψ.toOrderEmbedding.wellFoundedLT
  have key : ∀ S : Subrepresentation B.ρ, (∀ c ∉ T, jhMult c.rep.ρ S.toRepresentation = 0) →
      φ (sub B S) = ∑ c ∈ T, jhMult c.rep.ρ S.toRepresentation * φ (SmRep.ofIrr c.rep) := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    intro hS'
    rcases eq_or_ne S ⊥ with rfl | hS
    · have hs : Subsingleton (⊥ : Subrepresentation B.ρ).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ B.V))
      rw [h0 _ hs]
      exact (Finset.sum_eq_zero fun c _ => by
        rw [jhMult_of_subsingleton c.rep.irr, zero_mul]).symm
    obtain ⟨R, -, hR⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hS)
    let σ : IrrRep G := ⟨_, subQuot S R, (quo B S R).smooth, isIrreducible_subQuot hR⟩
    obtain ⟨e⟩ := σ.nonempty_equiv_rep
    have hm : ∀ c : IrrCl G, jhMult c.rep.ρ S.toRepresentation =
        jhMult c.rep.ρ R.toRepresentation + if c = σ.cl then 1 else 0 := fun c => by
      rw [jhMult_of_le c.rep.irr hR.le, ← jhMult_rep_rep, jhMult_congr_right _ e]
    have hp : ∀ v : S.toSubmodule, (Submodule.Quotient.mk v : (quo B S R).V) = 0 ↔
        v.1 ∈ R.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have h1 := hadd (sub B S) (sub B R) (quo B S R) ⟨Submodule.inclusion hR.le, fun _ => rfl⟩
      ⟨Submodule.mkQ _, fun _ => rfl⟩ (Submodule.inclusion_injective hR.le)
      (Submodule.Quotient.mk_surjective _) (fun u => (hp _).2 u.2)
      fun v hv => ⟨⟨v.1, (hp v).1 hv⟩, rfl⟩
    have h2 : φ (quo B S R) = φ (SmRep.ofIrr σ.cl.rep) :=
      (congr_equiv φ h0 hadd (B := SmRep.ofIrr σ.cl.rep) (B' := quo B S R) e).symm
    have h3 : σ.cl ∈ T := by
      by_contra hn
      have := hS' _ hn
      rw [hm] at this
      simp at this
    rw [h1, h2, ih R hR.lt fun c hc => (add_eq_zero.1 ((hm c).symm.trans (hS' c hc))).1]
    simp only [hm, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', if_pos h3]
  have h4 := key ⊤ (by simpa only [jhMult_congr_right _ (topEquiv B.ρ)] using hT)
  rw [← congr_equiv φ h0 hadd (B := sub B ⊤) (B' := B) (topEquiv B.ρ), h4]
  simp only [jhMult_congr_right _ (topEquiv B.ρ)]

end AdditiveExpand

open AdditiveExpand in

theorem additive_family_expand : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)] [∀ i, IsTopologicalGroup (Γ i)] (Φ : (∀ i, GlobalTheory.SmGL.SmRep (Γ i)) → ℕ∞), (∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α), Subsingleton (A i).V → Φ A = 0) → (∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α) (B B₁ B₂ : GlobalTheory.SmGL.SmRep (Γ i)) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → Φ (Function.update A i B) = Φ (Function.update A i B₁) + Φ (Function.update A i B₂)) → ∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)), (∀ i, GlobalTheory.SmGL.HasFiniteLength (A i).ρ) → ∀ T : Finset (∀ i, GlobalTheory.SmGL.IrrCl (Γ i)), (∀ t ∉ T, ∃ i, GlobalTheory.SmGL.jhMult (t i).rep.ρ (A i).ρ = 0) → Φ A = ∑ t ∈ T, (∏ i, GlobalTheory.SmGL.jhMult (t i).rep.ρ (A i).ρ) * Φ (fun i => GlobalTheory.SmGL.SmRep.ofIrr (t i).rep) := by
  intro α _ _ Γ _ _ _ Φ h0 hadd
  classical
  have key : ∀ s : Finset α, ∀ A : ∀ i, SmRep (Γ i),
      (∀ i ∉ s, ∃ c : IrrCl (Γ i), A i = SmRep.ofIrr c.rep) → (∀ i, HasFiniteLength (A i).ρ) →
      ∀ T : Finset (∀ i, IrrCl (Γ i)), (∀ t ∉ T, ∃ i, jhMult (t i).rep.ρ (A i).ρ = 0) →
      Φ A = ∑ t ∈ T, (∏ i, jhMult (t i).rep.ρ (A i).ρ) * Φ (fun i => SmRep.ofIrr (t i).rep) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro A hA _ T hT
      choose c hc using fun i => hA i (Finset.notMem_empty i)
      obtain rfl : A = fun i => SmRep.ofIrr (c i).rep := funext hc
      have hm : ∀ t : ∀ i, IrrCl (Γ i),
          (∏ i, jhMult (t i).rep.ρ (SmRep.ofIrr (c i).rep).ρ) = if t = c then 1 else 0 := fun t => by
        have : ∀ i, jhMult (t i).rep.ρ (SmRep.ofIrr (c i).rep).ρ = if t i = c i then 1 else 0 :=
          fun i => jhMult_rep_rep _ _
        simp only [this, Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ,
          forall_const, funext_iff]
      have h3 : c ∈ T := by
        by_contra hn
        obtain ⟨i, hi⟩ := hT c hn
        exact one_ne_zero ((jhMult_self (c i).rep.irr).symm.trans hi)
      simp only [hm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', if_pos h3]
    | insert i s his ih =>
      intro A hA hl T hT
      let μ : ∀ j, IrrCl (Γ j) → SmRep (Γ j) → ℕ∞ := fun j c B => jhMult c.rep.ρ B.ρ
      have hC := finite_constituents (hl i)
      have h1 := one_coord₂ (fun B => Φ (Function.update A i B))
        (fun B hB => h0 _ i (by rw [Function.update_self]; exact hB)) (hadd A i) (A i) (hl i)
        hC.toFinset (fun c hc => by simpa using hc)
      simp only [Function.update_eq_self] at h1
      have h2 : ∀ c ∈ hC.toFinset, Φ (Function.update A i (SmRep.ofIrr c.rep)) =
          ∑ t ∈ T, ((if t i = c then 1 else 0) * ∏ j ∈ Finset.univ.erase i, μ j (t j) (A j)) *
            Φ (fun i => SmRep.ofIrr (t i).rep) := by
        intro c hc
        rw [ih (Function.update A i (SmRep.ofIrr c.rep)) ?_ ?_ T ?_]
        · refine Finset.sum_congr rfl fun t _ => ?_
          congr 1
          change ∏ j, μ j (t j) (Function.update A i (SmRep.ofIrr c.rep) j) = _
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
          congr 1
          · exact jhMult_rep_rep _ _
          · exact Finset.prod_congr rfl fun j hj => by
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        · intro j hj
          rcases eq_or_ne j i with rfl | hji
          · exact ⟨c, Function.update_self ..⟩
          · rw [Function.update_of_ne hji]
            exact hA j (by simp [hji, hj])
        · intro j
          rcases eq_or_ne j i with rfl | hji
          · rw [Function.update_self]; exact c.rep.hasFiniteLength
          · rw [Function.update_of_ne hji]; exact hl j
        · intro t ht
          obtain ⟨j, hj⟩ := hT t ht
          refine ⟨j, ?_⟩
          change μ j (t j) (Function.update A i (SmRep.ofIrr c.rep) j) = 0
          rcases eq_or_ne j i with rfl | hji
          · rw [Function.update_self]
            refine (jhMult_rep_rep _ _).trans (if_neg ?_)
            rintro rfl
            exact (hC.mem_toFinset.1 hc) hj
          · rw [Function.update_of_ne hji]; exact hj
      rw [h1, Finset.sum_congr rfl fun c hc => by rw [h2 c hc, Finset.mul_sum], Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      change _ = (∏ j, μ j (t j) (A j)) * _
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq]
      split_ifs with h
      · exact (mul_assoc _ _ _).symm
      · have : μ i (t i) (A i) = 0 := by simpa using h
        rw [this, zero_mul, zero_mul]
  exact fun A hl T hT => key Finset.univ A (fun i hi => absurd (Finset.mem_univ i) hi) hl T hT

end GlobalTheory.SmGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryConjugateDual
section
open GlobalTheory.PRep

namespace GlobalTheory.SmoothRiesz

theorem surjective_of_injective {F : Type} [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (T : F →ₛₗ[starRingEnd ℂ] Module.Dual ℂ F) (hT : ∀ x, T x = 0 → x = 0) : Function.Surjective T := by
  let b := Module.finBasis ℂ F
  have key : ∀ c : Fin (Module.finrank ℂ F) → ℂ,
      T (∑ i, starRingEnd ℂ (c i) • b i) = ∑ i, c i • T (b i) := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, Complex.conj_conj]
  have hli : LinearIndependent ℂ fun i => T (b i) := by
    refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
    have h := Fintype.linearIndependent_iff.1 b.linearIndependent _ (hT _ ((key c).trans hc)) i
    simpa using h
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by simp)
  intro l
  have hl : l ∈ Submodule.span ℂ (Set.range fun i => T (b i)) := hsp ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hl
  exact ⟨_, (key c).trans hc⟩

def stabiliser {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := fun {a b} ha hb => by
    show ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' := fun {a} ha => by
    show ρ a⁻¹ v = v
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul]; simp

theorem exists_conj_smoothDual : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsAdmissible ρ → GlobalTheory.LGrp.IsUnitarisable ρ → ∃ φ : V →ₛₗ[starRingEnd ℂ] smoothPart ρ.dual, Function.Bijective φ ∧ ∀ g x, φ (ρ g x) = GlobalTheory.LGrp.smoothDual ρ g (φ x) := by
  intro G _ _ _ K hKo hKc V _ _ ρ hρ hU
  obtain ⟨B, -, hpos, hinv⟩ := hU
  have hadj : ∀ g v x, B (ρ g⁻¹ v) x = B v (ρ g x) := by
    intro g v x
    rw [← hinv g, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hnd : ∀ x, B x x = 0 → x = 0 := fun x hx => by
    by_contra h
    have := hpos x h
    rw [hx] at this
    simp at this
  have hsm : ∀ x, B.flip x ∈ smoothPart ρ.dual := by
    intro x
    refine (stabiliser ρ.dual (B.flip x)).isOpen_of_mem_nhds (g := 1)
      (Filter.mem_of_superset ((hρ.1 x).mem_nhds (by simp)) fun g hg => ?_)
    have hg' : ρ g x = x := hg
    refine LinearMap.ext fun v => ?_
    show B (ρ g⁻¹ v) x = B v x
    rw [hadj, hg']
  refine ⟨B.flip.codRestrict _ hsm, ⟨?_, ?_⟩, fun g x => Subtype.ext (LinearMap.ext fun v => (hadj g v x).symm)⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => hnd x ?_
    exact LinearMap.congr_fun (congrArg Subtype.val hx) x
  · intro l
    let U : Subgroup G := stabiliser ρ.dual l.1 ⊓ K
    have hUo : IsOpen (U : Set G) := IsOpen.inter l.2 hKo
    have hUc : IsCompact (U : Set G) :=
      hKc.of_isClosed_subset (U.isClosed_of_isOpen hUo) fun _ h => h.2
    haveI := hρ.2 U hUo hUc
    let T : fixed ρ U →ₛₗ[starRingEnd ℂ] Module.Dual ℂ (fixed ρ U) :=
      (B.domRestrict₁₂ (fixed ρ U) (fixed ρ U)).flip
    obtain ⟨x, hx⟩ := surjective_of_injective T
      (fun x hx => Subtype.ext (hnd x (LinearMap.congr_fun hx x))) (l.1 ∘ₗ (fixed ρ U).subtype)
    refine ⟨x, Subtype.ext ?_⟩
    show B.flip x = l.1
    rw [← sub_eq_zero, ← LinearMap.ker_eq_top, eq_top_iff,
      ← (GlobalTheory.LocGL.isCompl_fixed_twKer hρ.1 hUc).sup_eq_top]
    refine sup_le (fun v hv => ?_) (Submodule.span_le.2 ?_)
    · exact sub_eq_zero.2 (LinearMap.congr_fun hx ⟨v, hv⟩)
    · rintro _ ⟨u, v, rfl⟩
      have h1 : l.1 (ρ u v) = l.1 v := by
        have := LinearMap.congr_fun (show ρ.dual (u : G)⁻¹ l.1 = l.1 from (U.inv_mem u.2).1) v
        rw [← this]
        show _ = l.1 (ρ (u : G)⁻¹⁻¹ v)
        rw [inv_inv]
      have h2 : B (ρ u v) x = B v x := by
        rw [← inv_inv (u : G), hadj, GlobalTheory.LGrp.mem_fixed.1 x.2 _ (U.inv_mem u.2)]
      simp [h1, h2]

end GlobalTheory.SmoothRiesz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainParOfNodeGap
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.IndefR.Links Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.WeilSignShift (NcGapGt NcGapGe minSig lamS lamT StepGap)
open GlobalTheory.Chain.ItPairCompare GlobalTheory.Chain.ParOfSizes

namespace GlobalTheory.Chain.ParOfNodeGap

theorem minSig_lamS_le {D : D7} (k : Fin D.R.m) (τ : D.what₂.Tau) : minSig (lamS D k τ) ≤ D.R.m := by
  unfold minSig
  refine (min_le_right _ _).trans ?_
  calc ((lamS D k τ).filter fun x => x.2 = false).card
      ≤ (Finset.univ.image fun i : Fin D.R.m =>
          ((val (D.hc τ) (k : ℕ) (Sum.inr (Sum.inl i)) + (D.hc τ).e k : ℚ), false)).card := by
        apply Finset.card_le_card
        rintro ⟨a, s⟩ hx
        rw [Finset.mem_filter] at hx
        obtain ⟨hx, hs⟩ := hx
        simp only at hs
        subst hs
        obtain ⟨y, hy, hsy⟩ := (mem_lamS k τ a false).1 hx
        rcases y with y | y | y
        · simp [sgn] at hsy
        · exact Finset.mem_image.2 ⟨y, Finset.mem_univ _, by rw [hy]⟩
        · simp [sgn] at hsy
    _ ≤ (Finset.univ : Finset (Fin D.R.m)).card := Finset.card_image_le
    _ = D.R.m := by simp

theorem num_bound' {n q m N : ℕ} (hq : q ≤ m) (hn : n ≤ N) (hm : 2 ≤ m) (hN : 3 * m ^ 2 ≤ N) :
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 4 * (N : ℝ) ^ 3 := by
  have hqm : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    have h1 : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ (2 : ℕ) := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h
        rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
        positivity
      · rw [← Real.rpow_natCast]
        apply Real.rpow_le_rpow_of_exponent_le
        · exact Nat.one_le_cast.mpr h
        · norm_num
    refine h1.trans ?_
    have : (q : ℝ) ≤ m := by exact_mod_cast hq
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
  have hnR : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hNR : 3 * (m : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hN12 : (12 : ℝ) ≤ N := by nlinarith
  have hpos : (0 : ℝ) ≤ (q : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (N : ℝ) * (m : ℝ) ^ 2 :=
        mul_le_mul (by linarith) hqm hpos (by positivity)
    _ ≤ 120 * (N : ℝ) * ((N : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 40 * (N : ℝ) ^ 2 := by ring
    _ ≤ 4 * (N : ℝ) ^ 3 := by nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) (by linarith : (0 : ℝ) ≤ N - 10)]

private theorem le_sub_b_succ_of_nodeGap {D : D7} {h : ℝ} (H : D.NodeGap h) (τ : D.what₂.Tau) :
    ∀ (i : ℕ) (hi : i + 1 < D.R.m), h ≤ (((D.hc τ).b ⟨i + 1, hi⟩ - (D.hc τ).b ⟨i, by omega⟩ : ℚ) : ℝ) := by
  intro i hi
  have := H D.u₀ τ i hi
  rwa [D.hcW_base] at this

private theorem rankY_le_N (D : D7) {j : ℕ} (hj : j ≤ D.R.m) : D.R.rankY j ≤ D.R.N D.R.m := by
  have h1 : j * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul hj le_rfl
  simp only [Ranks.rankY, Ranks.r, Ranks.N]
  rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem three_mul_m_sq_le_N (D : D7) : 3 * D.R.m ^ 2 ≤ D.R.N D.R.m := by
  have h1 : 3 * D.R.m + 1 ≤ D.R.t := D.R.three_m_lt_t
  have h2 : D.R.m * (3 * D.R.m + 1) ≤ D.R.m * D.R.t := Nat.mul_le_mul le_rfl h1
  simp only [Ranks.N]
  nlinarith

theorem stepGap_of_nodeGap {D : D7} (h : D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6))
    (k : Fin D.R.m) : StepGap D k := by
  set H : ℝ := 4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6 with hH
  have hg := le_sub_b_succ_of_nodeGap h
  have hNpos : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcube : ∀ j : ℕ, j ≤ D.R.m → ((D.R.rankY j : ℕ) : ℝ) ^ 3 < H := by
    intro j hj
    have : ((D.R.rankY j : ℕ) : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) := by exact_mod_cast rankY_le_N D hj
    have : ((D.R.rankY j : ℕ) : ℝ) ^ 3 ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) this 3
    have : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    nlinarith [pow_nonneg hNpos 3]
  intro τ
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ y s').1 hy
    exact (hcube _ (Nat.succ_le_of_lt k.isLt)).trans_le (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamT k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamT k τ y s').1 hy
    exact (hcube _ (Nat.succ_le_of_lt k.isLt)).trans_le (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
  · rintro ⟨x, s⟩ hx ⟨y, s'⟩ hy hne
    obtain ⟨a, rfl, rfl⟩ := (mem_lamS k τ x s).1 hx
    obtain ⟨b, rfl, rfl⟩ := (mem_lamS k τ y s').1 hy
    refine le_trans ?_ (le_val_sub (D.hc τ) (hg τ) _ _ a b hne)
    have hb := num_bound' (minSig_lamS_le k τ) (rankY_le_N D k.isLt.le) D.R.two_le_m (three_mul_m_sq_le_N D)
    have : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith

theorem chainPar_of_nodeGap :
    ∀ D : D7, D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6) → ∀ k, GlobalTheory.Chain.ChainPar D k := by
  intro D h k
  exact (chainPar_iff_stepGap k).mpr (stepGap_of_nodeGap h k)

end GlobalTheory.Chain.ParOfNodeGap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepCharactersEqGridRowZeroRanks
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GridJoin

theorem arrS_cast_weil_vac {D : D7} {S S' T T' : Node D} (hS : S = S') (hT : T = T') (a : ArrS S T)
    (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS χT : (AE D)ˣ →* Circle) {α : Type} (ω' : α)
    (hw : IsWeil ψ false S.V T.V χS χT a.ω) (hv : IsVac ψ θ false S T a.vac) (ho : HEq a.ω ω') :
    IsWeil ψ false S'.V T'.V χS χT (a.cast hS hT).ω ∧ IsVac ψ θ false S' T' (a.cast hS hT).vac ∧
      HEq (a.cast hS hT).ω ω' := by
  subst hS hT
  exact ⟨hw, hv, ho⟩

theorem chainStepCharacters_eq_gridRowZero_ranks {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (t : T) (j : ℕ) :
    Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1) =
      (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j), GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
  have hr : Odd D.R.r := by
    have h1 := D.R.k_even; have h2 := D.R.m_even; have h3 := D.R.two_le_m
    unfold Ranks.r; grind
  rw [Lift.chrStep_eq_att _ _ hr D.R.t_odd (Nat.le_add_left 1 j)]
  simp [rkV]

theorem testGridRowZeroArrows_weil_vacua_agree : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ (t : T) j, j < D.R.m → GlobalTheory.Grid.IsWeil R.ψ false (GlobalTheory.Grid.row0 R j).V (GlobalTheory.Grid.row0 R (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j)) (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (GlobalTheory.Grid.th0 R t j).ω ∧ GlobalTheory.Grid.IsVac R.ψ R.θ false (GlobalTheory.Grid.row0 R j) (GlobalTheory.Grid.row0 R (j + 1)) (GlobalTheory.Grid.th0 R t j).vac ∧ HEq (GlobalTheory.Grid.th0 R t j).ω (W.om (.mu t 0 j)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _ _ _ F hR _ G' W hW G _ _ _ _ t j hj
  have hc := chainStepCharacters_eq_gridRowZero_ranks R t j
  by_cases h : j + 1 < D.R.m
  · have hw : IsWeil R.ψ false (nodeY R j).V (nodeY R (j + 1)).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j))
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (stepY R t j).ω := by
      have := hR.chain.ωY t j h
      rw [hc] at this
      exact (isWeil_false _ _ _ _ _ _).2 this
    have hv : IsVac R.ψ R.θ false (nodeY R j) (nodeY R (j + 1)) (stepY R t j).vac := (hR.chain.vY t j h).1
    have key := arrS_cast_weil_vac (nodeY_eq_chainVertexAtRowZero_of_lt R (by omega)) (nodeY_eq_chainVertexAtRowZero_of_lt R h) (stepY R t j) R.ψ R.θ _ _ (W.om (.mu t 0 j)) hw hv
      (hW.omY t j h).symm
    unfold th0
    rw [dif_pos h]
    exact key
  · have h' : j + 1 = D.R.m := by omega
    have hw : IsWeil R.ψ false (nodeY R (D.R.m - 1)).V (nodeX R).V (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j))
        (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) (stepX R t).ω := by
      have hc' : Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m =
          (GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 j), GlobalTheory.Grid.GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
        rw [← h']; exact hc
      have := hR.chain.ωX t
      rw [hc'] at this
      exact (isWeil_false _ _ _ _ _ _).2 this
    have hv : IsVac R.ψ R.θ false (nodeY R (D.R.m - 1)) (nodeX R) (stepX R t).vac := (hR.chain.vX t).1
    have key := arrS_cast_weil_vac (nodeY_pred_eq_chainVertexAtRowZero_last R h') (nodeX_eq_chainVertexAtRowZero_of_ge R h) (stepX R t) R.ψ R.θ _ _ (W.om (.mu t 0 j)) hw hv
      (hW.omX t j h').symm
    unfold th0
    rw [dif_neg h, dif_pos h']
    exact key

end GlobalTheory.GridJoin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrientedHeis

theorem compAt_mt_of_mem_GfC {D : D7} (θ : InfFam D) (V : HSp D) {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V k) = 1 := by
  rw [GfC, MonoidHom.mem_ker] at hk
  unfold compAt Formalism.L2.Theta.mt
  unfold infHom at hk
  unfold infPart
  rw [MonoidHom.comp_apply] at hk
  have e := congrArg (fun g => (Units.val g).map (θ τ)) hk
  simp only [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)] at e
  rw [← e]
  rfl

theorem om_fin_pureTensorO : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ κ ∈ GfC S, ∀ κ' ∈ GfC T, ∀ sS sT BS BT f P, IsThetaFunO ψ S T f → om (κ, κ') (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (om (κ, κ') f) P := by
  intro D ψ S T χS χT om hW θ hθ κ hκ κ' hκ' sS sT BS BT f P hf
  have h1 := fun τ => compAt_mt_of_mem_GfC θ S hκ τ
  have h2 := fun τ => compAt_mt_of_mem_GfC θ T hκ' τ
  have := (om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT κ κ' (fun τ => by rw [h1 τ, one_mul, mul_one]) (fun τ => by rw [h2 τ, one_mul, mul_one]) (fun τ => by rw [h1 τ, one_mul]) (fun τ => by rw [h2 τ, one_mul]) f hf P).2
  exact this

end GlobalTheory.OrientedHeis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingIntegralJointHarmonicPosStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingIntegral_jointHarmonic_pos : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → DiscreteSeriesPositivity X → admQ5 X → CoverHaarIntegration X → admQ7 → admQ8 → ArchimedeanRallisFirst X := by
  first | exact @GlobalTheory.DoublingPos.doubling_pos | exact GlobalTheory.DoublingPos.doubling_pos | (intros; apply GlobalTheory.DoublingPos.doubling_pos <;> assumption)
end

