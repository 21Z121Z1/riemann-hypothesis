import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0011

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExistsOfMemSmulLat
section
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section G

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem exists_of_mem_smulLat {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {c : E} {abelian₂ : Submodule M.L.O V} {x : V} (hx : x ∈ H.smulLat c abelian₂) : ∃ l ∈ abelian₂, x = c • l := by
  unfold Formalism.MainNotions.S.Loc.HermSp.smulLat at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨l, hl, rfl⟩
  | zero => exact ⟨0, abelian₂.zero_mem, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨l, hl, rfl⟩ := hy
    obtain ⟨m, hm, rfl⟩ := hz
    exact ⟨l + m, abelian₂.add_mem hl hm, by simp [smul_add]⟩
  | smul a y _ hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact ⟨a • l, abelian₂.smul_mem a hl, smul_comm a c l⟩

def Lemma0G (M : Model F E) (r : ℕ) : Prop :=
  ∀ g : SplitG M.L, M.split = some g →
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r),
    H.IsGeneric t → ∀ (w : V) (hw : w ∈ H.W0 t.f t.f'),
      (w ∈ t.abelian₂ ↔ (H.mkW t.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩ ∈ H.Lset t.abelian₂ t.f ∧
        H.mkW t.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩ ∈ H.Lset t.abelian₂ t.f' ∧
        (H.mkW t.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, H.mkW t.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩) ∈ H.iotaGraph g t))

theorem lemma0G_holds (M : Model F E) (r : ℕ) : Lemma0G M r := by
  intro g hg V _ _ H t hgen w hw
  constructor
  · intro hwL
    refine ⟨⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩, hwL, rfl⟩, ⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, hwL, rfl⟩, ?_⟩
    refine ⟨⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H hw⟩, ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩, hwL, hwL, ?_, rfl⟩
    simp only [sub_self]
    exact Submodule.zero_mem _
  · rintro ⟨-, -, x', x, hx'L, hxL, hxx, hp⟩
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hp1, hp2⟩ := hp
    simp only [HermSp.mkW, Submodule.mkQ_apply] at hp1 hp2

    have ha' : w - (x' : V) ∈ H.X t.f' := by
      simpa [Submodule.mem_comap] using (Submodule.Quotient.eq _).1 hp1
    have ha : w - (x : V) ∈ H.X t.f := by
      simpa [Submodule.mem_comap] using (Submodule.Quotient.eq _).1 hp2
    obtain ⟨α', hα'⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ha'
    obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 ha
    obtain ⟨l, hl, hxl⟩ := exists_of_mem_smulLat H hxx
    have hq0 : (g.q : F) ≠ 0 := fun h0 => g.q_irr.ne_zero (by exact_mod_cast h0)
    have hqqi : algebraMap F E (g.q : F) * algebraMap F E ((g.q : F)⁻¹) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hq0, map_one]
    have hqiq : algebraMap F E ((g.q : F)⁻¹) * algebraMap F E (g.q : F) = 1 := by
      rw [mul_comm, hqqi]
    have hMM : H.MMfam t =
        Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
      simp only [HermSp.MMfam, hg]
    obtain ⟨-, hli, hprim⟩ := hgen.2
    rw [hMM] at hli hprim

    let γ : Fin (r + 1) ⊕ Fin (r + 1) → E := Sum.elim
      (Fin.snoc (fun i => algebraMap F E ((g.q : F)⁻¹) * (α' i - α i)) 0) (Fin.snoc α' 0)
    have hsum : ∑ j, γ j • Sum.elim t.f
        (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j = l := by
      have key : algebraMap F E (g.q : F) • ∑ j, γ j • Sum.elim t.f
          (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j =
          algebraMap F E (g.q : F) • l := by
        rw [← hxl, Fintype.sum_sum_type]
        simp only [γ, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
          Fin.snoc_last, zero_smul, add_zero, smul_add, Finset.smul_sum]
        have e1 : (x : V) - x' = (w - x') - (w - x) := by abel
        rw [e1, ← hα', ← hα, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, ← mul_assoc, hqqi, one_mul, smul_comm (algebraMap F E (g.q : F)) (α' i),
          smul_smul (algebraMap F E (g.q : F)), hqqi, one_smul, sub_smul, smul_sub]
        abel
      calc _ = (algebraMap F E ((g.q : F)⁻¹) * algebraMap F E (g.q : F)) • ∑ j, γ j • Sum.elim t.f
              (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j := by
            rw [hqiq, one_smul]
        _ = l := by rw [mul_smul, key, ← mul_smul, hqiq, one_smul]
    have hlO := hprim l hl ((Submodule.mem_span_range_iff_exists_fun E).2 ⟨γ, hsum⟩)
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 hlO
    have hβ' : ∑ j, (β j : E) • Sum.elim t.f
        (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) j = l := by
      simpa only [Subring.smul_def] using hβ
    have hzero := Fintype.linearIndependent_iff.1 hli (fun j => (β j : E) - γ j) (by
      simp only [sub_smul, Finset.sum_sub_distrib, hβ', hsum, sub_self])

    have hmem : ∀ i : Fin r, α' i ∈ M.L.O := by
      intro i
      have := hzero (Sum.inr i.castSucc)
      simp only [γ, Sum.elim_inr, Fin.snoc_castSucc, sub_eq_zero] at this
      rw [← this]
      exact (β _).2
    have hf'L := hgen.1.2.2.1.1.1
    have hw' : w = (x' : V) + ∑ i, α' i • t.f' i.castSucc := by rw [hα']; abel
    rw [hw']
    refine t.abelian₂.add_mem hx'L (Submodule.sum_mem _ fun i _ => ?_)
    have := t.abelian₂.smul_mem (⟨α' i, hmem i⟩ : M.L.O) (hf'L i.castSucc)
    simpa only [Subring.smul_def] using this

end G

end Formalism.L2.SG.LsDatumA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNE
section
noncomputable section

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA

variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem main (X : Submodule E S.V) (hXiso : ∀ x ∈ X, ∀ y ∈ X, S.hT x y = 0) (z : S.V) (hzX : z ∈ orth S X)
    (Λ Λ₂ : Submodule (𝓞 E) S.V) (hΛ : Submodule.IsLattice E Λ) (hΛ₂ : Submodule.IsLattice E Λ₂)
    (hSD : SD S Λ) (hSD₂ : SD S Λ₂) (hX : ∀ x ∈ X, x ∈ Λ₂ ↔ x ∈ Λ) (hz : z ∈ Λ) (hz₂ : z ∈ Λ₂)
    (hL : ∀ x ∈ Λ₂, x ∈ orth S X → ∃ y ∈ Λ, y - x ∈ X)
    (hL' : ∀ y ∈ Λ, y ∈ orth S X → ∃ x ∈ Λ₂, x ∈ orth S X ∧ y - x ∈ X)
    (hy : ∃ y ∈ Λ₂, y ∈ orth S X ∧ S.hT y z = 1) (htr : ∃ c : E, IsIntegral ℤ c ∧ c + star c = 1) :
    ∃ n : S.V ≃ₗ[E] S.V, (∀ a b, S.hT (n a) (n b) = S.hT a b) ∧ (∀ x ∈ X, n x = x) ∧ n z = z ∧
      (∀ x ∈ orth S X, n x - x ∈ X) ∧ (n : S.V → S.V) '' Λ₂ = Λ := by
  classical
  have hXo := X_le_orth S X hXiso
  obtain ⟨A, hAX, hA0, hAz, hAΛ⟩ :=
    stepB S X hXiso z hzX Λ Λ₂ hΛ₂ hSD₂ (fun x hx h => (hX x hx).1 h) hz hz₂ hL hy
  obtain ⟨g, hg, hgA⟩ := stepW S X hXiso A hAX hA0
  have hgX : ∀ x ∈ X, g x = x := fun x hx => by
    have e : g x = x + A ⟨x, hXo hx⟩ := hgA ⟨x, hXo hx⟩
    rw [e, hA0 ⟨x, hXo hx⟩ hx, add_zero]
  let Λ₃ : Submodule (𝓞 E) S.V := Λ₂.map ((g : S.V →ₗ[E] S.V).restrictScalars (𝓞 E))
  have hmem₃ : ∀ x, x ∈ Λ₃ ↔ g.symm x ∈ Λ₂ := fun x => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨g.symm x, h, by simp⟩
  have hfg₃ : Λ₃.FG := hΛ₂.fg.map _
  have hfull₃ : ∀ u : S.V, ∃ d : 𝓞 E, d ≠ 0 ∧ d • u ∈ Λ₃ := fun u => by
    obtain ⟨d, hd, hdu⟩ := PI.UnitaryGroupMassFormula.BetaLUniq.exists_smul_mem S Λ₂ hΛ₂ (g.symm u)
    refine ⟨d, hd, (hmem₃ _).2 ?_⟩
    rw [oSmul, map_smul, ← oSmul]
    exact hdu
  have hSD₃ : SD S Λ₃ := fun x => by
    rw [hmem₃, hSD₂]
    constructor
    · intro h y hy
      have := h (g.symm y) ((hmem₃ y).1 hy)
      rwa [← hg (g.symm y) (g.symm x), g.apply_symm_apply, g.apply_symm_apply] at this
    · intro h y hy
      rw [← hg y (g.symm x), g.apply_symm_apply]
      exact h (g y) ((hmem₃ _).2 (by simpa using hy))
  have hM : ∀ x ∈ orth S X, x ∈ Λ₃ ↔ x ∈ Λ := fun x hx => by
    rw [hmem₃]
    constructor
    · intro h
      obtain ⟨l, rfl⟩ : ∃ l, g l = x := ⟨g.symm x, g.apply_symm_apply x⟩
      rw [g.symm_apply_apply] at h
      have hlo : l ∈ orth S X := (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth S).2 fun x' hx' => by
        rw [← hg x' l, hgX x' hx']
        exact orth_X S hx hx'
      have e : g l = l + A ⟨l, hlo⟩ := hgA ⟨l, hlo⟩
      rw [e]
      exact hAΛ l hlo h
    · intro h
      obtain ⟨x₂, hx₂, hx₂o, hxx₂⟩ := hL' x h hx
      have hAx₂ := hAΛ x₂ hx₂o hx₂
      obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = x - (x₂ + A ⟨x₂, hx₂o⟩) := ⟨_, rfl⟩
      have hξX : ξ ∈ X := by
        have e : ξ = (x - x₂) - A ⟨x₂, hx₂o⟩ := by rw [hξ]; abel
        rw [e]
        exact X.sub_mem hxx₂ (hAX _)
      have hξΛ : ξ ∈ Λ := by rw [hξ]; exact Λ.sub_mem h hAx₂
      have hξΛ₂ : ξ ∈ Λ₂ := (hX ξ hξX).2 hξΛ
      have hlo : x₂ + ξ ∈ orth S X := (orth S X).add_mem hx₂o (hXo hξX)
      have e : g (x₂ + ξ) = x := by
        have h1 : g (x₂ + ξ) = (x₂ + ξ) + A ⟨x₂ + ξ, hlo⟩ := hgA ⟨x₂ + ξ, hlo⟩
        have h2 : A ⟨x₂ + ξ, hlo⟩ = A ⟨x₂, hx₂o⟩ + A ⟨ξ, hXo hξX⟩ := by
          rw [← map_add]
          rfl
        rw [h1, h2, hA0 ⟨ξ, hXo hξX⟩ hξX, add_zero, hξ]
        abel
      rw [← e, g.symm_apply_apply]
      exact Λ₂.add_mem hx₂ hξΛ₂
  obtain ⟨n₂, hn₂, hn₂o, hn₂img⟩ := stepD S X hXiso Λ Λ₃ hΛ hSD hfg₃ hfull₃ hSD₃ hM htr
  refine ⟨g.trans n₂, fun a b => ?_, fun x hx => ?_, ?_, fun x hx => ?_, ?_⟩
  · show S.hT (n₂ (g a)) (n₂ (g b)) = S.hT a b
    rw [hn₂, hg]
  · show n₂ (g x) = x
    rw [hgX x hx, hn₂o x (hXo hx)]
  · have e : g z = z + A ⟨z, hzX⟩ := hgA ⟨z, hzX⟩
    show n₂ (g z) = z
    rw [e, hAz, add_zero, hn₂o z hzX]
  · have e : g x = x + A ⟨x, hx⟩ := hgA ⟨x, hx⟩
    have ho : g x ∈ orth S X := by rw [e]; exact (orth S X).add_mem hx (hXo (hAX _))
    show n₂ (g x) - x ∈ X
    rw [hn₂o _ ho, e, add_sub_cancel_left]
    exact hAX _
  · have h3 : (g : S.V → S.V) '' (Λ₂ : Set S.V) = (Λ₃ : Set S.V) := by
      rw [Submodule.map_coe]
      rfl
    have e : ((g.trans n₂ : S.V ≃ₗ[E] S.V) : S.V → S.V) = n₂ ∘ g := rfl
    rw [e, Set.image_comp, h3, hn₂img]

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNA
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvOfVolLocPos
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.ProdConvCut

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)

def VolOneAEC : Prop :=
  {v : PlX X | ¬ (localVolumeUnit X ψ v = 1 ∧ ZZX X u u' ψ v = 1 ∧ (∀ l, PPX X u u' ψ l v = 1) ∧ jacX X v = 1)}.Finite

def MXAE : Prop := {v : PlX X | MX X u u' ψ v ≠ alX X u u' v}.Finite

private theorem multipliable_and_tprod_pos_of_finite_ne_one {α : Type*} (f : α → ℝ) (hpos : ∀ a, 0 < f a)
    (hfin : {a | ¬ f a = 1}.Finite) : Multipliable f ∧ 0 < ∏' a, f a := by
  have hs : ∀ b ∉ hfin.toFinset, f b = 1 := by
    intro b hb
    by_contra hne
    exact hb (hfin.mem_toFinset.2 hne)
  refine ⟨?_, ?_⟩
  · first
    | exact multipliable_of_ne_finset_one hs
    | exact (hasProd_prod_of_ne_finset_one hs).multipliable
  · rw [tprod_eq_prod hs]
    exact Finset.prod_pos (fun a _ => hpos a)

theorem prodConv_of_vol_locPos (h1 : VolOneAEC X u u' ψ) (hM : MXAE X u u' ψ) (h2 : LocPosC X u u' ψ) (h3 : AlConvC X u u') :
    ProdConv X u u' ψ := by
  unfold VolOneAEC at h1
  unfold LocPosC at h2
  unfold AlConvC at h3
  have hU := multipliable_and_tprod_pos_of_finite_ne_one (fun v : OrdX X => localVolumeUnit X ψ v.1) (fun v => (h2 v.1).2.1)
    (Set.Finite.preimage Subtype.val_injective.injOn
      (h1.subset (fun v (hv : ¬ localVolumeUnit X ψ v = 1) hall => hv hall.1)))
  have hZ := multipliable_and_tprod_pos_of_finite_ne_one (ZZX X u u' ψ) (fun v => (h2 v).2.2.1)
    (h1.subset (fun v hv hall => hv hall.2.1))
  have hP : ∀ l, Multipliable (PPX X u u' ψ l) ∧ 0 < ∏' v : PlX X, PPX X u u' ψ l v := fun l =>
    multipliable_and_tprod_pos_of_finite_ne_one (PPX X u u' ψ l) (fun v => (h2 v).2.2.2.1 l)
      (h1.subset (fun v hv hall => hv (hall.2.2.1 l)))
  have hJ := multipliable_and_tprod_pos_of_finite_ne_one (jacX X) (fun v => (h2 v).2.2.2.2.2)
    (h1.subset (fun v hv hall => hv hall.2.2.2))
  unfold ProdConv
  exact ⟨fun v => ⟨fun _ => (h2 v).1, (h2 v).2.1, (h2 v).2.2.1, (h2 v).2.2.2.1, (h2 v).2.2.2.2.1⟩,
    trivial, trivial, hU.1, hU.2, hZ.1, hZ.2, hP, h3.1, h3.2, hJ.1, hJ.2⟩

end Formalism.L2.SG.Pf.ProdConvCut2
end
end

