import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0009
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0022
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0021
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.WeilBound.CoreStatements.HodgeTatePoints.GermCompOneAssocOfConstantCoeffZero
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeFibreIdealLocallyFree
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_annSub_iff {n k : ℕ} {v : Fin n → Ω} :
    v ∈ annSub Ω n k ↔ ∀ j : Fin n, (j : ℕ) < k → v j = 0 := by
  simp [annSub, Submodule.mem_pi]

def stepCoord (Ω : Type) [Field Ω] {n : ℕ} (i : Fin n) : annSub Ω n i →ₗ[Ω] Ω :=
  (LinearMap.proj i).comp (annSub Ω n i).subtype

theorem stepCoord_apply {n : ℕ} (i : Fin n) (v : annSub Ω n i) :
    stepCoord Ω i v = (v : Fin n → Ω) i := rfl

theorem stepCoord_surjective {n : ℕ} (i : Fin n) : Function.Surjective (stepCoord Ω i) := by
  classical
  intro c
  refine ⟨⟨Pi.single i c, mem_annSub_iff.2 fun j hj => ?_⟩, by simp [stepCoord_apply]⟩
  have : j ≠ i := by rintro rfl; exact lt_irrefl _ hj
  simp [Pi.single_apply, this]

theorem mem_ker_stepCoord {n : ℕ} (i : Fin n) (v : annSub Ω n i) :
    v ∈ LinearMap.ker (stepCoord Ω i) ↔ (v : Fin n → Ω) ∈ annSub Ω n ((i : ℕ) + 1) := by
  rw [LinearMap.mem_ker, stepCoord_apply, mem_annSub_iff]
  constructor
  · intro h j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact mem_annSub_iff.1 v.2 j hj
    · rw [Fin.ext hj]; exact h
  · intro h
    exact h i (Nat.lt_succ_self _)

theorem summand_step {n : ℕ} {L : AddSubgroup (Fin n → Ω)} (i : Fin n)
    (h : Summand L (annSub Ω n ((i : ℕ) + 1))) :
    Summand (L.comap (annSub Ω n i).subtype.toAddMonoidHom) (LinearMap.ker (stepCoord Ω i)) := by
  obtain ⟨ρ, h1, h2, h3⟩ := h
  have hle : ∀ v, ρ v ∈ annSub Ω n i := fun v =>
    mem_annSub_iff.2 fun j hj => mem_annSub_iff.1 (h1 v) j (Nat.lt_succ_of_lt hj)
  refine ⟨(ρ.comp (annSub Ω n i).subtype).codRestrict _ fun v => hle _, fun v => ?_, fun u hu => ?_,
    fun v hv => ?_⟩
  · rw [mem_ker_stepCoord]
    exact h1 _
  · apply Subtype.ext
    exact h2 _ ((mem_ker_stepCoord i u).1 hu)
  · exact h3 _ hv

theorem locFree_step (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)} (hL : LocFree R n L)
    (i : Fin n) (h₀ : Summand L (annSub Ω n i)) (h₁ : Summand L (annSub Ω n ((i : ℕ) + 1))) :
    LocFree R 1 ((L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i)) := by
  have hA := ((GlobalTheory.T.locally_free_summand_criterion R (annSub Ω n i) n 0 L hL).2 h₀).1
  have hB := ((GlobalTheory.T.locally_free_summand_criterion R (LinearMap.ker (stepCoord Ω i)) _ 0 _ hA).2 (summand_step i h₁)).2
  have hr : Module.finrank Ω (annSub Ω n i) - Module.finrank Ω (LinearMap.ker (stepCoord Ω i)) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (stepCoord Ω i)
    rw [LinearMap.range_eq_top.2 (stepCoord_surjective i), finrank_top, Module.finrank_self] at h
    omega
  rw [hr] at hB
  have hC := (locFree_map_mkQ_iff R (stepCoord Ω i) (stepCoord_surjective i) _).1 hB
  convert hC using 1
  ext c
  constructor
  · rintro ⟨v, ⟨hv, hv'⟩, rfl⟩
    exact ⟨⟨v, hv'⟩, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, ⟨hv, v.2⟩, rfl⟩

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, LocFree R 1 (D.dId R p (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ i, (D.bc RC).dId RC p (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hB h1 h2
  obtain ⟨hg, hbc⟩ := GlobalTheory.T.lattice_good_base_change D R p w χ hc hB h1
  refine ⟨fun τ i => locFree_step R (hg τ).1 i (h2.ann τ i) (h2.ann τ ((i : ℕ) + 1)), ?_⟩
  intro C _ _ _ _ RC hRC τ i
  have haf := ((hbc C RC hRC).2 τ).1
  have hs := (GlobalTheory.T.locally_free_base_change_summand R RC hRC (bcMap Ω C (Fin n)) (isBaseChange_bcMap Ω C _)
    (D.af R p (χ τ)) (annSub Ω n i) (hg τ).1.1 (h2.ann τ i)).2
  rw [span_bcMap_annSub] at hs
  unfold LieLatticeData.dId
  rw [haf, hs]
  have hm := SpanExact.map_spanOver RC
    (bcMap Ω C (Fin n) '' ((D.af R p (χ τ) ⊓ (annSub Ω n i).toAddSubgroup : AddSubgroup _) : Set (Fin n → Ω)))
    (LinearMap.proj i : (Fin n → C) →ₗ[C] C)
  have himg : algebraMap Ω C '' (((D.af R p (χ τ) ⊓ (annSub Ω n i).toAddSubgroup : AddSubgroup _).map
      (Pi.evalAddMonoidHom (fun _ => Ω) i) : AddSubgroup Ω) : Set Ω) =
      (LinearMap.proj i : (Fin n → C) →ₗ[C] C) '' (bcMap Ω C (Fin n) ''
        ((D.af R p (χ τ) ⊓ (annSub Ω n i).toAddSubgroup : AddSubgroup _) : Set (Fin n → Ω))) := by
    ext c
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  rw [himg, ← hm]
  rfl

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeGraphComapLocallyFree
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] {n : ℕ}
  {Sg : Type} {r s : Sg → ℕ}

theorem mem_stepGraph_iff (D : LieLatticeData Ω F n Sg r s) (τ : Sg) (χ : F → Ω) (i : Fin n) (c : Ω)
    (m : Fin (r τ) → Ω) :
    (c, m) ∈ D.stepGraph τ χ i ↔
      ∃ g u, (g, m) ∈ D.Th τ ∧ u ∈ vanSub Ω F n ((i : ℕ) + 1) ∧
        c • (fun x : Fin n → F => χ (x i)) = g + u := by
  unfold LieLatticeData.stepGraph
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_sup]
  constructor
  · rintro ⟨⟨g, m'⟩, hy, ⟨u, m''⟩, hz, he⟩
    obtain ⟨hu, hm⟩ := AddSubgroup.mem_prod.1 hz
    have hm0 : m'' = 0 := hm
    subst hm0
    have h1 : g + u = c • (fun x : Fin n → F => χ (x i)) := congrArg Prod.fst he
    have h2 : m' + 0 = m := congrArg Prod.snd he
    rw [add_zero] at h2
    subst h2
    exact ⟨g, u, hy, hu, h1.symm⟩
  · rintro ⟨g, u, hg, hu, he⟩
    refine ⟨(g, m), hg, (u, 0), AddSubgroup.mem_prod.2 ⟨hu, rfl⟩, ?_⟩
    exact Prod.ext he.symm (add_zero m)

theorem vanSub_apply_zero {i : ℕ} {u : (Fin n → F) → Ω} (hu : u ∈ vanSub Ω F n i) : u 0 = 0 := by
  have h := (Submodule.mem_pi.1 hu) (0 : Fin n → F) (fun _ _ => rfl)
  simpa using h

theorem stepGraph_stable [Fintype F] (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω} {p : ℕ} {w : Ω}
    (hB : D.Base R p w) (τ : Sg) (χ : F → Ω) (i : Fin n) :
    ∀ a ∈ R, ∀ v ∈ D.stepGraph τ χ i, a • v ∈ D.stepGraph τ χ i := by
  rintro a ha ⟨c, m⟩ h
  obtain ⟨g, u, hg, hu, he⟩ := (mem_stepGraph_iff D τ χ i c m).1 h
  refine (mem_stepGraph_iff D τ χ i (a • c) (a • m)).2
    ⟨a • g, a • u, (hB.stable τ a ha).2.2 (g, m) hg, Submodule.smul_mem _ _ hu, ?_⟩
  rw [smul_assoc, he, smul_add]

theorem fst_mem_xId_of_mem_stepGraph [Fintype F] (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω}
    {p : ℕ} {w : Ω} (hB : D.Base R p w) (τ : Sg) (χ : F → Ω) (i : Fin n) {c : Ω}
    {m : Fin (r τ) → Ω} (h : (c, m) ∈ D.stepGraph τ χ i) : c ∈ D.xId χ i := by
  obtain ⟨g, u, hg, hu, he⟩ := (mem_stepGraph_iff D τ χ i c m).1 h
  have hgM : g ∈ D.M := (((hB.th τ).1 g).1 ⟨m, hg⟩).1
  refine AddSubgroup.mem_comap.2 (AddSubgroup.mem_sup.2 ⟨g, hgM, u, hu, ?_⟩)
  exact he.symm

theorem exists_mem_stepGraph_of_mem_xId [Fintype F] (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω}
    {p : ℕ} {w : Ω} (hB : D.Base R p w) (τ : Sg) (χ : F → Ω) (h0 : χ 0 = 0) (i : Fin n) {c : Ω}
    (h : c ∈ D.xId χ i) : ∃ m, (c, m) ∈ D.stepGraph τ χ i := by
  obtain ⟨g, hg, u, hu, he⟩ := AddSubgroup.mem_sup.1 (AddSubgroup.mem_comap.1 h)
  have he' : g + u = c • (fun x : Fin n → F => χ (x i)) := he
  have hu0 : u 0 = 0 := vanSub_apply_zero hu
  have hg0 : g 0 = 0 := by
    have := congrFun he' 0
    simpa [h0, hu0] using this
  obtain ⟨m, hm⟩ := ((hB.th τ).1 g).2 ⟨hg, hg0⟩
  exact ⟨m, (mem_stepGraph_iff D τ χ i c m).2 ⟨g, u, hm, hu, he'.symm⟩⟩

theorem zero_mem_stepGraph_iff (D : LieLatticeData Ω F n Sg r s) (τ : Sg) (χ : F → Ω) (i : Fin n)
    (m : Fin (r τ) → Ω) : (0, m) ∈ D.stepGraph τ χ i ↔ m ∈ D.kk τ ((i : ℕ) + 1) := by
  rw [mem_stepGraph_iff]
  constructor
  · rintro ⟨g, u, hg, hu, he⟩
    rw [zero_smul] at he
    have hgu : g = -u := eq_neg_of_add_eq_zero_left he.symm
    refine ⟨(g, m), ⟨hg, AddSubgroup.mem_prod.2 ⟨?_, trivial⟩⟩, rfl⟩
    rw [hgu]
    exact neg_mem hu
  · rintro ⟨⟨g, m'⟩, ⟨hg, hp⟩, rfl⟩
    have hv : g ∈ vanSub Ω F n ((i : ℕ) + 1) := (AddSubgroup.mem_prod.1 hp).1
    refine ⟨g, -g, hg, neg_mem hv, ?_⟩
    simp

theorem stepKer : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, LocFree R 1 ((D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _))) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ i, ((D.bc RC).stepGraph τ (fun a => algebraMap Ω C (χ τ a)) i).comap (AddMonoidHom.inl _ _) = spanOver RC (algebraMap Ω C '' (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hχ hB hG1 hG2
  refine ⟨fun τ i => ?_, fun C _ _ _ _ RC hRC τ i => ?_⟩
  · have h0 : χ τ 0 = 0 := (hχ.2.2.2.2 τ).1
    exact (LocFreeSchanuel.main R 1 (r τ) (D.xId (χ τ) i)
      ((D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _)) (D.kk τ ((i : ℕ) + 1))
      (D.stepGraph τ (χ τ) i) (((GlobalTheory.T.lattice_good_base_change D R p w χ hχ hB hG1).1 τ).2.2.2 i) (hG2.step τ i)
      (hG2.kk τ _) (stepGraph_stable D hB τ (χ τ) i)
      (fun c m h => ⟨fst_mem_xId_of_mem_stepGraph D hB τ (χ τ) i h, ⟨(c, m), h, rfl⟩⟩)
      (fun c h => exists_mem_stepGraph_of_mem_xId D hB τ (χ τ) h0 i h)
      (zero_mem_stepGraph_iff D τ (χ τ) i)
      (by
        rintro _ ⟨⟨c, m⟩, h, rfl⟩
        exact ⟨c, h⟩)).2
  · have hst := stepGraph_stable D hB τ (χ τ) i
    rw [(GlobalTheory.T.kernel_graph_base_change_holds D R p w χ hχ hB hG1 C RC hRC τ).2 i]
    let sw := (AddEquiv.prodComm (M := Ω) (N := Fin (r τ) → Ω)).toAddMonoidHom
    let Δ' : AddSubgroup ((Fin (r τ) → Ω) × Ω) := (D.stepGraph τ (χ τ) i).map sw
    have hst' : ∀ a ∈ R, ∀ v ∈ Δ', a • v ∈ Δ' := by
      rintro a ha _ ⟨x, hx, rfl⟩
      exact ⟨a • x, hst a ha x hx, rfl⟩
    have hfst : Δ'.map (AddMonoidHom.fst _ _) =
        (D.stepGraph τ (χ τ) i).map (AddMonoidHom.snd _ _) := by
      rw [AddSubgroup.map_map]
      rfl
    have key := (GlobalTheory.T.locally_free_base_change_quotient R RC hRC (bcMap Ω C (Fin (r τ))) (Algebra.linearMap Ω C)
      (isBaseChange_bcMap Ω C _) (IsBaseChange.linearMap Ω C) Δ' ⊥ (r τ) hst'
      (hfst ▸ hG2.step τ i) bot_le (by
        intro a _ v hv
        rw [AddSubgroup.mem_bot] at hv ⊢
        rw [hv, smul_zero])).2
    have hsw := spanOver_swap RC (bcMap Ω C (Fin (r τ))) (Algebra.linearMap Ω C)
      (D.stepGraph τ (χ τ) i)
    have e1 : Δ'.comap (AddMonoidHom.inr _ _) =
        (D.stepGraph τ (χ τ) i).comap (AddMonoidHom.inl _ _) := by
      ext c
      constructor
      · rintro ⟨⟨c', m⟩, h, he⟩
        have h1 : m = 0 := congrArg Prod.fst he
        have h2 : c' = c := congrArg Prod.snd he
        subst h1 h2
        exact h
      · intro h
        exact ⟨_, h, rfl⟩
    have e2 : ∀ X : AddSubgroup (C × (Fin (r τ) → C)),
        (X.map (AddEquiv.prodComm (M := C) (N := Fin (r τ) → C)).toAddMonoidHom).comap
          (AddMonoidHom.inr _ _) = X.comap (AddMonoidHom.inl _ _) := by
      intro X
      ext c
      constructor
      · rintro ⟨⟨c', m⟩, h, he⟩
        have h1 : m = 0 := congrArg Prod.fst he
        have h2 : c' = c := congrArg Prod.snd he
        subst h1 h2
        exact h
      · intro h
        exact ⟨_, h, rfl⟩
    rw [hsw, e2, e1] at key
    exact key

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterLatticeKernelLocallyFree
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_dotDual_iff (R : Subalgebra o Ω) {m : ℕ} {L : AddSubgroup (Fin m → Ω)}
    {v : Fin m → Ω} : v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

theorem std_le_dual (R : Subalgebra o Ω) {m : ℕ} {A : AddSubgroup (Fin m → Ω)}
    (h : A ≤ stdLat R (Fin m)) : stdLat R (Fin m) ≤ dotDual R A := by
  intro v hv
  rw [mem_dotDual_iff]
  intro l hl
  have hl' := (LatticeGoodness.mem_stdLat R).1 (h hl)
  have hv' := (LatticeGoodness.mem_stdLat R).1 hv
  show ∑ i, l i * v i ∈ R
  exact sum_mem fun i _ => R.mul_mem (hl' i) (hv' i)

theorem smul_mem_std (R : Subalgebra o Ω) {m : ℕ} {A : AddSubgroup (Fin m → Ω)} {w : Ω}
    (h : mulLat w (stdLat R (Fin m)) ≤ A) {v : Fin m → Ω} (hv : v ∈ dotDual R A) :
    w • v ∈ stdLat R (Fin m) := by
  classical
  rw [LatticeGoodness.mem_stdLat]
  intro j
  have h0 : (Pi.single j 1 : Fin m → Ω) ∈ stdLat R (Fin m) := by
    rw [LatticeGoodness.mem_stdLat]
    intro k
    by_cases hk : k = j
    · subst hk; simpa using R.one_mem
    · simpa [Pi.single_apply, hk] using R.zero_mem
  have h1 : w • (Pi.single j 1 : Fin m → Ω) ∈ A := h (AddSubgroup.mem_map.2 ⟨_, h0, rfl⟩)
  have h2 := (mem_dotDual_iff R).1 hv _ h1
  simpa [smul_dotProduct] using h2

theorem core (R : Subalgebra o Ω) {a b c : ℕ} (W : AddSubgroup (Fin a → Ω))
    (O : AddSubgroup (Fin c → Ω)) (Gam : AddSubgroup ((Fin a → Ω) × (Fin b → Ω)))
    (Del : AddSubgroup ((Fin b → Ω) × (Fin c → Ω))) (H : AddSubgroup (Fin b → Ω)) (w : Ω)
    (hw0 : w ≠ 0) (fW : LocFree R a W) (fO : LocFree R c O) (fH : LocFree R b H)
    (hstd : stdLat R (Fin b) ≤ H) (hwv : ∀ v ∈ H, w • v ∈ stdLat R (Fin b))
    (fIm : LocFree R c ((Del ⊓ H.prod ⊤).map (AddMonoidHom.snd _ _)))
    (sG : ∀ x ∈ R, ∀ v ∈ Gam, x • v ∈ Gam) (sD : ∀ x ∈ R, ∀ v ∈ Del, x • v ∈ Del)
    (g1 : ∀ x, (∃ y, (x, y) ∈ Gam) ↔ w • x ∈ W) (g2 : ∀ y, (0, y) ∈ Gam ↔ y ∈ stdLat R _)
    (g3 : ∀ x, (x, 0) ∈ Gam ↔ x ∈ W)
    (d1 : ∀ y, (∃ z, (y, z) ∈ Del) ↔ w • y ∈ stdLat R _) (d3 : ∀ z, (0, z) ∈ Del ↔ z ∈ O)
    (d4 : ∀ y, (y, 0) ∈ Del ↔ ∃ x, (x, y) ∈ Gam) :
    LocFree R a ((Gam ⊓ (⊤ : AddSubgroup _).prod H).map (AddMonoidHom.fst _ _)) := by

  have hK : LocFree R b ((Del ⊓ H.prod ⊤).comap (AddMonoidHom.inl _ _)) := by
    refine (LocFreeSchanuel.main R b c H _ O (Del ⊓ H.prod ⊤) fH fIm fO ?_ ?_ ?_ ?_ ?_).2
    · intro x hx v hv
      obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hv
      refine AddSubgroup.mem_inf.2 ⟨sD x hx v h1, AddSubgroup.mem_prod.2 ⟨?_, trivial⟩⟩
      exact fH.1 x hx _ (AddSubgroup.mem_prod.1 h2).1
    · intro v z h
      exact ⟨(AddSubgroup.mem_prod.1 (AddSubgroup.mem_inf.1 h).2).1, AddSubgroup.mem_map.2 ⟨(v, z), h, rfl⟩⟩
    · intro v hv
      obtain ⟨z, hz⟩ := (d1 v).2 (hwv v hv)
      exact ⟨z, AddSubgroup.mem_inf.2 ⟨hz, AddSubgroup.mem_prod.2 ⟨hv, trivial⟩⟩⟩
    · intro z
      constructor
      · intro h
        exact (d3 z).1 (AddSubgroup.mem_inf.1 h).1
      · intro h
        exact AddSubgroup.mem_inf.2 ⟨(d3 z).2 h, AddSubgroup.mem_prod.2 ⟨H.zero_mem, trivial⟩⟩
    · intro z hz
      obtain ⟨⟨v, z'⟩, h, rfl⟩ := AddSubgroup.mem_map.1 hz
      exact ⟨v, h⟩
  have sG' : ∀ x ∈ R, ∀ v ∈ Gam ⊓ (⊤ : AddSubgroup _).prod H, x • v ∈ Gam ⊓ (⊤ : AddSubgroup _).prod H := by
    intro x hx v hv
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hv
    exact AddSubgroup.mem_inf.2 ⟨sG x hx v h1, AddSubgroup.mem_prod.2
      ⟨trivial, fH.1 x hx _ (AddSubgroup.mem_prod.1 h2).2⟩⟩

  have hG' : LocFree R (a + b) (Gam ⊓ (⊤ : AddSubgroup _).prod H) := by
    have e1 : (Gam ⊓ (⊤ : AddSubgroup _).prod H).comap
        (LinearMap.inl Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom = W := by
      ext x
      constructor
      · intro h
        exact (g3 x).1 (AddSubgroup.mem_inf.1 h).1
      · intro h
        exact AddSubgroup.mem_inf.2 ⟨(g3 x).2 h, AddSubgroup.mem_prod.2 ⟨trivial, H.zero_mem⟩⟩
    have e2 : (Gam ⊓ (⊤ : AddSubgroup _).prod H).map
        (LinearMap.snd Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom =
        (Del ⊓ H.prod ⊤).comap (AddMonoidHom.inl _ _) := by
      ext y
      constructor
      · intro h
        obtain ⟨⟨x, y'⟩, hxy, rfl⟩ := AddSubgroup.mem_map.1 h
        obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 hxy
        exact AddSubgroup.mem_inf.2 ⟨(d4 y').2 ⟨x, h1⟩,
          AddSubgroup.mem_prod.2 ⟨(AddSubgroup.mem_prod.1 h2).2, trivial⟩⟩
      · intro h
        obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 h
        obtain ⟨x, hx⟩ := (d4 y).1 h1
        exact AddSubgroup.mem_map.2 ⟨(x, y), AddSubgroup.mem_inf.2 ⟨hx,
          AddSubgroup.mem_prod.2 ⟨trivial, (AddSubgroup.mem_prod.1 h2).1⟩⟩, rfl⟩
    exact LocFreeExt.main R (LinearMap.inl Ω _ _) (LinearMap.snd Ω _ _) LinearMap.inl_injective
      LinearMap.snd_surjective (LinearMap.range_inl Ω _ _) _ a b sG' (e1 ▸ fW) (e2 ▸ hK)

  have eF : Gam.map (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom = divLat w W := by
    ext x
    constructor
    · intro h
      obtain ⟨⟨x', y⟩, hxy, rfl⟩ := AddSubgroup.mem_map.1 h
      exact (g1 x').1 ⟨y, hxy⟩
    · intro h
      obtain ⟨y, hy⟩ := (g1 x).2 h
      exact AddSubgroup.mem_map.2 ⟨(x, y), hy, rfl⟩
  have fDiv : LocFree R a (Gam.map (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom) :=
    eF ▸ LatticeGoodness.locFree_divLat R hw0 fW
  have hGam : LocFree R (b + a) Gam := by
    have e1 : Gam.comap (LinearMap.inr Ω (Fin a → Ω) (Fin b → Ω)).toAddMonoidHom = stdLat R (Fin b) := by
      ext y
      exact g2 y
    exact LocFreeExt.main R (LinearMap.inr Ω _ _) (LinearMap.fst Ω _ _) LinearMap.inr_injective
      LinearMap.fst_surjective (LinearMap.range_inr Ω _ _) _ b a sG
      (e1 ▸ LatticeGoodness.locFree_stdLat R b) fDiv

  have hfin : Module.finrank Ω (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω))) = b := by
    rw [← LinearMap.range_inr, LinearMap.finrank_range_of_inj LinearMap.inr_injective,
      Module.finrank_fin_fun]
  obtain ⟨ρ, hρ1, hρ2, hρ3⟩ := (GlobalTheory.T.locally_free_summand_criterion R (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)))
    (b + a) a Gam hGam).1
    ((LatticeGoodness.locFree_map_mkQ_iff R _ LinearMap.fst_surjective Gam).2 fDiv)
  have hS : Summand (Gam ⊓ (⊤ : AddSubgroup _).prod H)
      (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω))) := by
    refine ⟨ρ, hρ1, hρ2, fun v hv => ?_⟩
    have h1 := hρ3 v (AddSubgroup.mem_inf.1 hv).1
    have h2 : (ρ v).1 = 0 := hρ1 v
    refine AddSubgroup.mem_inf.2 ⟨h1, AddSubgroup.mem_prod.2 ⟨trivial, hstd ?_⟩⟩
    apply (g2 _).1
    have : ((0 : Fin a → Ω), (ρ v).2) = ρ v := by rw [← h2]
    rwa [this]
  have hfinal := ((GlobalTheory.T.locally_free_summand_criterion R (LinearMap.ker (LinearMap.fst Ω (Fin a → Ω) (Fin b → Ω)))
    (a + b) a _ hG').2 hS).2
  rw [hfin, Nat.add_sub_cancel] at hfinal
  exact (LatticeGoodness.locFree_map_mkQ_iff R _ LinearMap.fst_surjective _).1 hfinal

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ τ, LocFree R (r τ) (D.kerH R p τ (χ τ)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hC hB hG₁ hG₂ hw τ
  have hw0 : w ≠ 0 := by
    obtain ⟨c, -, hc⟩ := hC.2.2.1
    intro h
    apply hC.1
    rw [hc, h, mul_zero]
  obtain ⟨-, fH, hle, -⟩ := (GlobalTheory.T.lattice_good_base_change D R p w χ hC hB hG₁).1 τ
  obtain ⟨-, fW, -, fO⟩ := hB.free τ
  obtain ⟨g1, g2, g3⟩ := hB.gam τ
  obtain ⟨d1, -, d3, d4⟩ := hB.del τ
  exact core R (D.W τ) (D.omHT τ) (D.Gam τ) (D.Del τ) (D.hh R p (χ τ)) w hw0 fW fO fH
    (std_le_dual R hle) (fun v hv => smul_mem_std R (hw τ) hv) (hG₂.im τ)
    (fun x hx => (hB.stable τ x hx).1) (fun x hx => (hB.stable τ x hx).2.1) g1 g2 g3 d1 d3 d4

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerFree
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUniqueStatement
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_bundle_base_extension_unique : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → (LatLE O x E E' → LatLE O (joinCoord x z) EB E'B) ∧ (SameGeneric O x E E' → SameGeneric O (joinCoord x z) EB E'B) ∧ (∀ c : Ω, IsScaled x c E.lat E'.lat → IsScaled (joinCoord x z) c EB.lat E'B.lat) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve | exact GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleShortExactStatement
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_bundle_short_exact : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N N₁ N₂ : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (E : ChartBundle O (mseg x) N V) (i : V₁ →ₗ[Ω] V) (p : V →ₗ[Ω] V₂) (E₁ : ChartBundle O (mseg x) N₁ V₁) (E₂ : ChartBundle O (mseg x) N₂ V₂), IsSubQuot O x E i p E₁ E₂ → ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB : ChartBundle O (mseg (joinCoord x z)) N V) (EB₁ : ChartBundle O (mseg (joinCoord x z)) N₁ V₁) (EB₂ : ChartBundle O (mseg (joinCoord x z)) N₂ V₂), IsPull O x z E EB → IsPull O x z E₁ EB₁ → IsPull O x z E₂ EB₂ → IsSubQuot O (joinCoord x z) EB i p EB₁ EB₂ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PullSubQuot.main | exact GlobalTheory.CompanionTheory.Ar.Num.PullSubQuot.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PullSubQuot.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualEigenSubDegreeTransposeStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_eigen_sub_degree_transpose : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Matrix (Fin d) (Fin d) K, IsBun C L → (∀ a, IsHom C L L (Matrix.toLin' (ρ a))) → ∀ s, subDeg C (dotDual C L) (eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a))) = - subDeg C L (eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.EigDual.eig_dual_deg | exact GlobalTheory.CompanionTheory.Ar.Crv.EigDual.eig_dual_deg | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.EigDual.eig_dual_deg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeFlagFrameStatement
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_flag_frame : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), IsDualLat O x β E.lat F.lat → ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → ∀ w₁ : Module.Basis (Fin N) Ω V₁, (∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) → IsFlagFrame x F w₁ (fun j => -b j.rev) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FlagDual.main | exact GlobalTheory.CompanionTheory.Ar.Num.FlagDual.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FlagDual.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenspaceFrobeniusTwistStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_frobenius_twist : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.eig_frobenius_twist | exact GlobalTheory.CompanionTheory.Ar.Crv.eig_frobenius_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.eig_frobenius_twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalLinearTermComposition
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem lin_comp_chain : ∀ (R : Type) [CommRing R] (d : ℕ) (φ ψ : Pt R 1 d), (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → lin (comp1 φ ψ) 1 = lin φ 1 * lin ψ 1 ∧ lin (pt R (n := 1) d 0) 1 = 1 ∧ ∀ p : ℕ, 1 ≤ p → lin (comp1 φ (ptPow R d p 0)) p = lin φ 1 ∧ lin (comp1 φ (comp1 ψ (ptPow R d p 0))) p = lin φ 1 * lin ψ 1 :=
  @PositivityTheory.HtPt.Ca.lin_comp

end GlobalTheory.CompanionTheory.Ar.Conj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeKernelImageLatticeStatement
section
open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.GR ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_kernel_image_lattice : ∀ {o C : Type} [CommRing o] [Field C] [Algebra o C] (RC : Subalgebra o C) (p : ℕ) {F : Type} [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData C F n Sg r s) (w : C) (χ : Sg → F → C) (τ : Sg), w ≠ 0 → mulLat w (stdLat RC _) ≤ D.af RC p (χ τ) → D.af RC p (χ τ) ≤ stdLat RC _ → ∀ (ht : (Fin n → C) →ₗ[C] (Fin (s τ) → C)) (hb : (Fin (r τ) → C) →ₗ[C] (Fin n → C)), Function.Injective hb → LinearMap.range hb = LinearMap.ker ht → (stdLat RC _).map ht.toAddMonoidHom = D.omHT τ → (stdLat RC _).comap hb.toAddMonoidHom = D.W τ → (D.hh RC p (χ τ)).map ht.toAddMonoidHom = D.om τ → (D.hh RC p (χ τ)).comap hb.toAddMonoidHom = divLat w (D.lie τ) → (∀ b c, (b, c) ∈ D.Del τ ↔ w • b ∈ stdLat RC _ ∧ c - ht b ∈ D.omHT τ) → (∀ a b, (a, b) ∈ D.Gam τ ↔ w • a ∈ D.W τ ∧ b - hb a ∈ stdLat RC _) → D.imH RC p τ (χ τ) = D.om τ ∧ D.kerH RC p τ (χ τ) = divLat w (D.lie τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PtSeq.pt_seq_lin | exact GlobalTheory.CompanionTheory.Ar.PtSeq.pt_seq_lin | (intros; apply GlobalTheory.CompanionTheory.Ar.PtSeq.pt_seq_lin <;> assumption)
end

