import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PreservesFiniteColimitsTwistFunctor
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0328
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0326
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullEqOfNatTrans
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDoubleCosetIntersection
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

private theorem conj_apply_lemma (k : Type) [Field k] {N : ℕ} (w : Equiv.Perm (Fin N))
    (A : GL (Fin N) k) (u v : Fin N) :
    (↑(permGL k w * A * (permGL k w)⁻¹) : Matrix (Fin N) (Fin N) k) (w u) (w v) =
      (↑A : Matrix (Fin N) (Fin N) k) u v := by
  have hv : ∀ σ : Equiv.Perm (Fin N),
      (↑(permGL k σ) : Matrix (Fin N) (Fin N) k) = (σ⁻¹).toPEquiv.toMatrix := fun σ => rfl
  rw [← map_inv, Units.val_mul, Units.val_mul, hv, hv, inv_inv, PEquiv.mul_toMatrix_toPEquiv,
    PEquiv.toMatrix_toPEquiv_mul]
  simp [Matrix.submatrix_apply]

theorem GlobalTheory.CompanionTheory.GeomCell.innerMat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (e' : (Σ j, m' j) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j) (w : Equiv.Perm (Fin N)) (hcell : ∀ i j (t : c i j), w (e' ⟨j, g j ⟨i, t⟩⟩) = e ⟨i, f i ⟨j, t⟩⟩) (p : Levi k m') (hp : p ∈ relParab k g) (hx : permGL k w * leviEmb k e' p * (permGL k w)⁻¹ ∈ blockUpper k N β), ((GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨_, hx⟩ : levi k N β) : GL (Fin N) k) = leviEmb k e (relEmb k f (swapBlocks k c (relProj k g ⟨p, hp⟩))) := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ m' _ _ c _ _ e β hβ e' f g w hcell p hp hx
  have key : ∀ a b : Fin N, β a = β b ↔ blk e a = blk e b := by
    intro a b
    constructor
    · intro h
      rcases lt_trichotomy (blk e a) (blk e b) with h' | h' | h'
      · exact absurd h (ne_of_lt ((hβ a b).mpr h'))
      · exact h'
      · exact absurd h (ne_of_gt ((hβ b a).mpr h'))
    · intro h
      rcases lt_trichotomy (β a) (β b) with h' | h' | h'
      · exact absurd h (ne_of_lt ((hβ a b).mp h'))
      · exact h'
      · exact absurd h (ne_of_gt ((hβ b a).mp h'))
  have hL : ∀ x y, (↑(↑((GroundTheory.Automorphic.Parabolic.leviProj k N β) ⟨_, hx⟩ : levi k N β) :
      GL (Fin N) k) : Matrix (Fin N) (Fin N) k) x y = if β x = β y then
      (↑(permGL k w * leviEmb k e' p * (permGL k w)⁻¹) : Matrix (Fin N) (Fin N) k) x y else 0 :=
    fun x y => rfl
  have hrel : ∀ (Q : ∀ i, Levi k (c i)) (i : α), relEmb k f Q i = leviEmb k (f i) (Q i) :=
    fun Q i => rfl
  have hsw : ∀ (R : ∀ j, Levi k (fun i => c i j)) (i : α) (j : β'), swapBlocks k c R i j = R j i :=
    fun R i j => rfl
  have hproj : ∀ (j : β') (i : α) (s s' : c i j),
      (↑((relProj k g ⟨p, hp⟩) j i) : Matrix (c i j) (c i j) k) s s' =
        (↑(p j) : Matrix (m' j) (m' j) k) (g j ⟨i, s⟩) (g j ⟨i, s'⟩) :=
    fun j i s s' => leviProj_apply k (g j) _ i s s'
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨j, t⟩, rfl⟩ := (f i).surjective a
  obtain ⟨⟨i', a'⟩, rfl⟩ := e.surjective y
  obtain ⟨⟨j', t'⟩, rfl⟩ := (f i').surjective a'
  rw [hL]
  by_cases hii : i = i'
  · subst hii
    rw [if_pos ((key _ _).mpr (by rw [blk_apply, blk_apply])), ← hcell i j t, ← hcell i j' t',
      conj_apply_lemma, hcell i j t, hcell i j' t', leviEmb_apply_same, hrel]
    by_cases hjj : j = j'
    · subst hjj
      rw [leviEmb_apply_same, leviEmb_apply_same, hsw, hproj]
    · rw [leviEmb_apply_ne k e' p hjj, leviEmb_apply_ne k (f i) _ hjj]
  · rw [if_neg (fun h => hii (by rw [key, blk_apply, blk_apply] at h; exact h)),
      leviEmb_apply_ne k e _ hii]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviEquivContinuous
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.LeviCont

theorem levi_iso_homeo (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (φ : Levi k m ≃* levi k N β) (hφ : ∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) : Continuous φ ∧ Continuous φ.symm := by
  have hcont : ∀ (Ψ : Levi k m → GL (Fin N) k) (ρ : ∀ a, GL (m a) k → Matrix (m a) (m a) k),
      (∀ a, Continuous (ρ a)) →
      (∀ g a (i j : m a), (Ψ g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) = ρ a (g a) i j) →
      (∀ g a b (i : m a) (j : m b), a ≠ b →
        (Ψ g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0) →
      Continuous fun g => (Ψ g : Matrix (Fin N) (Fin N) k) := by
    intro Ψ ρ hρ hs hn
    refine continuous_pi fun r => continuous_pi fun s => ?_
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective r
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective s
    by_cases hab : a = b
    · subst hab
      simp_rw [hs]
      exact (continuous_apply j).comp ((continuous_apply i).comp ((hρ a).comp (continuous_apply a)))
    · simp_rw [hn _ _ _ _ _ hab]
      exact continuous_const
  have hinv : ∀ g, ((φ g : levi k N β) : GL (Fin N) k)⁻¹ = leviEmb k e g⁻¹ := by
    intro g
    rw [← hφ, map_inv, Subgroup.coe_inv]
  have hs1 : ∀ g a (i j : m a), ((φ g : levi k N β) : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
      (g a : Matrix (m a) (m a) k) i j := by
    intro g a i j
    rw [hφ]
    exact leviEmb_apply_same k e g a i j
  have hs2 : ∀ g a (i j : m a),
      (((φ g : levi k N β) : GL (Fin N) k)⁻¹ : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
      (((g a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k) i j := by
    intro g a i j
    rw [hinv]
    exact leviEmb_apply_same k e g⁻¹ a i j
  have hn1 : ∀ g a b (i : m a) (j : m b), a ≠ b →
      ((φ g : levi k N β) : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
    intro g a b i j hab
    rw [hφ]
    exact leviEmb_apply_ne k e g hab i j
  have hn2 : ∀ g a b (i : m a) (j : m b), a ≠ b →
      (((φ g : levi k N β) : GL (Fin N) k)⁻¹ : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨b, j⟩) = 0 := by
    intro g a b i j hab
    rw [hinv]
    exact leviEmb_apply_ne k e g⁻¹ hab i j
  refine ⟨?_, ?_⟩
  · refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
    · exact hcont (fun g => (φ g : GL (Fin N) k)) (fun a u => (u : Matrix (m a) (m a) k))
        (fun a => Units.continuous_val) hs1 hn1
    · exact hcont (fun g => ((φ g : GL (Fin N) k))⁻¹) (fun a u => ((u⁻¹ : GL (m a) k) : Matrix (m a) (m a) k))
        (fun a => Units.continuous_coe_inv) hs2 hn2
  · refine continuous_pi fun a => Units.continuous_iff.2 ⟨?_, ?_⟩
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      have h : ∀ h : levi k N β, ((φ.symm h a : GL (m a) k) : Matrix (m a) (m a) k) i j =
          ((h : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) := by
        intro h
        rw [← hs1, MulEquiv.apply_symm_apply]
      simp_rw [Function.comp_apply, h]
      exact (continuous_apply _).comp ((continuous_apply _).comp
        ((Units.continuous_val (M := Matrix (Fin N) (Fin N) k)).comp continuous_subtype_val))
    · refine continuous_pi fun i => continuous_pi fun j => ?_
      have h : ∀ h : levi k N β, (((φ.symm h a)⁻¹ : GL (m a) k) : Matrix (m a) (m a) k) i j =
          (((h : GL (Fin N) k))⁻¹ : GL (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) := by
        intro h
        rw [← hs2, MulEquiv.apply_symm_apply]
      simp_rw [h]
      exact (continuous_apply _).comp ((continuous_apply _).comp
        ((Units.continuous_coe_inv (M := Matrix (Fin N) (Fin N) k)).comp continuous_subtype_val))

end GlobalTheory.CompanionTheory.LeviCont
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRefinementBlockOrder
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.CellCompare

theorem mem_relParab_iff_leviEmb_mem_blockUpper :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ}
      {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type}
      [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N)
      (f : ∀ i, (Σ j, c i j) ≃ m i) (δ : Fin N → ℕ)
      (hδ : ∀ i j j' (t : c i j) (t' : c i j'),
        δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (x : Levi k m),
      x ∈ relParab k f ↔ leviEmb k e x ∈ blockUpper k N δ := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ c _ _ e f δ hδ x
  unfold relParab
  rw [Subgroup.mem_pi]
  change _ ↔ (leviEmb k e x : Matrix (Fin N) (Fin N) k).BlockTriangular δ
  constructor
  · intro hx p q hpq
    obtain ⟨⟨a, u⟩, rfl⟩ := e.surjective p
    obtain ⟨⟨b, v⟩, rfl⟩ := e.surjective q
    by_cases hab : a = b
    · subst hab
      obtain ⟨⟨j, t⟩, rfl⟩ := (f a).surjective u
      obtain ⟨⟨j', t'⟩, rfl⟩ := (f a).surjective v
      rw [leviEmb_apply_same]
      exact mem_parab_iff.1 (hx a trivial) j j' t t' ((hδ a j' j t' t).1 hpq)
    · exact leviEmb_apply_ne k e x hab u v
  · intro hx i _
    rw [mem_parab_iff]
    intro j j' t t' hjj
    have h := hx ((hδ i j' j t' t).2 hjj)
    rwa [leviEmb_apply_same] at h

end GlobalTheory.CompanionTheory.CellCompare
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRefinementParabolic
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.RelUnipBridge

theorem one_apply_sigma {k n α : Type} [Zero k] [One k] [DecidableEq n] {m : α → Type}
    [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n) (a : α) (r s : m a) :
    (1 : Matrix n n k) (e ⟨a, r⟩) (e ⟨a, s⟩) = (1 : Matrix (m a) (m a) k) r s := by
  by_cases h : r = s
  · subst h; simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    intro h'
    have := e.injective h'
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact h this

theorem mem_relUnip_iff_leviEmb_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (δ : Fin N → ℕ) (hδ : ∀ i j j' (t : c i j) (t' : c i j'), δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (x : Levi k m), x ∈ relUnip k f ↔ leviEmb k e x ∈ unipotentRadical k N δ := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ c _ _ e f δ hδ x
  rw [GroundTheory.Automorphic.Parabolic.mem_unipotentRadical]
  constructor
  · intro hx
    have hx' : ∀ a, x a ∈ unipRad k (f a) := fun a => hx a trivial
    refine ⟨fun r s hrs => ?_, fun r s hrs => ?_⟩
    · obtain ⟨⟨a, r⟩, rfl⟩ := e.surjective r
      obtain ⟨⟨b, s⟩, rfl⟩ := e.surjective s
      by_cases hab : a = b
      · subst hab
        rw [leviEmb_apply_same]
        obtain ⟨⟨j, t⟩, rfl⟩ := (f a).surjective r
        obtain ⟨⟨j', t'⟩, rfl⟩ := (f a).surjective s
        exact mem_parab_iff.1 (mem_unipRad.1 (hx' a)).1 j j' t t' ((hδ a j' j t' t).1 hrs)
      · exact leviEmb_apply_ne k e x hab r s
    · obtain ⟨⟨a, r⟩, rfl⟩ := e.surjective r
      obtain ⟨⟨b, s⟩, rfl⟩ := e.surjective s
      by_cases hab : a = b
      · subst hab
        rw [leviEmb_apply_same, one_apply_sigma]
        obtain ⟨⟨j, t⟩, rfl⟩ := (f a).surjective r
        obtain ⟨⟨j', t'⟩, rfl⟩ := (f a).surjective s
        have hjj : j = j' := by
          rcases lt_trichotomy j j' with h | h | h
          · exact absurd ((hδ a j j' t t').2 h) hrs.not_lt
          · exact h
          · exact absurd ((hδ a j' j t' t).2 h) hrs.symm.not_lt
        subst hjj
        rw [one_apply_sigma]
        exact (mem_unipRad.1 (hx' a)).2 j t t'
      · rw [leviEmb_apply_ne k e x hab r s, Matrix.one_apply_ne]
        intro h
        exact hab (congrArg Sigma.fst (e.injective h))
  · rintro ⟨hP, h1⟩ a -
    refine mem_unipRad.2 ⟨mem_parab_iff.2 fun j j' t t' hjj => ?_, fun j t t' => ?_⟩
    · have := hP ((hδ a j' j t' t).2 hjj)
      rwa [leviEmb_apply_same] at this
    · have hd : δ (e ⟨a, f a ⟨j, t⟩⟩) = δ (e ⟨a, f a ⟨j, t'⟩⟩) := by
        rcases lt_trichotomy (δ (e ⟨a, f a ⟨j, t⟩⟩)) (δ (e ⟨a, f a ⟨j, t'⟩⟩)) with h | h | h
        · exact absurd ((hδ a j j t t').1 h) (lt_irrefl j)
        · exact h
        · exact absurd ((hδ a j j t' t).1 h) (lt_irrefl j)
      have := h1 _ _ hd
      rwa [leviEmb_apply_same, one_apply_sigma, one_apply_sigma] at this

end GlobalTheory.CompanionTheory.RelUnipBridge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingBaseOfVanishingCohomology
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.Step

theorem shortExact_lvl_zero {A : Type} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules} {S : ℕ → Subobject P}
    (hS : ClosedSys I P S) :
    (ShortComplex.mk (incl (anti hS) 0) (grπ (anti hS) 0) (incl_grπ (anti hS) 0)).ShortExact := by
  have : Mono (incl (anti hS) 0) := by
    unfold incl
    infer_instance
  have : Epi (grπ (anti hS) 0) := by
    exact coequalizer.π_epi
  exact { exact := ShortComplex.exact_cokernel (incl (anti hS) 0) }

theorem lifts_zero : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), H.IsLB → ∀ {P : X.Modules}
    (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ),
    Subsingleton (GlobalTheory.coh (GlobalTheory.twistZ (S 0 : X.Modules) H n) 1) → Lifts I H hS n 0 := by
  intro A _ _ I X _ H hH P S hS n hv y
  have hsurj : Function.Surjective
      ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) 0)).app ⊤) :=
    GlobalTheory.cohOn.app_surjective
      (GlobalTheory.Twist.shortExact_map (GlobalTheory.Twist.isLB_lbZPow hH n) (shortExact_lvl_zero hS)) ⊤ hv
  obtain ⟨c, hc⟩ := hsurj y
  refine ⟨c, hc, ?_⟩
  have htop : Ideal.map (toFunctions (X := X) (A := A) ⊤) (I ^ 0) = ⊤ := by
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
  simp only [twPow, htop, Submodule.top_smul]
  trivial

end GlobalTheory.CompanionTheory.GE.Step
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftingInductiveSuccessiveApproximation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE GlobalTheory.CompanionTheory.GE.Step

namespace GlobalTheory.CompanionTheory.GE.Step

theorem step_of_lifts {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}}
    [X.Over (Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X) (hH : H.IsLB) {P : X.Modules}
    (S : ℕ → Subobject P) (hS : ClosedSys I P S) (n : ℤ) (e : ℕ) (hL : Lifts I H hS n (e + 1)) :
    ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1) := by
  rintro x ⟨c0, rfl⟩
  have hLB : (GlobalTheory.lbZPow H n).IsLB := GlobalTheory.Twist.isLB_lbZPow hH n
  let S0 : ShortComplex X.Modules :=
    ShortComplex.mk (incl (anti hS) (e + 1)) (grπ (anti hS) (e + 1)) (incl_grπ (anti hS) (e + 1))
  have hex0 : S0.Exact := S0.exact_of_g_is_cokernel (cokernelIsCokernel _)
  have hex1 : (S0.map (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H n))).Exact :=
    (GlobalTheory.Twist.exact_map_iff hLB S0).mpr hex0
  have hmono0 : Mono (incl (anti hS) (e + 1)) := mono_of_mono_fac (incl_arrow (anti hS) (e + 1))
  have hmono1 : Mono (S0.map (GlobalTheory.twistFunctor (GlobalTheory.lbZPow H n))).f :=
    (GlobalTheory.Twist.mono_map_iff hLB (incl (anti hS) (e + 1))).mpr hmono0
  have hexΓ := GlobalTheory.QCoh.exact_app_of_exact_of_mono hex1 ⊤
  let c1 : Γ(GlobalTheory.twistZ (lvl S (e + 1) : X.Modules) H n, ⊤) := c0
  obtain ⟨c, hc1, hc2⟩ := hL ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) (e + 1))).app ⊤ c1)
  have hker : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (grπ (anti hS) (e + 1))).app ⊤ (c1 - c) = 0 := by
    rw [map_sub, hc1, sub_self]
  obtain ⟨d, hd⟩ := (hexΓ (c1 - c)).mp hker
  let d1 : Γ(GlobalTheory.twistZ (S (e + 1) : X.Modules) H n, ⊤) := d
  have hd' : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (incl (anti hS) (e + 1))).app ⊤ d1 = c1 - c := hd
  refine ⟨(GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S (e + 1)).arrow).app ⊤ d1, ⟨d1, rfl⟩, ?_⟩
  have harr0 : incl (anti hS) (e + 1) ≫ (S e).arrow = (S (e + 1)).arrow :=
    incl_arrow (anti hS) (e + 1)
  have harr : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S (e + 1)).arrow).app ⊤ d1 =
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ (c1 - c) :=
    (congrArg (fun φ => (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) φ).app ⊤ d1) harr0.symm).trans
      ((congrArg (fun f => f.app ⊤ d1)
          (GlobalTheory.Twist.map_comp (GlobalTheory.lbZPow H n) (incl (anti hS) (e + 1)) (S e).arrow)).trans
        ((GlobalTheory.QCoh.app_app _ _ ⊤ d1).symm.trans
          (congrArg (fun s => (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ s) hd')))
  have hfin : (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 -
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S (e + 1)).arrow).app ⊤ d1 =
      (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c := by
    calc _ = (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 -
          (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ (c1 - c) := by rw [harr]
      _ = (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 -
          ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c1 -
            (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c) :=
          congrArg (fun t => (GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤ c0 - t)
            (map_sub (ConcreteCategory.hom ((GlobalTheory.Twist.map (GlobalTheory.lbZPow H n) (S e).arrow).app ⊤)) c1 c)
      _ = _ := sub_sub_cancel _ _
  rw [hfin]
  exact hc2

end GlobalTheory.CompanionTheory.GE.Step
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameDerivationCompatStatement
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_frame_derivation_compat : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [Smooth q] (s : ℕ) {V V' : X.Opens} (hVV : V ≤ V'), IsAffineOpen V' → ∀ {d : ℕ} (c : Coord q V d),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (E : Frame (sP (KS q s {V})) d) (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D), IsLoc q s c.t E ε →
    ∀ (σ : ∀ T, E.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s → ∀ (ξ : HQ (KS q s {V'}) r (r + 1) m) (y : Idx m d → Γ(X, V)),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {V}) r) (sFil (KS q s {V}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) (resKS q s hVV _ _ _ ξ) →
      ∀ I, y I ∈ jacSpan hVV (RingHom.id _) (fun k => D k) I.1 := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.coef_mem_jacSpan | exact GlobalTheory.CompanionTheory.ConeLocal.coef_mem_jacSpan | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.coef_mem_jacSpan <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFacts
section
noncomputable section

open NumberField IsDedekindDomain PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.LogAbs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem norm_cW_eq_one (u : Ad E) (hu : IsUnit u) : ∀ᶠ w in Filter.cofinite, ‖cW w u‖ = 1 := by
  have h := (FiniteAdeleRing.isUnit_iff.1 (hu.map (pFin E))).2
  filter_upwards [h] with w hw
  have e : cW w u = (pFin E u) w := rfl
  rw [e, FinitePlace.norm_def, hw]
  simp

theorem support_log_finite (u : Ad E) (hu : IsUnit u) :
    (Function.support fun w => Real.log ‖cW w u‖).Finite := by
  refine (Filter.eventually_cofinite.1 (norm_cW_eq_one u hu)).subset fun w hw h1 => hw ?_
  simp [h1]

theorem logAbs_mul (u u' : Ad E) (hu : IsUnit u) (hu' : IsUnit u') :
    logAbs (u * u') = logAbs u + logAbs u' := by
  have h1 : ∀ v, Real.log (‖cV v (u * u')‖ ^ 2) = Real.log (‖cV v u‖ ^ 2) + Real.log (‖cV v u'‖ ^ 2) := fun v => by
    rw [map_mul, norm_mul, mul_pow, Real.log_mul
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu.map (cV v)).ne_zero))
      (pow_ne_zero 2 (norm_ne_zero_iff.2 (hu'.map (cV v)).ne_zero))]
  have h2 : ∀ w, Real.log ‖cW w (u * u')‖ = Real.log ‖cW w u‖ + Real.log ‖cW w u'‖ := fun w => by
    rw [map_mul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hu.map (cW w)).ne_zero)
      (norm_ne_zero_iff.2 (hu'.map (cW w)).ne_zero)]
  unfold logAbs
  simp only [h1, h2]
  rw [Finset.sum_add_distrib, finsum_add_distrib (support_log_finite u hu) (support_log_finite u' hu')]
  ring

theorem norm_cV_algebraMap (v : InfinitePlace E) (c : E) : ‖cV v (algebraMap E (Ad E) c)‖ = v c := by
  rw [← InfinitePlace.norm_embedding_eq]
  exact congrArg norm (pInf_algebraMap c v)

theorem norm_cW_algebraMap (w : HeightOneSpectrum (𝓞 E)) (c : E) :
    ‖cW w (algebraMap E (Ad E) c)‖ = FinitePlace.mk w c := rfl

theorem logAbs_algebraMap (c : E) (hc : c ≠ 0) : logAbs (algebraMap E (Ad E) c) = 0 := by
  have hprod := prod_abs_eq_one hc
  have hA : (∏ w : InfinitePlace E, w c ^ w.mult) ≠ 0 := left_ne_zero_of_mul_eq_one hprod
  have hB : (∏ᶠ w : FinitePlace E, w c) ≠ 0 := right_ne_zero_of_mul_eq_one hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul hA hB, Real.log_one, Real.log_prod (fun w _ => pow_ne_zero _ ((InfinitePlace.pos_iff.2 hc).ne')),
    Real.log_finprod fun w : FinitePlace E => FinitePlace.pos_iff.2 hc] at hlog
  have hm : ∀ v : InfinitePlace E, v.mult = 2 := fun v =>
    InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩
  unfold logAbs
  simp only [norm_cV_algebraMap, norm_cW_algebraMap]
  simp only [hm] at hlog
  rw [← hlog, ← finsum_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := E)).symm]
  rfl

theorem logAbsBasic : LogAbsBasic := fun _ _ _ _ =>
  ⟨support_log_finite, logAbs_mul, logAbs_algebraMap⟩

end GlobalTheory.CompanionTheory.LogAbs

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OperatorSequenceSumEpi
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.KerSeq

theorem epi_sumMap_of_opSeq {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules}
    {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ} (h : OpSeq k M T d) (e : ℕ) :
    Epi (KerSeq.sumMap T d e) := by
  haveI : ∀ n, (M n).IsQuasicoherent := fun n => (h.coherent n).1
  haveI : (KerSeq.sumN M k d e).IsQuasicoherent := by
    unfold KerSeq.sumN
    exact GlobalTheory.QCoh.isQuasicoherent_biproduct _
  rw [GlobalTheory.QCoh.epi_iff_forall_affine]
  intro U hU
  have hg := h.gen (d + e) (Nat.le_add_right d e) ⟨U, hU⟩
  have hr : (GlobalTheory.QCoh.appLinear (KerSeq.sumMap T d e) U).range = ⊤ := by
    rw [eq_top_iff, ← hg, Submodule.span_le]
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_range] at hy
    obtain ⟨i, x, rfl⟩ := hy
    refine ⟨(biproduct.ι (fun _ : Fin k => M (d + e)) i).app U x, ?_⟩
    rw [GlobalTheory.QCoh.appLinear_apply, GlobalTheory.QCoh.app_app]
    simp [KerSeq.sumMap]
  rw [← GlobalTheory.QCoh.coe_appLinear]
  exact LinearMap.range_eq_top.1 hr

end GlobalTheory.CompanionTheory.GE.KerSeq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingIsoOfComponentIsosStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_iso_of_component_isos : ∀ {K : Type} [Field K] {P P' Q Q' T T' : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (pr' : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P' a) (Q' a') (T' c)) (p : ∀ a, Cx.Hom (P a) (P' a) (RingHom.id K)) (f : ∀ a, Cx.Hom (Q a) (Q' a) (RingHom.id K)) (g : ∀ a, Cx.Hom (T a) (T' a) (RingHom.id K)), (∀ a n, Function.Bijective ((p a).mapH n)) → (∀ a n, Function.Bijective ((f a).mapH n)) → (∀ a n, Function.Bijective ((g a).mapH n)) → (∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j), (g c).f n ((pr ha).μ h x y) = (pr' ha).μ h ((p a).f i x) ((f a').f j y)) → (KunE pr ↔ KunE pr') := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff | exact GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff | (intros; apply GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullEqOfNatTransStatement
section
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_eq_of_nat_trans : ∀ (R : Type) [CommRing R] (C C' : Type 1) [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) (m₁ m₂ : CH.Mor F F' (RingHom.id R)) (α : m₁.G ⟶ m₂.G), (∀ (T : C') (x : F.obj (m₁.G.obj T)), m₂.τ T ((F.map (α.app T)).hom x) = m₁.τ T x) → ∀ j, m₁.pull j = m₂.pull j := by
  first | exact @GlobalTheory.CompanionTheory.CatPrism.pull_eq_target | exact GlobalTheory.CompanionTheory.CatPrism.pull_eq_target | (intros; apply GlobalTheory.CompanionTheory.CatPrism.pull_eq_target <;> assumption)
end

