import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0352
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
import GroundTheory.AutomorphicForms.AnisotropicHeight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0022
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0355
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleLeviTransport
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.ParIndBridge

theorem parInd_equiv_parabolicInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((parInd e ρ).Equiv (parabolicInd k N β (ρ.comp φ.symm.toMonoidHom))) := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ W _ _ ρ
  have hP : parab k e = blockUpper k N β := GlobalTheory.T.parabolic_eq_block_upper k e β hβ
  have h12 : ∀ {p : GL (Fin N) k}, p ∈ parab k e → p ∈ blockUpper k N β := fun h => hP ▸ h
  have h21 : ∀ {p : GL (Fin N) k}, p ∈ blockUpper k N β → p ∈ parab k e := fun h => hP ▸ h
  have hchar : ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β) (w : W),
      (deltaHalf k m (leviProj k e ⟨p, h1⟩) : ℂ) • ρ (leviProj k e ⟨p, h1⟩) w =
        sqrtModular k N β ⟨p, h2⟩ •
          ρ (φ.symm (GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩)) w := by
    intro p h1 h2 w
    have hL := GlobalTheory.T.parabolic_levi_projection k e β hβ φ hφ p h1 h2
    rw [← hL, MulEquiv.symm_apply_apply, GlobalTheory.T.modulus_character_levi k e β hβ φ hφ, hL,
      GroundTheory.Automorphic.Parabolic.sqrtModular_leviProj]
  let σ := ρ.comp φ.symm.toMonoidHom
  let E : IndSp e ρ ≃ₗ[ℂ] GroundTheory.Automorphic.Parabolic.parabolicIndSpace k N β σ :=
    { toFun := fun f => ⟨f.1.1, fun p g => by
          have h := parInd_law e ρ f ⟨p.1, h21 p.2⟩ g
          refine h.trans ?_
          exact hchar p.1 (h21 p.2) p.2 _,
        GroundTheory.Automorphic.stabilizerOf (GlobalTheory.PRep.ind (parab k e)
          ((twist ρ (deltaHalf k m)).comp (leviProj k e))) f.1, f.2, fun x hx g => by
          have h := GroundTheory.Automorphic.mem_stabilizerOf.1 hx
          exact congrFun (congrArg Subtype.val h) g⟩
      invFun := fun f => ⟨⟨f.1, fun p g => by
          have h := f.2.1 ⟨p.1, h12 p.2⟩ g
          refine h.trans ?_
          exact (hchar p.1 p.2 (h12 p.2) _).symm⟩, by
          obtain ⟨-, K, hK, hf⟩ := f.2
          refine mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds (one_mem K)) fun x hx => ?_)
          exact Subtype.ext (funext fun g => hf x hx g)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Representation.Equiv.mk E fun g => LinearMap.ext fun f => Subtype.ext (funext fun x => rfl)⟩

end GlobalTheory.CompanionTheory.ParIndBridge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethOfRestrictBijectiveStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kuenneth_of_restrict_bijective : ∀ {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ U₂' : ObjectProperty E.C₂} {U₃ U₃' : ObjectProperty E.D} (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂' (E.L₂.obj T)) (k₁ : U₁' ≤ U₁) (k₂ : U₂' ≤ U₂) (k₃ : U₃' ≤ U₃), (∀ a n, Function.Bijective ((resU (E.F₁ a) k₁).pull n)) → (∀ a n, Function.Bijective ((resU (E.F₂ a) k₂).pull n)) → (∀ a n, Function.Bijective ((resU (E.F₃ a) k₃).pull n)) → (E.Kun U₁ U₂ U₃ h₁ h₂ ↔ E.Kun U₁' U₂' U₃' h₁' h₂') := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kun_res | exact GlobalTheory.CompanionTheory.KunGlue.kun_res | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kun_res <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIntersectionConjugate
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

noncomputable section

namespace GlobalTheory.CompanionTheory.GeomCell

open GroundTheory.Automorphic.Parabolic (leviPar normLeviParSqrtModular normLeviParInvSqrtModular innerJacquetSpace leviUnipotent cellLeviSubIncl cellInnerHom leviInfIncl levJacquetAction innerJacquetRep)

theorem nonempty_indRep_comp_equiv {G L : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group L] [TopologicalSpace L] [IsTopologicalGroup L] (Φ : L ≃* G) (hΦ : Continuous Φ)
    (hΦ' : Continuous Φ.symm) (H : Subgroup G) (P : Subgroup L) (hHP : ∀ p, p ∈ P ↔ Φ p ∈ H)
    {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (σ : Representation ℂ H V) (τ : Representation ℂ P V') (T : V ≃ₗ[ℂ] V')
    (hT : ∀ (p : P) (v : V), T (σ ⟨Φ p, (hHP p.1).1 p.2⟩ v) = τ p (T v)) :
    Nonempty (Representation.Equiv ((indRep H σ).comp Φ.toMonoidHom) (GlobalTheory.PRep.smInd P τ)) := by
  have hTs : ∀ (p : P) (v : V'), T.symm (τ p v) = σ ⟨Φ p, (hHP p.1).1 p.2⟩ (T.symm v) := by
    intro p v
    apply T.injective
    rw [hT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let A : GroundTheory.Automorphic.indSpace H σ ≃ₗ[ℂ] GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind P τ) :=
    { toFun := fun φ => ⟨⟨fun l => T ((φ : G → V) (Φ l)), fun p x => by
          obtain ⟨h1, -⟩ := GroundTheory.Automorphic.mem_indSpace.1 φ.2
          have := h1 ⟨Φ p, (hHP p.1).1 p.2⟩ (Φ x)
          show T ((φ : G → V) (Φ (p * x))) = _
          rw [map_mul]
          exact (congrArg T this).trans (hT p _)⟩, by
          obtain ⟨-, K, hK, hKφ⟩ := GroundTheory.Automorphic.mem_indSpace.1 φ.2
          refine mem_smoothPart_of_nhds (Filter.mem_of_superset
            ((hK.preimage hΦ).mem_nhds (by simp [one_mem])) fun l hl => ?_)
          apply Subtype.ext
          funext x
          show T ((φ : G → V) (Φ (x * l))) = T ((φ : G → V) (Φ x))
          rw [map_mul, hKφ _ hl]⟩
      invFun := fun ψ => ⟨fun x => T.symm (ψ.1.1 (Φ.symm x)), by
          refine GroundTheory.Automorphic.mem_indSpace.2 ⟨fun h x => ?_, ?_⟩
          · have hp : Φ.symm h ∈ P := (hHP _).2 (by simp)
            have h1 := ψ.1.2 ⟨Φ.symm h, hp⟩ (Φ.symm x)
            have h2 : Φ.symm ((h : G) * x) = Φ.symm h * Φ.symm x := map_mul _ _ _
            show T.symm (ψ.1.1 (Φ.symm ((h : G) * x))) = σ h (T.symm (ψ.1.1 (Φ.symm x)))
            rw [h2]
            refine (congrArg T.symm h1).trans ((hTs _ _).trans ?_)
            congr 2
            exact Subtype.ext (by simp)
          · let S : Subgroup L :=
              { carrier := {l | GlobalTheory.PRep.ind P τ l ψ.1 = ψ.1}
                mul_mem' := by
                  intro a b ha hb
                  simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
                  rw [hb, ha]
                one_mem' := by simp
                inv_mem' := by
                  intro a ha
                  simp only [Set.mem_ofPred_eq] at *
                  conv_lhs => rw [← ha]
                  rw [← Module.End.mul_apply, ← map_mul]
                  simp }
            refine ⟨S.comap Φ.symm.toMonoidHom, ?_, fun g hg x => ?_⟩
            · exact IsOpen.preimage hΦ' ψ.2
            · have h3 : GlobalTheory.PRep.ind P τ (Φ.symm g) ψ.1 = ψ.1 := hg
              have h4 := congrFun (congrArg Subtype.val h3) (Φ.symm x)
              have h5 : Φ.symm (x * g) = Φ.symm x * Φ.symm g := map_mul _ _ _
              show T.symm (ψ.1.1 (Φ.symm (x * g))) = T.symm (ψ.1.1 (Φ.symm x))
              rw [h5]
              exact congrArg T.symm h4⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun l => map_add T _ _))
      map_smul' := fun c a => Subtype.ext (Subtype.ext (funext fun l => map_smul T _ _))
      left_inv := fun a => Subtype.ext (funext fun x => by simp)
      right_inv := fun a => Subtype.ext (Subtype.ext (funext fun x => by simp)) }
  refine ⟨.mk A fun l => ?_⟩
  refine LinearMap.ext fun a => Subtype.ext (Subtype.ext (funext fun x => ?_))
  show T ((a : G → V) (Φ x * Φ l)) = T ((a : G → V) (Φ (x * l)))
  rw [map_mul]

def coinvEquiv {M G W : Type} [Group M] [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ M W) (φ : M ≃* G) (U : Subgroup M) (U' : Subgroup G)
    (hU : ∀ u, u ∈ U ↔ φ u ∈ U') :
    Representation.Coinvariants ((ρ.comp φ.symm.toMonoidHom).comp U'.subtype) ≃ₗ[ℂ]
      GlobalTheory.PRep.Jacquet ρ U :=
  Submodule.quotEquivOfEq _ _ (by
    refine congrArg (Submodule.span ℂ) (Set.ext fun y => ⟨?_, ?_⟩)
    · rintro ⟨⟨u', v⟩, rfl⟩
      have hu : φ.symm (u' : G) ∈ U := (hU _).2 (by simp)
      exact ⟨⟨_, hu⟩, v, by simp⟩
    · rintro ⟨u, v, rfl⟩
      exact ⟨⟨⟨φ u, (hU _).1 u.2⟩, v⟩, by simp⟩)

theorem coinvEquiv_mk {M G W : Type} [Group M] [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ M W) (φ : M ≃* G) (U : Subgroup M) (U' : Subgroup G)
    (hU : ∀ u, u ∈ U ↔ φ u ∈ U') (x : W) :
    coinvEquiv ρ φ U U' hU (Representation.Coinvariants.mk _ x) = Submodule.Quotient.mk x := rfl

section
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ}
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)]
  {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]

theorem relProj_relEmb (f : ∀ i, (Σ j, c i j) ≃ m i) (q : ∀ i, Levi k (c i))
    (hq : relEmb k f q ∈ relParab k f) : relProj k f ⟨relEmb k f q, hq⟩ = q := by
  funext i
  exact leviProj_leviEmb k (f i) (q i)

theorem relEmb_mem_relParab (f : ∀ i, (Σ j, c i j) ≃ m i) (q : ∀ i, Levi k (c i)) :
    relEmb k f q ∈ relParab k f := fun i _ => leviEmb_mem_parab k (f i) (q i)

variable {k}

theorem cell_equiv (f : ∀ i, (Σ j, c i j) ≃ m i) (g : ∀ j, (Σ i, c i j) ≃ m' j)
    (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y)
    (φ : Levi k m ≃* levi k N β)
    (hφ : ∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g)
    (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ) (hγ : ∀ x y, γ x < γ y ↔ blk e' x < blk e' y)
    (φ' : Levi k m' ≃* levi k N γ)
    (hφ' : ∀ g, ((φ' g : levi k N γ) : GL (Fin N) k) = leviEmb k e' g)
    {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W)
    (w : Equiv.Perm (Fin N))
    (hcell : ∀ i j (t : c i j), w (e' ⟨j, g j ⟨i, t⟩⟩) = e ⟨i, f i ⟨j, t⟩⟩) :
    Nonempty (Representation.Equiv
      ((indRep (cellLeviSub k β γ w) (normInducing (ρ.comp φ.symm.toMonoidHom) γ w)).comp
        φ'.toMonoidHom) (cellFunctor f g ρ)) := by
  have hδg : ∀ j i i' (t : c i j) (t' : c i' j),
      (β ∘ w) (e' ⟨j, g j ⟨i, t⟩⟩) < (β ∘ w) (e' ⟨j, g j ⟨i', t'⟩⟩) ↔ i < i' := by
    intro j i i' t t'
    simp only [Function.comp, hcell, hβ, blk_apply]
  have hδf : ∀ i j j' (t : c i j) (t' : c i j'),
      (γ ∘ ⇑w⁻¹) (e ⟨i, f i ⟨j, t⟩⟩) < (γ ∘ ⇑w⁻¹) (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j' := by
    intro i j j' t t'
    simp only [Function.comp, ← hcell, Equiv.Perm.inv_def, Equiv.symm_apply_apply, hγ, blk_apply]
  have hP : ∀ p, p ∈ relParab k g ↔ φ' p ∈ cellLeviSub k β γ w := by
    intro p
    rw [GlobalTheory.T.levi_refinement_block_order k e' g (β ∘ w) hδg p, Subgroup.mem_subgroupOf]
    refine ⟨fun h => ⟨(φ' p).2, by rw [hφ']; exact h⟩, fun h => ?_⟩
    have := h.2
    rwa [hφ'] at this
  have hU : ∀ u, u ∈ relUnip k f ↔ φ u ∈ leviUnipotent k N β (γ ∘ ⇑w⁻¹) := by
    intro u
    rw [GlobalTheory.T.levi_refinement_parabolic k e f (γ ∘ ⇑w⁻¹) hδf u, leviUnipotent, Subgroup.mem_subgroupOf, hφ]
  obtain ⟨hc, hc'⟩ := GlobalTheory.T.levi_equiv_continuous k e' γ φ' hφ'
  refine nonempty_indRep_comp_equiv φ' hc hc' (cellLeviSub k β γ w) (relParab k g) hP _ _
    (coinvEquiv ρ φ (relUnip k f) (leviUnipotent k N β (γ ∘ ⇑w⁻¹)) hU) ?_
  intro p v
  obtain ⟨x, rfl⟩ := Representation.Coinvariants.mk_surjective _ v
  set b : cellLeviSub k β γ w := ⟨φ' p, (hP p.1).1 p.2⟩ with hbdef
  set q := relProj k g p with hq
  set sq := swapBlocks k c q with hsq
  have hbG : (((b : levi k N γ)) : GL (Fin N) k) = leviEmb k e' p.1 := hφ' _
  have hxm : permGL k w * leviEmb k e' p.1 * (permGL k w)⁻¹ ∈ blockUpper k N β := by
    rw [← hbG]
    exact (GroundTheory.Automorphic.Parabolic.permConj k β w ⟨_, b.2.2⟩).2
  have hin : GroundTheory.Automorphic.Parabolic.leviInfIncl β (γ ∘ ⇑w⁻¹)
      (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)) = φ (relEmb k f sq) := by
    apply Subtype.ext
    rw [hφ, ← GlobalTheory.T.levi_double_coset_intersection k e β hβ e' f g w hcell p.1 p.2 hxm]
    show ((GroundTheory.Automorphic.Parabolic.leviProj k N β _ : levi k N β) : GL (Fin N) k) = _
    congr 2
    exact Subtype.ext (show permGL k w * (((b : levi k N γ)) : GL (Fin N) k) * (permGL k w)⁻¹ = _ by
      rw [hbG])
  have h4 : normLeviParSqrtModular k γ (β ∘ w) (cellLeviSubIncl k β γ w b) =
      ((relDeltaHalf k (fun j i => c i j) q : ℂˣ) : ℂ) :=
    GlobalTheory.T.refined_block_order_compat k e' g γ (β ∘ w) hγ hδg (GlobalTheory.T.levi_refinement_block_order k e' g (β ∘ w) hδg) φ' hφ'
      p.1 p.2 b.2
  have hmemh : ((φ (relEmb k f sq) : levi k N β) : GL (Fin N) k) ∈ leviPar k N β (γ ∘ ⇑w⁻¹) := by
    rw [← hin]
    exact (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)).2
  have h5 : normLeviParInvSqrtModular k β (γ ∘ ⇑w⁻¹)
      (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)) =
      (((relDeltaHalf k c sq)⁻¹ : ℂˣ) : ℂ) := by
    have h6 := GlobalTheory.T.refined_block_order_compat k e f β (γ ∘ ⇑w⁻¹) hβ hδf
      (GlobalTheory.T.levi_refinement_block_order k e f (γ ∘ ⇑w⁻¹) hδf) φ hφ (relEmb k f sq) (relEmb_mem_relParab k f sq)
      hmemh
    rw [relProj_relEmb] at h6
    have h7 : cellInnerHom β γ w (cellLeviSubIncl k β γ w b) =
        ⟨((φ (relEmb k f sq) : levi k N β) : GL (Fin N) k), hmemh⟩ :=
      Subtype.ext (congrArg (fun z : levi k N β => (z : GL (Fin N) k)) hin)
    show (normLeviParSqrtModular k β (γ ∘ ⇑w⁻¹) _)⁻¹ = _
    rw [h7, h6, Units.val_inv_eq_inv_val]
  have hact : (ρ.comp φ.symm.toMonoidHom) (GroundTheory.Automorphic.Parabolic.leviInfIncl β (γ ∘ ⇑w⁻¹)
      (cellInnerHom β γ w (cellLeviSubIncl k β γ w b))) x = ρ (relEmb k f sq) x := by
    rw [hin]
    simp
  have hL : (normInducing (ρ.comp φ.symm.toMonoidHom) γ w) b
      (Representation.Coinvariants.mk _ x) =
      normLeviParSqrtModular k γ (β ∘ w) (cellLeviSubIncl k β γ w b) •
        normLeviParInvSqrtModular k β (γ ∘ ⇑w⁻¹) (cellInnerHom β γ w (cellLeviSubIncl k β γ w b)) •
          Representation.Coinvariants.mk _ ((ρ.comp φ.symm.toMonoidHom)
            (GroundTheory.Automorphic.Parabolic.leviInfIncl β (γ ∘ ⇑w⁻¹)
              (cellInnerHom β γ w (cellLeviSubIncl k β γ w b))) x) := rfl
  rw [hL, h4, h5, hact, map_smul, map_smul, coinvEquiv_mk]
  rfl

end

theorem cell_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {β' : Type} [Fintype β'] [LinearOrder β'] {m' : β' → Type} [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ (e' : (Σ j, m' j) ≃ Fin N) (γ : Fin N → ℕ), (∀ x y, γ x < γ y ↔ blk e' x < blk e' y) → ∀ (φ' : Levi k m' ≃* levi k N γ), (∀ g, ((φ' g : levi k N γ) : GL (Fin N) k) = leviEmb k e' g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W) (w : Equiv.Perm (Fin N)), ∃ (f : ∀ i, (Σ j, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m i) (g : ∀ j, (Σ i, Fin ((Finset.univ.filter fun x : Fin N => blk e x = i ∧ blk e' (w.symm x) = j).card)) ≃ m' j), Nonempty (Representation.Equiv ((indRep (cellLeviSub k β γ w) (normInducing (ρ.comp φ.symm.toMonoidHom) γ w)).comp φ'.toMonoidHom) (cellFunctor f g ρ)) := by
  intro k _ _ _ _ α _ _ N m _ _ β' _ _ m' _ _ e β hβ φ hφ e' γ hγ φ' hφ' W _ _ ρ w
  obtain ⟨f, g, hcell⟩ := GlobalTheory.T.block_count_reindex_equivs e e' w
  exact ⟨f, g, cell_equiv f g e β hβ φ hφ e' γ hγ φ' hφ' ρ w hcell⟩

end GlobalTheory.CompanionTheory.GeomCell
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsEqLogIdeleModule
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh

theorem logAbs_eq_log_ideleModule (E : Type) [Field E] [NumberField E] [IsCMField E] (s : (Ad E)ˣ) :
    logAbs (s : Ad E) = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ) := by
  have hm : ∀ v : InfinitePlace E, v.mult = 2 := fun v =>
    InfinitePlace.mult_isComplex ⟨v, IsTotallyComplex.isComplex v⟩
  have hinf : ∀ w : InfinitePlace E, ‖(s : Ad E).1 w‖ ≠ 0 := fun w =>
    norm_ne_zero_iff.2 (GroundTheory.Global.IdeleGroup.infinite_ne_zero s w)
  have hfin : ∀ v : HeightOneSpectrum (𝓞 E), 0 < ‖(s : Ad E).2 v‖ := fun v =>
    norm_pos_iff.2 (GroundTheory.Global.IdeleGroup.finite_ne_zero s v)
  have hA : (∏ w : InfinitePlace E, ‖(s : Ad E).1 w‖ ^ w.mult) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (hinf w)
  have hB : (∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖(s : Ad E).2 v‖) ≠ 0 :=
    (GroundTheory.Global.IdeleGroup.finiteModule_pos s).ne'
  have e : (GroundTheory.Global.IdeleGroup.ideleModule E s : ℝ) =
      (∏ w : InfinitePlace E, ‖(s : Ad E).1 w‖ ^ w.mult) *
        ∏ᶠ v : HeightOneSpectrum (𝓞 E), ‖(s : Ad E).2 v‖ :=
    GroundTheory.Global.IdeleGroup.ideleModule_eq s
  rw [e, Real.log_mul hA hB, Real.log_prod (fun w _ => pow_ne_zero _ (hinf w)), Real.log_finprod hfin]
  unfold logAbs
  simp only [GlobalTheory.CompanionTheory.TorNorm.norm_cV, hm]
  rfl

end GlobalTheory.CompanionTheory.TorusCh

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilradicalTranslationMeasurePreservingStatement
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilradical_translation_measure_preserving : ∀ (n : ℕ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) [MeasurableSpace (nilrad W₁ W₂)]
  [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure] (Y : nilrad W₁ W₂),
  MeasurePreserving (nmul hW Y) ν ν := by
  first | exact @GlobalTheory.CompanionTheory.LocVan.nmul_measurePreserving | exact GlobalTheory.CompanionTheory.LocVan.nmul_measurePreserving | (intros; apply GlobalTheory.CompanionTheory.LocVan.nmul_measurePreserving <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSqIntegralSmulLe
section
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.Godement

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

theorem inner_map {ρ : Γ → (B →L[ℂ] B)} (hU : IsU ρ) (g : Γ) (x y : B) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨-, -, hnorm, -⟩ := hU
  exact (LinearIsometry.mk (ρ g : B →ₗ[ℂ] B) (hnorm g)).inner_map_map x y

theorem inner_orbit {ρ : Γ → (B →L[ℂ] B)} (hU : IsU ρ) (v : B) (g h : Γ) :
    ⟪ρ g v, ρ h v⟫_ℂ = ⟪v, ρ (g⁻¹ * h) v⟫_ℂ := by
  rw [← GlobalTheory.CompanionTheory.Godement.inner_map hU g v (ρ (g⁻¹ * h) v)]
  obtain ⟨-, hmul, -, -⟩ := hU
  congr 1
  calc ρ h v = ρ (g * (g⁻¹ * h)) v := by rw [mul_inv_cancel_left]
    _ = ρ g (ρ (g⁻¹ * h) v) := by rw [hmul g (g⁻¹ * h), ContinuousLinearMap.mul_apply]

end Unitary

theorem mul_le_half_add (a b : ℝ≥0∞) : a * b ≤ 2⁻¹ * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.young_inequality a b Real.HolderConjugate.two_two
  rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.ofReal_ofNat] at h
  calc a * b ≤ a ^ 2 / 2 + b ^ 2 / 2 := h
    _ = 2⁻¹ * (a ^ 2 + b ^ 2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (a ^ 2), mul_comm (b ^ 2), mul_add]

theorem norm_sq_integral_smul_le : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (ρ : Γ → (B →L[ℂ] B)), IsU ρ → ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν → ∀ f : Γ → ℂ, Measurable f → Integrable f ν →
    Integrable (fun g => ‖f g‖ ^ 2) ν →
    ‖∫ g, f g • ρ g v ∂ν‖ ^ 2 ≤ (∫ g, ‖f g‖ ^ 2 ∂ν) * ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := by
  intro Γ _ _ _ _ _ _ _ ν _ _ B _ _ _ ρ hU v hφ f hf hfi hf2
  obtain ⟨-, -, -, hcont⟩ := id hU
  have hA : 0 ≤ ∫ g, ‖f g‖ ^ 2 ∂ν := integral_nonneg fun g => sq_nonneg _
  have hB : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun g => norm_nonneg _
  by_cases hF : Integrable (fun g => f g • ρ g v) ν
  swap
  · rw [integral_undef hF, norm_zero, zero_pow two_ne_zero]
    exact mul_nonneg hA hB
  have hψc : Continuous fun x : Γ => ‖⟪v, ρ x v⟫_ℂ‖ₑ := (continuous_const.inner (hcont v)).enorm
  have hψ : Measurable fun x : Γ => ‖⟪v, ρ x v⟫_ℂ‖ₑ := hψc.measurable
  have hfe : Measurable fun g : Γ => ‖f g‖ₑ ^ 2 := hf.enorm.pow_const 2
  have hswap : ∀ g h : Γ, ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ = ‖⟪v, ρ (g⁻¹ * h) v⟫_ℂ‖ₑ := by
    intro g h
    rw [← GlobalTheory.CompanionTheory.Godement.inner_orbit hU v h g, ← GlobalTheory.CompanionTheory.Godement.inner_orbit hU v g h,
      ← inner_conj_symm (ρ h v) (ρ g v), RCLike.enorm_conj]
  have hswapm : AEMeasurable (Function.uncurry fun h g : Γ =>
      2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ)) (ν.prod ν) := by
    apply Measurable.aemeasurable
    exact measurable_const.mul ((hfe.comp measurable_snd).mul
      (hψ.comp (measurable_fst.inv.mul measurable_snd)))
  have hm3 : Measurable fun h => 2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν :=
    (measurable_const.mul hfe).mul_const _
  have hm4 : Measurable fun h => 2⁻¹ * ‖f h‖ₑ ^ 2 := measurable_const.mul hfe
  have hII : ⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ =
      ∫ h, f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν) ∂ν := by
    rw [← integral_inner hF]
    refine integral_congr_ae ?_
    filter_upwards with h
    rw [inner_smul_right, ← inner_conj_symm, ← integral_inner hF]
    simp only [inner_smul_right]
  have key : ‖⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ‖ₑ ≤
      (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
    rw [hII]
    calc ‖∫ h, f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν) ∂ν‖ₑ
        ≤ ∫⁻ h, ‖f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν)‖ₑ ∂ν :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ h, ∫⁻ g, 2⁻¹ * (‖f h‖ₑ ^ 2 + ‖f g‖ₑ ^ 2) * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν ∂ν := by
          refine lintegral_mono fun h => ?_
          beta_reduce
          rw [enorm_mul, RCLike.enorm_conj]
          calc ‖f h‖ₑ * ‖∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν‖ₑ
              ≤ ‖f h‖ₑ * ∫⁻ g, ‖f g * ⟪ρ h v, ρ g v⟫_ℂ‖ₑ ∂ν := by
                gcongr
                exact enorm_integral_le_lintegral_enorm _
            _ ≤ ∫⁻ g, ‖f h‖ₑ * ‖f g * ⟪ρ h v, ρ g v⟫_ℂ‖ₑ ∂ν := lintegral_const_mul_le _ _
            _ ≤ _ := by
                refine lintegral_mono fun g => ?_
                beta_reduce
                rw [enorm_mul, GlobalTheory.CompanionTheory.Godement.inner_orbit hU, ← mul_assoc]
                gcongr ?_ * _
                exact GlobalTheory.CompanionTheory.Godement.mul_le_half_add _ _
      _ = ∫⁻ h, (2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν +
            ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν) ∂ν := by
          refine lintegral_congr fun h => ?_
          have hm : Measurable fun g => ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ := hψ.comp (measurable_const_mul h⁻¹)
          have hm2 : Measurable fun g => 2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ :=
            measurable_const.mul hm
          calc ∫⁻ g, 2⁻¹ * (‖f h‖ₑ ^ 2 + ‖f g‖ₑ ^ 2) * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν
              = ∫⁻ g, (2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ +
                  2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ)) ∂ν :=
                lintegral_congr fun g => by ring
            _ = ∫⁻ g, 2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν +
                  ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν :=
                lintegral_add_left hm2 _
            _ = _ := by
                rw [lintegral_const_mul _ hm,
                  lintegral_mul_left_eq_self (fun x => ‖⟪v, ρ x v⟫_ℂ‖ₑ) h⁻¹]
      _ = (∫⁻ h, 2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν ∂ν) +
            ∫⁻ h, ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν ∂ν :=
          lintegral_add_left hm3 _
      _ = 2⁻¹ * (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * (∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν) +
            2⁻¹ * (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * (∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν) := by
          congr 1
          · rw [lintegral_mul_const _ hm4, lintegral_const_mul _ hfe]
          · rw [lintegral_lintegral_swap hswapm]
            calc ∫⁻ g, ∫⁻ h, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν ∂ν
                = ∫⁻ g, 2⁻¹ * ‖f g‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν ∂ν := by
                  refine lintegral_congr fun g => ?_
                  have hm : Measurable fun h => ‖⟪v, ρ (g⁻¹ * h) v⟫_ℂ‖ₑ :=
                    hψ.comp (measurable_const_mul g⁻¹)
                  simp_rw [hswap g]
                  rw [← lintegral_mul_left_eq_self (fun x => ‖⟪v, ρ x v⟫_ℂ‖ₑ) g⁻¹,
                    ← lintegral_const_mul _ hm]
                  exact lintegral_congr fun h => by ring
              _ = _ := by
                  rw [lintegral_mul_const _ hm4, lintegral_const_mul _ hfe]
      _ = (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
          rw [← two_mul, ← mul_assoc, ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hX : ENNReal.ofReal (∫ g, ‖f g‖ ^ 2 ∂ν) = ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2 (Filter.Eventually.of_forall fun g => sq_nonneg _)]
    refine lintegral_congr fun g => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hY : ENNReal.ofReal (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) = ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hφ.norm (Filter.Eventually.of_forall fun g => norm_nonneg _)]
    exact lintegral_congr fun g => ofReal_norm_eq_enorm _
  have hL : ‖∫ g, f g • ρ g v ∂ν‖ ^ 2 = ‖⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [hL, ← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA hB), ENNReal.ofReal_mul hA, hX, hY,
    ofReal_norm_eq_enorm]
  exact key

end GlobalTheory.CompanionTheory.Godement
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RayClassPartialZetaIntegralityStatement
section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_class_partial_zeta_integrality : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 𝔠 : Ideal (𝓞 F)) (J : Type) [Fintype J] (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → 𝔠.IsPrime → (Ideal.absNorm 𝔠).Prime → (∀ j i, v j i ∉ 𝔠 * 𝔟) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => (classWeight (Ideal.absNorm 𝔠) 𝔠 I.1 : ℂ) * ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) (T s)) → ∀ k : ℕ, 1 ≤ k → ∃ q : ℚ, T (1 - (k : ℂ)) = (q : ℂ) ∧ ∀ l : ℕ, l.Prime → l ≠ Ideal.absNorm 𝔠 → ¬ l ∣ Ideal.absNorm 𝔟 → 0 ≤ padicValRat l q := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality.classTwist_value_int | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality.classTwist_value_int | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Integrality.classTwist_value_int <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_calculus_holds : PositivityTheory.RgBcC.RCalc := by
  first | exact @GlobalTheory.CompanionTheory.RCalc.rcalc | exact GlobalTheory.CompanionTheory.RCalc.rcalc | (intros; apply GlobalTheory.CompanionTheory.RCalc.rcalc <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsFiniteGeneratorsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_sections_finite_generators : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ n : ℤ, (∀ e, ∀ x ∈ twSecs H n (S e), ∃ y ∈ twSecs H n (S (e + 1)), x - y ∈ twPow I H n P (e + 1)) → ∃ W : Set Γ(GlobalTheory.twistZ P H n, ⊤), (∀ e, W ⊆ twSecs H n (S e)) ∧ ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W, x - b ∈ twPow I H n P (e + 1) := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwLim.exists_compat_limit | exact GlobalTheory.CompanionTheory.GE.TwLim.exists_compat_limit | (intros; apply GlobalTheory.CompanionTheory.GE.TwLim.exists_compat_limit <;> assumption)
end

