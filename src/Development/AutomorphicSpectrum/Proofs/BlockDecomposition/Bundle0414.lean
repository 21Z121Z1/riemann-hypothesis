import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0407
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0405
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0175
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0401
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0398
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0341
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0342
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0340

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenKerDerChar
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.CompanionTheory.PRep.DerExact

theorem isOpen_ker_derChar (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) (N n : ℕ) :
    IsOpen ((derChar k ψ N n).ker : Set (derUnip k N n)) := by
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_addChar_eq_one ψ hψ
  let F : derUnip k N n → k := fun u => ∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ),
    (u : GL (Fin N) k).val p.1 p.2
  have hF : Continuous F := by
    refine continuous_finsetSum _ fun p _ => ?_
    have h1 : Continuous fun u : derUnip k N n => ((u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) :=
      Units.continuous_val.comp continuous_subtype_val
    exact (continuous_apply p.2).comp ((continuous_apply p.1).comp h1)
  have hsub : F ⁻¹' GlobalTheory.SplitWeil.cball s ⊆ ((derChar k ψ N n).ker : Set (derUnip k N n)) := by
    intro u hu
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    show Circle.toUnits (ψ (F u)) = 1
    rw [hs _ hu, map_one]
  have h1 : F 1 = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    show ((1 : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0
    rw [Units.val_one]
    exact Matrix.one_apply_ne fun e => by
      have := (Finset.mem_filter.1 hp).2.1; rw [e] at this; omega
  have hmem : F ⁻¹' GlobalTheory.SplitWeil.cball s ∈ nhds (1 : derUnip k N n) :=
    hF.continuousAt.preimage_mem_nhds (by rw [h1]; exact GlobalTheory.SplitWeil.cball_mem_nhds s)
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset hmem hsub)

end GlobalTheory.CompanionTheory.PRep.DerExact
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetHeckeConditionHolds
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.HeckeExist

theorem exists_heckeOp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.CH k := by
  intro k _ _ _ _ N J _ hJc V _ _ π hπ g
  obtain ⟨E, hE1, -, hE3, -, -⟩ :=
    GlobalTheory.CompanionTheory.CompactAvg.exists_average (GL (Fin N) k) J hJc V π hπ
  refine ⟨((E ∘ₗ π g ∘ₗ (fixed π J).subtype).codRestrict (fixed π J) (fun v => hE1 _)), ?_⟩
  intro v l hl
  have h := LinearMap.congr_fun (hE3 l hl) (π g (v : V))
  simpa using h.symm

end GlobalTheory.CompanionTheory.HeckeExist
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityDropZeroBlocks
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos Matrix

namespace GlobalTheory.CompanionTheory.FineProd.JmDrop

section Blocks

variable {R : Type} [Field R] {r r' : ℕ} {d : Fin r → ℕ} {o : Fin r' → Fin r}

theorem dropHom_surjective (ho : Function.Injective o) :
    Function.Surjective (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o) := by
  classical
  intro x
  have key : ∀ (j : Fin r) (b : Fin r') (hb : o b = j) (a : Fin r') (ha : o a = j),
      (hb ▸ x b : GL (Fin (d j)) R) = ha ▸ x a := by
    intro j b hb a ha
    obtain rfl : b = a := ho (hb.trans ha.symm)
    rfl
  refine ⟨(fun j => if hj : ∃ a, o a = j then hj.choose_spec ▸ x hj.choose else 1 :
    ∀ j, GL (Fin (d j)) R), ?_⟩
  funext a
  have hj : ∃ b, o b = o a := ⟨a, rfl⟩
  show (if hj : ∃ b, o b = o a then (hj.choose_spec ▸ x hj.choose : GL (Fin (d (o a))) R) else 1) = x a
  rw [dif_pos hj]
  exact key (o a) _ hj.choose_spec a rfl

variable {n : Type} [Fintype n] [DecidableEq n]
  {e : (Σ j, Fin (d j)) ≃ n} {e' : (Σ a, Fin (d (o a))) ≃ n}

theorem unipRad_eq (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o)
    (he : ∀ a t, e' ⟨a, t⟩ = e ⟨o a, t⟩) : unipRad R e = unipRad R e' := by
  ext g
  rw [GlobalTheory.SmGL.mem_unipRad, GlobalTheory.SmGL.mem_unipRad,
    GlobalTheory.SmGL.mem_parab_iff, GlobalTheory.SmGL.mem_parab_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b i j hab => ?_, fun a i j => ?_⟩
    · rw [he, he]
      exact h1 _ _ i j (hm hab)
    · rw [he, he]
      exact h2 _ i j
  · rintro ⟨h1, h2⟩
    refine ⟨fun A B i j hBA => ?_, fun A i j => ?_⟩
    · obtain ⟨a, rfl⟩ := hne A (Fin.pos i).ne'
      obtain ⟨b, rfl⟩ := hne B (Fin.pos j).ne'
      rw [← he, ← he]
      exact h1 a b i j (hm.lt_iff_lt.1 hBA)
    · obtain ⟨a, rfl⟩ := hne A (Fin.pos i).ne'
      rw [← he, ← he]
      exact h2 a i j

theorem leviEmb_eq (hm : StrictMono o) (he : ∀ a t, e' ⟨a, t⟩ = e ⟨o a, t⟩)
    (g : Levi R fun j => Fin (d j)) :
    leviEmb R e g = leviEmb R e' (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o g) := by
  apply Units.ext
  ext p q
  obtain ⟨⟨a, i⟩, rfl⟩ := e'.surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := e'.surjective q
  by_cases hab : a = b
  · subst hab
    have h1 := GlobalTheory.SmGL.leviEmb_apply_same R e g (o a) i j
    have h2 := GlobalTheory.SmGL.leviEmb_apply_same R e'
      (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o g) a i j
    rw [← he, ← he] at h1
    exact h1.trans h2.symm
  · have h1 := GlobalTheory.SmGL.leviEmb_apply_ne R e g (hm.injective.ne hab) i j
    have h2 := GlobalTheory.SmGL.leviEmb_apply_ne R e'
      (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o g) hab i j
    rw [← he, ← he] at h1
    exact h1.trans h2.symm

omit [Fintype n] [DecidableEq n] in

theorem modExp_drop (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o) (a : Fin r') :
    modExp (fun b => Fin (d (o b))) a = modExp (fun j => Fin (d j)) (o a) := by
  unfold GlobalTheory.SmGL.modExp
  congr 1
  all_goals
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Fintype.sum_of_injective o hm.injective _ _ (fun j hj => ?_) (fun b => ?_)
    · by_cases hd : d j = 0
      · simp [hd]
      · exact absurd (hne j hd) hj
    · simp [hm.lt_iff_lt]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r r' : ℕ} {d : Fin r → ℕ} {o : Fin r' → Fin r}

theorem deltaHalf_drop (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o)
    (g : Levi k fun j => Fin (d j)) :
    deltaHalf k (fun j => Fin (d j)) g =
      deltaHalf k (fun a => Fin (d (o a))) (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) d o g) := by
  rw [GlobalTheory.SmGL.deltaHalf_apply, GlobalTheory.SmGL.deltaHalf_apply]
  symm
  refine Fintype.prod_of_injective o hm.injective _ _ (fun j hj => ?_) (fun a => ?_)
  · have hd : d j = 0 := by
      by_contra hd
      exact hj (hne j hd)
    haveI : IsEmpty (Fin (d j)) := by
      rw [hd]
      infer_instance
    have hdet : Matrix.GeneralLinearGroup.det (g j) = 1 := by
      ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_isEmpty]
    rw [hdet, map_one]
  · rw [GlobalTheory.CompanionTheory.FineProd.JmDrop.modExp_drop hm hne a]
    first
    | rfl
    | skip

variable {n : Type} [Fintype n] [DecidableEq n]
  {e : (Σ j, Fin (d j)) ≃ n} {e' : (Σ a, Fin (d (o a))) ≃ n}
  {V : Type} [AddCommGroup V] [Module ℂ V]

def jacDrop (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o)
    (he : ∀ a t, e' ⟨a, t⟩ = e ⟨o a, t⟩) (π : Representation ℂ (GL n k) V) :
    (jac e π).Equiv
      ((jac e' π).comp (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) d o) :
        Representation ℂ (Levi k fun j => Fin (d j)) _) :=
  have h3 : twKer π (unipRad k e) 1 = twKer π (unipRad k e') 1 := by rw [unipRad_eq hm hne he]
  .mk (Submodule.quotEquivOfEq _ _ h3) fun g => by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.quotEquivOfEq _ _ h3 (jac e π g (Submodule.Quotient.mk v)) =
      jac e' π (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) d o g) (Submodule.Quotient.mk v)
    rw [jac_mk, jac_mk, map_smul, deltaHalf_drop hm hne, leviEmb_eq hm he]
    rfl

end Local

theorem jm_drop : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL k) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), jm y hd π = jm (fun a => y (o a)) hd' π := by
  intro k _ _ _ _ r r' N y hd o hm hne hd' V _ _ π
  have he := GlobalTheory.T.standard_blocks_reindex_strictMono (fun j => (y j).1) hd o hm hne hd'
  obtain ⟨φ⟩ := GlobalTheory.T.tensor_product_drop_zero_factors y o hm hne
  unfold Zc.jm
  rw [GlobalTheory.SmGL.jhMult_congr_left φ,
    GlobalTheory.SmGL.jhMult_congr_right _
      (GlobalTheory.CompanionTheory.FineProd.JmDrop.jacDrop (d := fun j => (y j).1) (o := o) hm hne he π),
    GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective _
      (GlobalTheory.CompanionTheory.FineProd.JmDrop.dropHom_surjective (R := k) (d := fun j => (y j).1) hm.injective)]

end GlobalTheory.CompanionTheory.FineProd.JmDrop

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOrderEmbedding
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
open GlobalTheory.CompanionTheory.FineProd (dropHom)

namespace GlobalTheory.CompanionTheory.WordProd.RowCell

section Blocks

variable {r r' N : ℕ} (d : Fin r → ℕ) (o : Fin r' → Fin r) (ho : StrictMono o)
  (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o)

def dropSigma : (Σ a, Fin (d (o a))) ≃ (Σ j, Fin (d j)) :=
  Equiv.ofBijective (fun p => ⟨o p.1, p.2⟩) (by
    constructor
    · rintro ⟨a, t⟩ ⟨b, s⟩ h
      obtain rfl : a = b := ho.injective (congrArg Sigma.fst h)
      simpa using h
    · rintro ⟨j, t⟩
      obtain ⟨a, rfl⟩ := hz j (Nat.pos_iff_ne_zero.1 (Fin.pos t))
      exact ⟨⟨a, t⟩, rfl⟩)

def dropPlacing (f : (Σ j, Fin (d j)) ≃ Fin N) : (Σ a, Fin (d (o a))) ≃ Fin N :=
  (dropSigma d o ho hz).trans f

@[simp] theorem dropPlacing_apply (f : (Σ j, Fin (d j)) ≃ Fin N) (a : Fin r') (t : Fin (d (o a))) :
    dropPlacing d o ho hz f ⟨a, t⟩ = f ⟨o a, t⟩ := rfl

variable (k : Type) [Field k] (f : (Σ j, Fin (d j)) ≃ Fin N)

theorem mem_parab_dropPlacing (g : GL (Fin N) k) :
    g ∈ parab k f ↔ g ∈ parab k (dropPlacing d o ho hz f) := by
  rw [mem_parab_iff, mem_parab_iff]
  constructor
  · intro h a b i j hab
    exact h _ _ i j (ho hab)
  · intro h a b i j hab
    obtain ⟨a, rfl⟩ := hz a (Nat.pos_iff_ne_zero.1 (Fin.pos i))
    obtain ⟨b, rfl⟩ := hz b (Nat.pos_iff_ne_zero.1 (Fin.pos j))
    exact h a b i j (ho.lt_iff_lt.1 hab)

theorem mem_unipRad_dropPlacing (g : GL (Fin N) k) :
    g ∈ unipRad k f ↔ g ∈ unipRad k (dropPlacing d o ho hz f) := by
  rw [mem_unipRad, mem_unipRad, ← mem_parab_dropPlacing d o ho hz k f g]
  refine and_congr_right fun _ => ⟨fun h a i j => h (o a) i j, fun h a i j => ?_⟩
  obtain ⟨a, rfl⟩ := hz a (Nat.pos_iff_ne_zero.1 (Fin.pos i))
  exact h a i j

theorem leviEmb_dropPlacing (g : Levi k fun j => Fin (d j)) :
    leviEmb k f g = leviEmb k (dropPlacing d o ho hz f) (dropHom d o g) := by
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := (dropPlacing d o ho hz f).surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := (dropPlacing d o ho hz f).surjective y
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same, dropPlacing_apply, dropPlacing_apply, leviEmb_apply_same]
    rfl
  · rw [leviEmb_apply_ne k _ _ hab, dropPlacing_apply, dropPlacing_apply,
      leviEmb_apply_ne k _ _ (ho.injective.ne hab)]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r r' N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSubquotient_pullback {G L W : Type} [Group G] [Group L] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (s : L →* G) (h : IsSubquotient σ ρ) :
    IsSubquotient (σ.comp s) (ρ.comp s) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (s g) hv⟩,
    ⟨f.toLinearMap, fun g => f.isIntertwining' (s g)⟩, hf⟩

theorem jac_dropPlacing_equiv (d : Fin r → ℕ) (o : Fin r' → Fin r) (ho : StrictMono o)
    (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (f : (Σ j, Fin (d j)) ≃ Fin N)
    (π : Representation ℂ (GL (Fin N) k) V) :
    Nonempty ((jac f π).Equiv
      ((jac (dropPlacing d o ho hz f) π).comp (dropHom d o) :
        Representation ℂ (Levi k fun j => Fin (d j)) _)) := by
  have hs' : ∀ g, ((leviEmb k (dropPlacing d o ho hz f)).comp (dropHom d o)) g ∈
      Subgroup.normalizer (unipRad k (dropPlacing d o ho hz f) : Set (GL (Fin N) k)) :=
    fun g => leviEmb_mem_normalizer k _ _
  obtain ⟨φ⟩ := Placing.jacquet_equiv π (N := unipRad k f) (N' := unipRad k (dropPlacing d o ho hz f))
    (s := leviEmb k f) (s' := (leviEmb k (dropPlacing d o ho hz f)).comp (dropHom d o))
    (leviEmb_mem_normalizer k f) hs' (deltaHalf k fun j => Fin (d j))⁻¹ 1
    (fun u hu => by simpa using (mem_unipRad_dropPlacing d o ho hz k f u).1 hu)
    (fun u hu => by simpa using (mem_unipRad_dropPlacing d o ho hz k f u).2 hu)
    (fun g => by simpa using leviEmb_dropPlacing d o ho hz k f g)
  have e : twist (jacquet π (unipRad k (dropPlacing d o ho hz f))
      ((leviEmb k (dropPlacing d o ho hz f)).comp (dropHom d o)) hs')
        (deltaHalf k fun j => Fin (d j))⁻¹ =
      ((jac (dropPlacing d o ho hz f) π).comp (dropHom d o) :
        Representation ℂ (Levi k fun j => Fin (d j)) _) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun v => ?_
    rw [twist_apply, MonoidHom.comp_apply]
    show _ = twist _ _ _ v
    rw [twist_apply, MonoidHom.inv_apply, MonoidHom.inv_apply,
      GlobalTheory.CompanionTheory.FineProd.ProdDrop.deltaHalf_drop d o ho hz g]
    rfl
  rw [← e]
  exact ⟨φ⟩

theorem jhMult_jac_ne_zero_of_jm (y : Fin r → IrrGL k) (o : Fin r' → Fin r) (ho : StrictMono o)
    (hz : ∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) (hd : ∑ a, (y (o a)).1 = N)
    (f : (Σ j, Fin (y j).1) ≃ Fin N) (π : Representation ℂ (GL (Fin N) k) V)
    (h : jm (fun a => y (o a)) hd π ≠ 0) :
    jhMult (piTensor fun j => (y j).rep) (jac f π) ≠ 0 := by
  obtain ⟨φ⟩ := GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv y o ho hz
  obtain ⟨ψ⟩ := jac_dropPlacing_equiv (fun j => (y j).1) o ho hz f π
  obtain ⟨χ⟩ := (Placing.parInd_jac_placing k _ _ _
    (stdBlocks (fun a => (y (o a)).1) hd) (dropPlacing (fun j => (y j).1) o ho hz f) V).2 π
  have h1 : IsSubquotient (piTensor fun a => (y (o a)).rep)
      (jac (dropPlacing (fun j => (y j).1) o ho hz f) π) :=
    (jhMult_ne_zero_iff.1 h).trans (.of_injective χ.toIntertwiningMap χ.toLinearEquiv.injective)
  have h2 := isSubquotient_pullback (dropHom (k := k) (fun j => (y j).1) o) h1
  exact jhMult_ne_zero_iff.2
    ((IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans
      (h2.trans (.of_injective ψ.symm.toIntertwiningMap ψ.symm.toLinearEquiv.injective)))

end Local

theorem sigma_clOf {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (x : IrrGL k) (d : ℕ) (h : d = x.1) : (⟨d, clOf x d⟩ : IrrGL k) = x := by
  subst h
  exact Sigma.ext rfl (heq_of_eq (clOf_self x))

theorem jhMult_row : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n p N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ (zz : Fin n → IrrGL k) (σ : Fin p ↪o Fin n) (c : Fin n → ℕ), (∀ a, c (σ a) = (zz (σ a)).1) → (∀ j, j ∉ Set.range σ → c j = 0) → ∀ (hz : ∑ a, (zz (σ a)).1 = N) (f : (Σ j, Fin (c j)) ≃ Fin N), jm (fun a => zz (σ a)) hz π ≠ 0 → jhMult (piTensor fun j => (clOf (zz j) (c j)).rep.ρ) (jac f π) ≠ 0 := by
  intro k _ _ _ _ n p N V _ _ π _ zz σ c hc h0 hz f h
  let y : Fin n → IrrGL k := fun j => ⟨c j, clOf (zz j) (c j)⟩
  have hy : (fun a => y (σ a)) = fun a => zz (σ a) := funext fun a => sigma_clOf _ _ (hc a)
  have key : ∀ (x x' : Fin p → IrrGL k) (_ : x = x') (hx : ∑ a, (x a).1 = N) (hx' : ∑ a, (x' a).1 = N),
      jm x hx π = jm x' hx' π := by
    rintro x _ rfl _ _
    rfl
  have hd : ∑ a, (y (σ a)).1 = N := by
    rw [← hz]
    exact Finset.sum_congr rfl fun a _ => hc a
  exact jhMult_jac_ne_zero_of_jm y σ σ.strictMono
    (fun j hj => by_contra fun hn => hj (h0 j hn)) hd f π (by rwa [key _ _ hy hd hz])

end GlobalTheory.CompanionTheory.WordProd.RowCell

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetTwoFactorCentralCharacterMulStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_two_factor_central_character_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), ∀ (x : Fin 2 → IrrGL k) (hd : ∑ a, (x a).1 = N), Zc.jm x hd π ≠ 0 → ∀ (t : kˣ) (c c0 c1 : ℂ), (∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v) → Zl.ScalarBy (x 0) t c0 → Zl.ScalarBy (x 1) t c1 → c0 * c1 = c := by
  first | exact @GlobalTheory.CompanionTheory.JacCentral.scalar_mul_eq | exact GlobalTheory.CompanionTheory.JacCentral.scalar_mul_eq | (intros; apply GlobalTheory.CompanionTheory.JacCentral.scalar_mul_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionBoundStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_eigenfunction_bound : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∃ C₀ : ℝ, ∀ ψ : GA E N → ℂ, Continuous ψ → (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) →
  (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
  ∀ (x : GA E N) (k : ℕ), {γ : GA E N | γ ∈ latticeGL E N ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k →
    ‖ψ x‖ ^ 2 ≤ C₀ * k := by
  first | exact @GlobalTheory.CompanionTheory.Conc.besselPt | exact GlobalTheory.CompanionTheory.Conc.besselPt | (intros; apply GlobalTheory.CompanionTheory.Conc.besselPt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KilledByPolynomialSmoothingStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.killed_by_polynomial_smoothing : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ) (r : ℕ) (p : ℂ[X]), Ker ν β → 0 < r → r < n → Continuous f →
  An.Kill r f p → An.Kill r (sm ν β f) p := by
  first | exact @GlobalTheory.CompanionTheory.Conc.kill_sm | exact GlobalTheory.CompanionTheory.Conc.kill_sm | (intros; apply GlobalTheory.CompanionTheory.Conc.kill_sm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisLeft
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem glue_r : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₁ : ObjectProperty E.C₁) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₂) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → U₁ (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun U₁ (capU V S) (capU W S) (h₁ S) (h₂ S)) → E.Kun U₁ (capU V ∅) (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  intro hM hC K _ E U₁ ι _ _ V W hV hW h₁ h₂ hK
  refine GlobalTheory.T.cosieve_pairing_family_compat hM hC E.F₂ E.F₃ (fun a => CH.cx (U₁.ι ⋙ E.F₁ a))
    (fun U U' => (∀ T, U' T → U₁ (E.L₁.obj T)) ∧ (∀ T, U' T → U (E.L₂.obj T)))
    (fun U U' r {a a' c} ha => E.pr U₁ U U' r.1 r.2 ha) ?_ V W hV hW (fun S => ⟨h₁ S, h₂ S⟩)
    (fun S hS => hK S hS)
  intro A B A' B' r₁ r₂ k k' a a' c ha i j n hn x y
  have h := GlobalTheory.T.pairing_restrict_compat E r₁.1 r₁.2 r₂.1 r₂.2 (le_refl U₁) k k' ha hn x y
  rw [GlobalTheory.T.restrict_self_pullC_eq] at h
  exact h

end GlobalTheory.CompanionTheory.KunGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethMayerVietorisRight
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem mapH_id_bij {K : Type} [Field K] (C : Cx.{1} K) (n : ℕ) :
    Function.Bijective ((Cx.Hom.id C).mapH n) := by
  have h : ∀ x : C.H n, (Cx.Hom.id C).mapH n x = x := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  exact ⟨fun x y e => by simpa only [h] using e, fun y => ⟨y, h y⟩⟩

theorem swapPr_swapPr_apply {K : Type} [Field K] {P Q T : ℕ → Cx.{1} K}
    (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) {a a' c : ℕ} (ha : a + a' = c)
    {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j) :
    (swapPr (P := Q) (Q := P) (T := T) (fun {a a' c} ha => swapPr pr ha) ha).μ h x y = (pr ha).μ h x y := by
  simp only [swapPr, LinearMap.smul_apply, LinearMap.flip_apply, smul_smul]
  have s : ((-1 : ℤ) ^ (i * j) * (-1) ^ (j * i)) = 1 := by
    rw [mul_comm j i, ← mul_pow]
    simp
  rw [s, one_smul]

theorem glue_l : MVBij → CovDesc → ∀ {K : Type} [Field K] (E : XD K) (U₂ : ObjectProperty E.C₂) {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T)) (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T)), (∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S)) → E.Kun (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) := by
  intro hMV hCD K _ E U₂ ι _ _ V W hV hW h₁ h₂ hK
  let Rel : ObjectProperty E.C₁ → ObjectProperty E.D → Prop := fun U U' =>
    (∀ T, U' T → U (E.L₁.obj T)) ∧ (∀ T, U' T → U₂ (E.L₂.obj T))
  let prr : ∀ (U : ObjectProperty E.C₁) (U' : ObjectProperty E.D), Rel U U' → ∀ {a a' c : ℕ}, a + a' = c →
      CxPairing (CH.cx (U₂.ι ⋙ E.F₂ a)) (CH.cx (U.ι ⋙ E.F₁ a')) (CH.cx (U'.ι ⋙ E.F₃ c)) :=
    fun U U' r {a a' c} ha =>
      swapPr (P := fun a => CH.cx (U.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a))
        (T := fun c => CH.cx (U'.ι ⋙ E.F₃ c)) (fun {a a' c} ha => E.pr U U₂ U' r.1 r.2 ha) ha
  have hnat : ∀ {U₁ U₂' : ObjectProperty E.C₁} {U₁' U₂'' : ObjectProperty E.D} (r₁ : Rel U₁ U₁') (r₂ : Rel U₂' U₂'')
      (k : U₂' ≤ U₁) (k' : U₂'' ≤ U₁') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n)
      (x : (CH.cx (U₂.ι ⋙ E.F₂ a)).X i) (y : CH.Cn (U₁.ι ⋙ E.F₁ a') j),
      (resU (E.F₃ c) k').pullC n ((prr U₁ U₁' r₁ ha).μ hn x y) = (prr U₂' U₂'' r₂ ha).μ hn x ((resU (E.F₁ a') k).pullC j y) := by
    intro U₁ U₂' U₁' U₂'' r₁ r₂ k k' a a' c ha i j n hn x y
    simp only [prr, swapPr, LinearMap.smul_apply, LinearMap.flip_apply, map_zsmul]
    rw [GlobalTheory.T.pairing_restrict_compat E r₁.1 r₁.2 r₂.1 r₂.2 k (le_refl U₂) k' (show a' + a = c by omega) (show j + i = n by omega) y x,
      GlobalTheory.T.restrict_self_pullC_eq (E.F₂ a) U₂ (le_refl U₂) i x]
  have key := GlobalTheory.T.cosieve_pairing_family_compat hMV hCD E.F₁ E.F₃ (fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) Rel prr hnat V W hV hW
    (fun S => ⟨h₁ S, h₂ S⟩) (fun S hS => GlobalTheory.T.kuenneth_swap _ (hK S hS))
  have k2 := GlobalTheory.T.kuenneth_swap _ key
  refine (GlobalTheory.T.pairing_iso_of_component_isos _ _ (fun a => Cx.Hom.id _) (fun a => Cx.Hom.id _) (fun a => Cx.Hom.id _)
    (fun a n => mapH_id_bij _ n) (fun a n => mapH_id_bij _ n) (fun a n => mapH_id_bij _ n) ?_).1 k2
  intro a a' c ha i j n h x y
  exact swapPr_swapPr_apply (P := fun a => CH.cx ((capU V ∅).ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a))
    (T := fun c => CH.cx ((capU W ∅).ι ⋙ E.F₃ c)) (fun {a a' c} ha => E.pr (capU V ∅) U₂ (capU W ∅) (h₁ ∅) (h₂ ∅) ha) ha h x y

end GlobalTheory.CompanionTheory.KunGlue
end

