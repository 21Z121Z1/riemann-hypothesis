import Mathlib
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegTwo
import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.Bundle0001
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskySegments.SegDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0376
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0626
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import CompanionTheory.AutomorphicTheory.SegmentRepresentations.IrreducibleSegments.IsIrreduciblePiTensorSegTerm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0069
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0651
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0070
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

-- bundled from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.ExistsPermOfIsSubquotientJac
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.Perm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem entries_zero_or_d {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin d)
    (s : ∀ i j, IrrRep (GL (Fin (b.1 i j)) k))
    (hs : ∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (segTerm σ.ρ l i))) :
    ∀ i j, b.1 i j = 0 ∨ b.1 i j = d := by
  intro i j₀
  by_contra hc
  push Not at hc
  have h0 : 0 < b.1 i j₀ := Nat.pos_of_ne_zero hc.1
  have h1 : b.1 i j₀ < d := lt_of_le_of_ne (MultOne.entry_le b i j₀) hc.2
  obtain ⟨j₁, hj, h2⟩ := MultOne.exists_other b h1
  have hcu : IsCuspidal (segTerm σ.ρ l i) :=
    GlobalTheory.LocGL.isCuspidal_twist hσ (isSmoothChar_of_isUnram (isUnram_absPow k _))
  have hne : unipRad k (f i) ≠ ⊥ := by
    refine GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff.2 ?_
    have e0 : blk (f i) (f i ⟨j₀, ⟨0, h0⟩⟩) = j₀ := by simp [blk]
    have e1 : blk (f i) (f i ⟨j₁, ⟨0, h2⟩⟩) = j₁ := by simp [blk]
    rcases lt_or_gt_of_ne hj with hlt | hlt
    · exact ⟨_, _, e1.symm ▸ e0.symm ▸ hlt⟩
    · exact ⟨_, _, e0.symm ▸ e1.symm ▸ hlt⟩
  haveI := hcu.2 l (fun j => b.1 i j) (f i) hne
  have hirr : (piTensor fun j => (s i j).ρ).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun j => (s i j).irr)
      fun j φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (s i j).smooth (s i j).irr φ hφ
  exact jhMult_ne_zero_iff.2 (hs i) (jhMult_of_subsingleton hirr _)

open GlobalTheory.LocGL in

theorem row_of_eq {d r : ℕ} (c : Fin r → ℕ) (j₀ : Fin r) (h0 : ∀ j, j ≠ j₀ → c j = 0) (hcd : c j₀ = d)
    (f : (Σ j, Fin (c j)) ≃ Fin d) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin d) k) V) (hτs : IsSmooth τ) (hτ : τ.IsIrreducible)
    (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (hs : IsSubquotient (piTensor fun j => (s j).ρ) (jac f τ)) :
    IrrGL.of (s j₀).ρ (s j₀).smooth (s j₀).irr = IrrGL.of τ hτs hτ := by
  subst hcd
  have h1 := GlobalTheory.CompanionTheory.Hypotheses₂.TD.isSubquotient_comp_mulSingle (fun j => (s j).ρ) (fun j => (s j).irr) j₀
  have h2 := h1.trans (SupportUnique.isSubquotient_comp hs
    (MonoidHom.mulSingle (fun j => GL (Fin (c j)) k) j₀))
  have h3 := h2.trans (SupportUnique.isSubquotient_jac_single j₀ h0 f τ)
  obtain ⟨φ⟩ := SupportUnique.nonempty_equiv_of_isSubquotient (s j₀).irr hτ h3
  exact IrrGL.of_eq_of.2 ⟨φ.symm⟩

open GlobalTheory.LocGL in

theorem col_of_eq {d r : ℕ} (c : Fin r → ℕ) (i₀ : Fin r) (h0 : ∀ i, i ≠ i₀ → c i = 0)
    (g : (Σ i, Fin (c i)) ≃ Fin d) (t : ∀ i, IrrRep (GL (Fin (c i)) k)) {V : Type} [AddCommGroup V]
    [Module ℂ V] (τ : Representation ℂ (GL (Fin d) k) V) (hτs : IsSmooth τ) (hτ : τ.IsIrreducible)
    (h : IrrGL.of (t i₀).ρ (t i₀).smooth (t i₀).irr = IrrGL.of τ hτs hτ) :
    Nonempty ((multiProd g fun i => (t i).ρ).Equiv τ) := by
  have hcd : c i₀ = d := congrArg Sigma.fst h
  subst hcd
  obtain ⟨φ⟩ := IrrGL.of_eq_of.1 h
  obtain ⟨ψ⟩ := GlobalTheory.CompanionTheory.WordProd.OneBlockProd.multiProd_single c i₀ h0 t g
  exact ⟨ψ.trans φ⟩

theorem eq_of_eq_d {d l : ℕ} (hd : 0 < d) (c : Fin l → ℕ) (hsum : ∑ j, c j = d) {j j' : Fin l}
    (hj : c j = d) (hj' : c j' = d) : j = j' := by
  classical
  by_contra hne
  have h := Finset.sum_le_sum_of_subset (f := c) (Finset.subset_univ {j, j'})
  rw [Finset.sum_pair hne, hsum, hj, hj'] at h
  omega

theorem exists_eq_d {d l : ℕ} (hd : 0 < d) (c : Fin l → ℕ) (hsum : ∑ j, c j = d)
    (h01 : ∀ j, c j = 0 ∨ c j = d) : ∃ j, c j = d := by
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := c) (by omega)
  exact ⟨j, (h01 j).resolve_left hj⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_perm_of_cell {d l : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (b : SizeMatrix (fun _ : Fin l => Fin d) (fun _ : Fin l => Fin d))
    (h01 : ∀ i j, b.1 i j = 0 ∨ b.1 i j = d)
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin d) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin d)
    (s : ∀ i j, IrrRep (GL (Fin (b.1 i j)) k))
    (hs : ∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (segTerm σ.ρ l i)))
    {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hπ : π.IsIrreducible)
    (h : IsSubquotient π (piTensor fun j => multiProd (g j) fun i => (s i j).ρ)) :
    ∃ w : Equiv.Perm (Fin l), Nonempty (π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) := by
  classical
  have hr : ∀ i, ∑ j, b.1 i j = d := fun i => by simpa using b.2.1 i
  have hc : ∀ j, ∑ i, b.1 i j = d := fun j => by simpa using b.2.2 j
  choose v hv using fun j => exists_eq_d hd (fun i => b.1 i j) (hc j) (fun i => h01 i j)
  have hvinj : Function.Injective v := fun j j' e =>
    eq_of_eq_d hd (b.1 (v j)) (hr (v j)) (hv j) (e ▸ hv j')
  let w : Equiv.Perm (Fin l) := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hvinj)
  refine ⟨w, ?_⟩
  have hE : ∀ j, Nonempty ((multiProd (g j) fun i => (s i j).ρ).Equiv (segTerm σ.ρ l (v j))) := by
    intro j
    refine col_of_eq (fun i => b.1 i j) (v j) (fun i hi => ?_) (g j) (fun i => s i j) _
      (MultOne.isSmooth_segTerm σ _) (MultOne.isIrreducible_segTerm σ _) ?_
    · exact (h01 i j).resolve_right fun h => hi (eq_of_eq_d hd (fun i => b.1 i j) (hc j) h (hv j))
    · exact row_of_eq (b.1 (v j)) j
        (fun j' hj' => (h01 (v j) j').resolve_right fun h => hj' (eq_of_eq_d hd _ (hr (v j)) h (hv j)))
        (hv j) (f (v j)) _ _ _ (s (v j)) (hs (v j))
  let E := GlobalTheory.LocGL.piTensorEquiv fun j => (hE j).some
  have hT : (piTensor fun j => segTerm σ.ρ l (v j)).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => MultOne.isIrreducible_segTerm σ _)
      fun a φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (MultOne.isSmooth_segTerm σ _)
        (MultOne.isIrreducible_segTerm σ _) φ hφ
  have h' := h.trans (IsSubquotient.of_injective E.toIntertwiningMap E.toLinearEquiv.injective)
  obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportUnique.nonempty_equiv_of_isSubquotient hπ hT h'
  exact ⟨φ.symm⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_perm_of_isSubquotient_jac (hG : GeometricLemma) {d l : ℕ} (hd : 0 < d) (hl : 0 < l)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    {X : Type} [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X)
    (hπ : π.IsIrreducible)
    (h : IsSubquotient π (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l)))) :
    ∃ w : Equiv.Perm (Fin l), Nonempty (π.Equiv (piTensor fun a => segTerm σ.ρ l (w a))) := by
  obtain ⟨b, f, g, s, hs, hπs⟩ := exists_cell_of_isSubquotient (hG k).1 (hG k).2
    (consecBlocks l d) (consecBlocks l d) (MultOne.isSmooth_segTerm σ)
    (MultOne.hasFiniteLength_segTerm σ) hπ h
  exact exists_perm_of_cell hd σ hσ b (entries_zero_or_d hd σ hσ b f s hs) f g s hs π hπ hπs

end CompanionTheory.Pf1.SegRepC.Perm

end
end

-- bundled from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.ExistsUniqueIrredSub
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.LocGL GlobalTheory.Published

namespace CompanionTheory.Pf1.SegRepC.Uniq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_unique_irred_sub {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ)
    (h1 : jhMult (piTensor (segTerm σ.ρ l))
      (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) = 1) :
    ∃ S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S.toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
        S'.toRepresentation.IsIrreducible → S' = S) ∧
      jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) S.toRepresentation) = 1 := by
  have hρ := CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l
  have hsρ : IsSmooth (piTensor (segTerm σ.ρ l)) := isSmooth_piTensor fun a =>
    isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))
  have hsπ : IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := isSmooth_parInd _ _
  have := GlobalTheory.CompanionTheory.SocleJm.nontrivial_indSp (consecBlocks l d) hρ hsρ
  have hfl : HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)
  have hone : ∀ T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)), IsAtom T →
      1 ≤ jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) T.toRepresentation) :=
    GlobalTheory.CompanionTheory.SocleJm.one_le_jhMult_jac_atom _ hρ
  have hjm : jhMult (piTensor (segTerm σ.ρ l)) (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) ≤ 1 := h1.le
  have hsoc : ∃ τ : IrrRep (GL (Fin (l * d)) k), IsSocle τ.ρ (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.SocleJm.exists_isSocle_of_forall_isAtom (π := multiProd (consecBlocks l d) (segTerm σ.ρ l)) (consecBlocks l d) hρ hsπ hfl hone hjm
  obtain ⟨τ, hτ, f, hf, hS⟩ := hsoc
  have hat : IsAtom f.range := isAtom_range hτ f hf
  have hatom : ∀ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible → IsAtom S' := fun S' hS' => by
    let g : S'.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ⟨S'.toSubmodule.subtype, fun _ => rfl⟩
    have hr : g.range = S' := Subrepresentation.toSubmodule_injective (Submodule.range_subtype _)
    have h := isAtom_range hS' g Subtype.val_injective
    rwa [hr] at h
  refine ⟨f.range, GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom _ hat,
    fun S' hS' => hS S' (hatom S' hS'), le_antisymm ?_ ?_⟩
  · let ι : f.range.toRepresentation.IntertwiningMap (multiProd (consecBlocks l d) (segTerm σ.ρ l)) := ⟨f.range.toSubmodule.subtype, fun _ => rfl⟩
    have hinj : Function.Injective (jacMap (consecBlocks l d) ι) :=
      GlobalTheory.JacInj.jacMap_injective k _ _ _ (consecBlocks l d) _ _ f.range.toRepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)) ι hsπ
        Subtype.val_injective
    exact (GlobalTheory.CompanionTheory.SocleJm.jhMult_le_of_injective hρ (jacMap (consecBlocks l d) ι) hinj).trans hjm
  · exact hone _ hat

end CompanionTheory.Pf1.SegRepC.Uniq

end
end

-- bundled from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.HasFiniteLengthJacSub
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.SegTwo

def RhoNuRhoReducible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ), 0 < d → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def revTensor {d : ℕ} (σ : IrrRep (GL (Fin d) k)) :=
  piTensor fun a : Fin 2 => segTerm σ.ρ 2 a.rev

theorem isSmooth_segTerm' {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    IsSmooth (segTerm σ.ρ l a) :=
  isSmooth_twist σ.smooth (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem isIrreducible_segTerm' {d l : ℕ} (σ : IrrRep (GL (Fin d) k)) (a : Fin l) :
    (segTerm σ.ρ l a).IsIrreducible :=
  GlobalTheory.LocGL.isIrreducible_twist σ.irr _

set_option synthInstance.maxHeartbeats 400000 in

theorem isIrreducible_segTensor {d : ℕ} (hd : 0 < d) (σ : IrrRep (GL (Fin d) k)) :
    (piTensor (segTerm σ.ρ 2)).IsIrreducible :=
  GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => isIrreducible_segTerm' σ a)
    fun a φ hφ => GlobalTheory.CompanionTheory.SocleFrob.exists_eq_smul_id _ (isSmooth_segTerm' σ a)
      (isIrreducible_segTerm' σ a) φ hφ

set_option synthInstance.maxHeartbeats 400000 in

theorem hasFiniteLength_jac_sub {d : ℕ} (hd : 0 < d)
    (σ : IrrRep (GL (Fin d) k)) (hσ : IsCuspidal σ.ρ)
    (S : Subrepresentation (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2))) :
    HasFiniteLength (jac (consecBlocks 2 d) S.toRepresentation) := by
  have hsρ : IsSmooth (piTensor (segTerm σ.ρ 2)) := isSmooth_piTensor fun a =>
    isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))
  have hρ := CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ 2
  have hsπ : IsSmooth (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)) := isSmooth_parInd _ _
  have hfl : HasFiniteLength (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)) :=
    GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)
  have hsS : IsSmooth S.toRepresentation := GlobalTheory.CompanionTheory.JacExp.isSmooth_sub hsπ S
  have hflS : HasFiniteLength S.toRepresentation :=
    GlobalTheory.CompanionTheory.IrrSub.hasFiniteLength_of_isSubquotient
      (IsSubquotient.of_injective ⟨S.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective) hfl
  exact (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).2.1 _ _ _ (consecBlocks 2 d) _ S.toRepresentation hsS hflS

end CompanionTheory.Pf1.SegRepC.SegTwo

end
end

-- bundled from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.IsSubquotientJacMultiProdOfSub
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.Lift

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmooth_multiProd_segTerm {d : ℕ} (σ : IrrRep (GL (Fin d) k)) (l : ℕ) :
    IsSmooth (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
  isSmooth_parInd _ _

set_option synthInstance.maxHeartbeats 400000 in

theorem isSubquotient_jac_multiProd_of_sub {d l : ℕ} (σ : IrrRep (GL (Fin d) k))
    (S : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
    {X : Type} [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X}
    (h : IsSubquotient π (jac (consecBlocks l d) S.toRepresentation)) :
    IsSubquotient π (jac (consecBlocks l d) (multiProd (consecBlocks l d) (segTerm σ.ρ l))) :=
  h.trans (GlobalTheory.JacquetExact.isSubquotient_jac (d := fun _ => d) (consecBlocks l d)
    (isSmooth_multiProd_segTerm σ l)
    (IsSubquotient.of_injective ⟨S.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective))

theorem perm_eq_one_of_lt_succ {l : ℕ} (w : Equiv.Perm (Fin l))
    (h : ∀ (i : ℕ) (hi : i + 1 < l), w.symm ⟨i, by omega⟩ < w.symm ⟨i + 1, hi⟩) : w = 1 := by
  cases l with
  | zero => exact Subsingleton.elim _ _
  | succ n =>
    have hm : StrictMono w.symm := Fin.strictMono_iff_lt_succ.2 fun i => h i.1 (by omega)
    have he : ∀ y, w.symm y = y := fun y => by
      have := congrArg (fun e : Fin (n + 1) ≃o Fin (n + 1) => e y)
        (Subsingleton.elim (hm.orderIsoOfSurjective _ w.symm.surjective) (OrderIso.refl _))
      simpa using this
    ext x
    have hx := he (w x)
    simp only [Equiv.symm_apply_apply] at hx
    simp [← hx]

end CompanionTheory.Pf1.SegRepC.Lift

end
end

-- bundled from CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.IsSubquotientJacOfLe
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.PiLocalization₂

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option synthInstance.maxHeartbeats 400000 in

theorem exists_irred_le {d l : ℕ} (hd : 0 < d) (hl : 0 < l) (σ : IrrRep (GL (Fin d) k))
    (hσ : IsCuspidal σ.ρ) (T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)))
    (hT : T.toSubmodule ≠ ⊥) :
    ∃ S' : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l)),
      S'.toRepresentation.IsIrreducible ∧ S'.toSubmodule ≤ T.toSubmodule := by
  have hρ := CompanionTheory.Lit1.SegRep.PIrr.isIrreducible_piTensor_segTerm σ l
  have hsρ : IsSmooth (piTensor (segTerm σ.ρ l)) := isSmooth_piTensor fun a =>
    isSmooth_twist σ.smooth (IsSmoothChar.detChar (GlobalTheory.LocGL.isSmoothChar_absPow _))
  have hfl : HasFiniteLength (multiProd (consecBlocks l d) (segTerm σ.ρ l)) :=
    GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength k _ _ _ _ _ _ hsρ (hasFiniteLength_of_isIrreducible hρ)
  have hT' : T ≠ ⊥ := fun h => hT (by rw [h]; rfl)
  obtain ⟨S, hS, hle⟩ := GlobalTheory.CompanionTheory.JacExp.exists_atom_le hfl hT'
  exact ⟨S, GlobalTheory.ClassFin.isIrreducible_toRepresentation_of_isAtom _ hS, hle⟩

set_option synthInstance.maxHeartbeats 400000 in

theorem isSubquotient_jac_of_le {d l : ℕ} (σ : IrrRep (GL (Fin d) k))
    {S T : Subrepresentation (multiProd (consecBlocks l d) (segTerm σ.ρ l))} (hST : S.toSubmodule ≤ T.toSubmodule)
    {X : Type} [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (Levi k fun _ : Fin l => Fin d) X}
    (h : IsSubquotient π (jac (consecBlocks l d) S.toRepresentation)) :
    IsSubquotient π (jac (consecBlocks l d) T.toRepresentation) :=
  h.trans (GlobalTheory.JacquetExact.isSubquotient_jac (d := fun _ => d) (consecBlocks l d)
    (GlobalTheory.CompanionTheory.JacExp.isSmooth_sub (isSmooth_parInd _ _) T)
    (IsSubquotient.of_injective ⟨Submodule.inclusion hST, fun _ => rfl⟩ (Submodule.inclusion_injective hST)))

end CompanionTheory.Pf1.SegRepC.PiLocalization₂

end
end

