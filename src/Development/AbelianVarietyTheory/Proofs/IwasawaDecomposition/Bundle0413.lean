import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0404
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0939
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Columns.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RTupQEqOneIff
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowAct

section Gen

variable {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

theorem parLev_of_Q (q : (levEnv V β L).Q) :
    Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _) ∈ parLev D.sp.cm V.gram β L := q.2.1

def rTupQ : (levEnv V β L).Q →* G0 L.Pg L.r where
  toFun q := rTup β L (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _))
  map_one' := by
    simp only [OneMemClass.coe_one, map_one]
    exact rTup_one
  map_mul' x y := by
    simp only [Subgroup.coe_mul, map_mul]
    exact rTup_mul (parLev_of_Q V β L x) (parLev_of_Q V β L y)

theorem rTupQ_apply (q : (levEnv V β L).Q) :
    rTupQ V β L q = rTup β L (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf V) : GL _ _)) := rfl

theorem rTupQ_eq_one_iff (q : (levEnv V β L).Q) :
    rTupQ V β L q = 1 ↔ ((q : Bridge.Gf V)) ∈ (levEnv V β L).J := by
  constructor
  · intro h
    exact ⟨parLev_of_Q V β L q, Subgroup.mem_bot.2 h⟩
  · intro h
    exact Subgroup.mem_bot.1 h.2

end Gen

end GlobalTheory.Mem.R3.RowAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankEquivariantHomsIntoIsotypicSumOfIso
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.MultIso

variable {H S0 S X : Type} [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S]
  [AddCommGroup X] [Module ℂ X]

def precomp (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (B : Submodule ℂ X)
    (φ : S →ₗ[ℂ] S0) (hφ : ∀ g s, φ (σ g s) = σ0 g (φ s)) : homInto σ0 ρ B →ₗ[ℂ] homInto σ ρ B where
  toFun T := ⟨T.1 ∘ₗ φ, fun s => T.2.1 (φ s), fun g s => by
    show T.1 (φ (σ g s)) = ρ g (T.1 (φ s))
    rw [hφ]; exact T.2.2 g (φ s)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rank_homInto_of_asModule (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X)
    (B : Submodule ℂ X) (e : σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) :
    Module.rank ℂ (homInto σ ρ B) = Module.rank ℂ (homInto σ0 ρ B) := by
  let φ : S →ₗ[ℂ] S0 :=
    { toFun := fun s => σ0.asModuleEquiv (e (σ.asModuleEquiv.symm s))
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        rw [show e (c • σ.asModuleEquiv.symm a) = c • e (σ.asModuleEquiv.symm a) from
          LinearMap.map_smul_of_tower e.toLinearMap c _, map_smul] }
  let ψ : S0 →ₗ[ℂ] S :=
    { toFun := fun s => σ.asModuleEquiv (e.symm (σ0.asModuleEquiv.symm s))
      map_add' := fun a b => by simp
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        rw [show e.symm (c • σ0.asModuleEquiv.symm a) = c • e.symm (σ0.asModuleEquiv.symm a) from
          LinearMap.map_smul_of_tower e.symm.toLinearMap c _, map_smul] }
  have hφψ : ∀ s, φ (ψ s) = s := fun s => by simp [φ, ψ]
  have hψφ : ∀ s, ψ (φ s) = s := fun s => by simp [φ, ψ]
  have φeq : ∀ g s, φ (σ g s) = σ0 g (φ s) := fun g s => by
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
  have ψeq : ∀ g s, ψ (σ0 g s) = σ g (ψ s) := fun g s => by
    simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Representation.asModuleEquiv_symm_map_rho, map_smul, Representation.asModuleEquiv_map_smul,
      Representation.asAlgebraHom_of]
  let E : homInto σ0 ρ B ≃ₗ[ℂ] homInto σ ρ B :=
    { precomp σ0 σ ρ B φ φeq with
      invFun := precomp σ σ0 ρ B ψ ψeq
      left_inv := fun T => Subtype.ext (LinearMap.ext fun s => by
        show T.1 (φ (ψ s)) = T.1 s
        rw [hφψ])
      right_inv := fun T => Subtype.ext (LinearMap.ext fun s => by
        show T.1 (ψ (φ s)) = T.1 s
        rw [hψφ]) }
  exact E.rank_eq.symm

theorem homInto_iSup_range (σ0 : Representation ℂ H S0) (ρ : Representation ℂ H X) (C : Submodule ℂ X) :
    homInto σ0 ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) = homInto σ0 ρ C := by
  have hle : (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) ≤ C := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨s, rfl⟩
    exact hg.1 s
  ext f
  refine ⟨fun hf => ⟨fun s => hle (hf.1 s), hf.2⟩, fun hf => ⟨fun s => ?_, hf.2⟩⟩
  exact (le_iSup₂_of_le f hf le_rfl : LinearMap.range f ≤ ⨆ g ∈ homInto σ0 ρ C, LinearMap.range g) ⟨s, rfl⟩

theorem rank_homInto_iSup_range : ∀ (H S0 S X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S]
    [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X)
    (C : Submodule ℂ X), Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) →
    Module.rank ℂ (homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g)) = Module.rank ℂ (homInto σ0 ρ C) := by
  intro H S0 S X _ _ _ _ _ _ _ σ0 σ ρ C ⟨e⟩
  rw [rank_homInto_of_asModule σ0 σ ρ _ e, homInto_iSup_range]

end GlobalTheory.MultIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankIsotypicConjTypeEqConjModel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

noncomputable section

namespace GlobalTheory.IsotConj

open GlobalTheory.ConjDim

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

theorem conjMap_zero' (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) : conjMap M M' c h 0 = 0 :=
  MultilinearMap.ext fun _ => star_zero _

theorem conjMap_add (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (T T' : MMap M) :
    conjMap M M' c h (T + T') = conjMap M M' c h T + conjMap M M' c h T' :=
  MultilinearMap.ext fun _ => star_add _ _

theorem conjMap_smul (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) (r : ℂ) (T : MMap M) :
    conjMap M M' c h (r • T) = star r • conjMap M M' c h T := by
  refine MultilinearMap.ext fun v' => ?_
  show star (r • (T : MMap M) _) = star r • star ((T : MMap M) _)
  rw [star_smul]

theorem conjMap_actM {n : ℕ} (P : principalLevelFrame.RowPsi V n) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ) (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    (k : Formalism.AUTREP.GAf D.host.E n) (T : MMap M) :
    conjMap M M' c h (principalLevelFrame.actM P M k T) = principalLevelFrame.actM P M' k (conjMap M M' c h T) :=
  MultilinearMap.ext fun _ => funext fun _ => rfl

theorem conjMap_minf (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {n : ℕ} (P : principalLevelFrame.RowPsi V n)
    (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    (hM : ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec),
      (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g))
    (T : MMap M) (hT : T ∈ principalLevelFrame.Minf θ P M) : conjMap M M' c h T ∈ principalLevelFrame.Minf θ P M' := by
  unfold principalLevelFrame.Minf at hT ⊢
  refine Submodule.iSup_induction _ (motive := fun T => conjMap M M' c h T ∈ _) hT ?_ ?_ ?_
  · intro N T hT
    obtain ⟨T', hT', e1⟩ := hM _ _ T hT
    have : conjMap M M' c h T = T' := by
      refine MultilinearMap.ext fun v' => funext fun g => ?_
      rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
      rfl
    rw [this]
    exact Submodule.mem_iSup_of_mem N (mult_congr θ M' (fun k _ => by simp) hT')
  · rw [conjMap_zero']; exact zero_mem _
  · intro T T' h1 h2
    rw [conjMap_add]; exact add_mem h1 h2

def cjS {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) (x : π.S) : (principalLevelFrame.FinTyp.conjT π).S :=
  ⟨fun g => star ((x : Formalism.AUTREP.GAf D.host.E n → ℂ) g), by
    show (fun g => star (star ((x : Formalism.AUTREP.GAf D.host.E n → ℂ) g))) ∈ π.S
    simpa using x.2⟩

theorem cjS_add {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) (x y : π.S) : cjS π (x + y) = cjS π x + cjS π y :=
  Subtype.ext (funext fun _ => star_add _ _)

theorem cjS_smul {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) (a : ℂ) (x : π.S) : cjS π (a • x) = star a • cjS π x :=
  Subtype.ext (funext fun _ => by simp [cjS, mul_comm])

theorem conjT_conjT {n : ℕ} (π : Formalism.L2.NG.FinTyp D.host.E n) : principalLevelFrame.FinTyp.conjT (principalLevelFrame.FinTyp.conjT π) = π := by
  rcases π with ⟨S0, _, _, _, _⟩
  show Formalism.L2.NG.FinTyp.mk (principalLevelFrame.conjSub (principalLevelFrame.conjSub S0)) _ _ _ _ = _
  congr 1
  exact principalLevelFrame.conjSub_conjSub S0

theorem conjMap_isot (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {n : ℕ} (P : principalLevelFrame.RowPsi V n)
    (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (h : ∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ)
    (hM : ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec),
      (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g))
    (π : Formalism.L2.NG.FinTyp D.host.E n) (T : MMap M)
    (hT : T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) (principalLevelFrame.FinTyp.conjT π)) :
    conjMap M M' c h T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M') (principalLevelFrame.Minf θ P M') π := by
  unfold principalLevelFrame.isotIn at hT
  refine Submodule.iSup_induction _ (motive := fun T => conjMap M M' c h T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M') (principalLevelFrame.Minf θ P M') π) hT ?_ ?_ ?_
  · intro Φ T hT
    refine Submodule.iSup_induction _ (motive := fun T => conjMap M M' c h T ∈ principalLevelFrame.isotIn (principalLevelFrame.actM P M') (principalLevelFrame.Minf θ P M') π) hT ?_ ?_ ?_
    · rintro ⟨hΦ, hR⟩ T ⟨f, rfl⟩
      let Ψ : π.S →ₗ[ℂ] MMap M' :=
        { toFun := fun x => conjMap M M' c h (Φ (cjS π x))
          map_add' := fun x y => by rw [cjS_add, map_add, conjMap_add]
          map_smul' := fun a x => by simp only [RingHom.id_apply]; rw [cjS_smul, map_smul, conjMap_smul, star_star] }
      have hΨ : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M') π Ψ := by
        intro k x
        show conjMap M M' c h (Φ (cjS π _)) = principalLevelFrame.actM P M' k (conjMap M M' c h (Φ (cjS π x)))
        rw [← conjMap_actM, ← hΦ k]
        rfl
      have hΨR : LinearMap.range Ψ ≤ principalLevelFrame.Minf θ P M' := by
        rintro _ ⟨x, rfl⟩
        exact conjMap_minf θ P M M' c h hM _ (hR (LinearMap.mem_range_self Φ _))
      have e : cjS π ⟨fun g => star ((f : Formalism.AUTREP.GAf D.host.E n → ℂ) g), f.2⟩ = f :=
        Subtype.ext (funext fun _ => star_star _)
      refine Submodule.mem_iSup_of_mem Ψ (Submodule.mem_iSup_of_mem ⟨hΨ, hΨR⟩ ⟨⟨fun g => star ((f : Formalism.AUTREP.GAf D.host.E n → ℂ) g), f.2⟩, ?_⟩)
      show conjMap M M' c h (Φ (cjS π _)) = conjMap M M' c h (Φ f)
      rw [e]
    · rw [conjMap_zero']; exact zero_mem _
    · intro T T' h1 h2
      rw [conjMap_add]; exact add_mem h1 h2
  · rw [conjMap_zero']; exact zero_mem _
  · intro T T' h1 h2
    rw [conjMap_add]; exact add_mem h1 h2

theorem rank_le (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S')
    (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ)
    (hc : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w))
    (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) {n : ℕ}
    (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n)
    (hχ : ∀ k ∈ J, χ' k = star (χ k)) (he : ∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) :
    Module.rank ℂ (principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π)) ≤ Module.rank ℂ (principalLevelFrame.isotL θ P M' J χ' e' π) := by
  obtain ⟨h, hM⟩ := GlobalTheory.T.complexConjugation_maps_multiplicitySpace θ M M' c hc
  have key : ∀ T ∈ principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π), conjMap M M' c h T ∈ principalLevelFrame.isotL θ P M' J χ' e' π := by
    rintro T ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨?_, ?_⟩, conjMap_isot θ P M M' c h hM π T h3⟩
    · obtain ⟨T', hT', e1⟩ := hM J χ T h1
      have : conjMap M M' c h T = T' := by
        refine MultilinearMap.ext fun v' => funext fun g => ?_
        rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
        rfl
      rw [this]
      exact mult_congr θ M' hχ hT'
    · have h2' : ∀ v, e (T v) = T v := fun v => by
        have := congrArg (fun U : MMap M => U v) (sub_eq_zero.1 (LinearMap.mem_ker.1 h2))
        exact this
      refine LinearMap.mem_ker.2 (sub_eq_zero.2 (MultilinearMap.ext fun v' => ?_))
      show e' (conjMap M M' c h T v') = conjMap M M' c h T v'
      rw [conjMap_apply, he, h2']
  let j : principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π) →+ principalLevelFrame.isotL θ P M' J χ' e' π :=
    AddMonoidHom.mk' (fun T => ⟨conjMap M M' c h T, key T T.2⟩) fun T T' =>
      Subtype.ext (MultilinearMap.ext fun v' => star_add _ _)
  refine rank_le_of_injective_injective (star : ℂ → ℂ) j (fun r hr => star_eq_zero.1 hr) ?_ ?_
  · refine (injective_iff_map_eq_zero j).2 fun T hT => Subtype.ext ?_
    exact conjMap_eq_zero M M' c h T (congrArg Subtype.val hT)
  · intro r T
    refine Subtype.ext (MultilinearMap.ext fun v' => ?_)
    show star (star r • (T : MMap M) _) = r • star ((T : MMap M) _)
    rw [star_smul, star_star]

theorem conj_rank : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → ∀ (J : Set (GA D V)) (χ χ' : GA D V → ℂ) (e e' : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), (∀ k ∈ J, χ' k = star (χ k)) → (∀ φ : GA D V → ℂ, e' (star φ) = star (e φ)) → Module.rank ℂ (principalLevelFrame.isotL θ P M J χ e (principalLevelFrame.FinTyp.conjT π)) = Module.rank ℂ (principalLevelFrame.isotL θ P M' J χ' e' π) := by
  intro D V S S' θ M M' c hc J χ χ' e e' n P π hχ he
  refine le_antisymm (rank_le θ M M' c hc J χ χ' e e' P π hχ he) ?_
  have := rank_le θ M' M (fun τ => (c τ).symm) ?_ J χ' χ e' e P (principalLevelFrame.FinTyp.conjT π) ?_ ?_
  · rwa [conjT_conjT] at this
  · intro τ g hg w
    apply (c τ).injective
    rw [hc τ g hg]
    simp
  · intro k hk
    rw [hχ k hk, star_star]
  · intro φ
    rw [← star_star φ, he, star_star, star_star]

end GlobalTheory.IsotConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowActSmulOfWeight
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.RowsSign

open MvPolynomial
open scoped ComplexOrder

section General

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem degree_of_colWeight {ν : Fin n → ℕ} (m : Fin n × Fin n →₀ ℕ)
    (h : Finsupp.weight (Formalism.GradedWeylDivisibility.colW n n) m = ν) : (m.sum fun _ k => k) = ∑ j, ν j := by
  classical
  rw [← h, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [Formalism.GradedWeylDivisibility.colW, Pi.single_apply]

theorem rowAct_smul_of_weight {R : Type} [CommRing R] {ν : Fin n → ℕ} (c : R) (g : Matrix (Fin n) (Fin n) R)
    (f : MvPolynomial (Fin n × Fin n) R) (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) f ν) :
    Formalism.GradedWeylDivisibility.rowAct R (c • g) f = c ^ (∑ j, ν j) • Formalism.GradedWeylDivisibility.rowAct R g f := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [← degree_of_colWeight m (hf (mem_support_iff.mp hm))]
  have h1 : ∀ v : Fin n × Fin n, (∑ b : Fin n, C ((c • g) v.1 b) * X (b, v.2) : MvPolynomial (Fin n × Fin n) R) =
      C c * ∑ b : Fin n, C (g v.1 b) * X (b, v.2) := by
    intro v
    simp only [Matrix.smul_apply, smul_eq_mul, C_mul, Finset.mul_sum, mul_assoc]
  simp only [Formalism.GradedWeylDivisibility.rowAct, aeval_monomial, h1, Finsupp.prod, Finsupp.sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, smul_eq_C_mul, C_pow]
  ring

def totDeg (lam : ι → DomWeight n) : ℕ := ∑ τ, ∑ j, (lam τ).natW j

theorem blockAct_smul_of_mem (lam : ι → DomWeight n) (a : K) (M : ι → Matrix (Fin n) (Fin n) K)
    {y : Formalism.L2.DIV.Pol K ι n} (hy : y ∈ VV K lam) :
    Formalism.GradedWeylDivisibility.blockAct K (fun τ => a • M τ) y = a ^ totDeg lam • Formalism.GradedWeylDivisibility.blockAct K M y := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hy
  induction hy using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨F, hF, rfl⟩ := hP
    have hT := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n (fun τ => a • M τ)).1
    have hT' := (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n M).1
    have h2 : ∀ τ, Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.rowAct K (a • M τ) (F τ)) =
        C (a ^ (∑ j, (lam τ).natW j)) * Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.rowAct K (M τ) (F τ)) := by
      intro τ
      rw [rowAct_smul_of_weight a (M τ) (F τ) (Formalism.GradedWeylDivisibility.mem_dualWeyl_iff.1 (hF τ)).1, map_smul, smul_eq_C_mul]
    rw [map_prod, map_prod]
    simp only [hT, hT']
    rw [Finset.prod_congr rfl fun τ _ => h2 τ, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum,
      smul_eq_C_mul]
    rfl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, map_smul, hx, smul_comm]

variable [StarRing K]

def negSign (lam : ι → DomWeight n) : K := gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * (-1) ^ totDeg lam

theorem pairK_neg (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) (x y : VV K lam) :
    pairK lam (fun τ => -G τ) x y = negSign lam * pairK lam G x y := by
  have hy := blockAct_smul_of_mem lam (-1 : K) (fun τ => (G τ)ᵀ) y.2
  have hT : (fun τ => (-G τ)ᵀ) = fun τ => (-1 : K) • (G τ)ᵀ := by
    funext τ
    rw [Matrix.transpose_neg, neg_one_smul]
  have hg : gramTw lam (fun τ => -G τ) = gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam G := by
    unfold gramTw
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← mul_zpow, ← Matrix.det_mul, neg_mul, one_mul]
  simp only [pairK, pairP, LinearMap.domRestrict₁₂_apply, LinearMap.smul_apply, LinearMap.compl₂_apply,
    AlgHom.toLinearMap_apply, smul_eq_mul]
  rw [hT, hy, map_smul, hg, negSign, smul_eq_mul]
  ring

theorem negSign_mul_self (lam : ι → DomWeight n) : negSign (K := K) lam * negSign lam = 1 := by
  have hd : ((-1 : Matrix (Fin n) (Fin n) K)).det * ((-1 : Matrix (Fin n) (Fin n) K)).det = 1 := by
    rw [← Matrix.det_mul, neg_mul_neg, one_mul, Matrix.det_one]
  have hz : ∀ e : ℤ, ((-1 : Matrix (Fin n) (Fin n) K)).det ^ e * ((-1 : Matrix (Fin n) (Fin n) K)).det ^ e = 1 := by
    intro e
    rw [← mul_zpow, hd, _root_.one_zpow]
  have hp : ((-1 : K) ^ totDeg lam) * (-1) ^ totDeg lam = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hgg : gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) = 1 := by
    unfold gramTw
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun τ _ => hz _
  calc negSign (K := K) lam * negSign lam
      = (gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K)) * gramTw lam (fun _ => (-1 : Matrix (Fin n) (Fin n) K))) *
        (((-1 : K) ^ totDeg lam) * (-1) ^ totDeg lam) := by unfold negSign; ring
    _ = 1 := by rw [hgg, hp, one_mul]

end General

end GlobalTheory.RowsSign

namespace GlobalTheory.RowsSign

open scoped ComplexOrder InnerProductSpace

theorem pairV_neg_one_eq {E K : Type} [Field E] [Field K] [StarRing K] {ι : Type} [Fintype ι] {n : ℕ}
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (φ : K →+* ℂ) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (c0 : VV K lam →ₛₗ[φ] W)
    (h : ∀ x y, inner ℂ (c0 x) (c0 y) = φ (pairV emb lam (-1) x y)) :
    ∀ x y, pairV emb lam (-1) x y = pairV emb lam 1 x y := by
  have hG : gramK emb (-1 : Matrix (Fin n) (Fin n) E) = fun τ => -(gramK emb 1 τ) := by
    funext τ
    ext i j
    simp [gramK, Matrix.neg_apply, Matrix.one_apply]
  have hneg : ∀ x y, pairV emb lam (-1) x y = negSign lam * pairV emb lam 1 x y := by
    intro x y
    unfold pairV
    rw [hG, pairK_neg]
  by_cases hnt : Nontrivial (VV K lam)
  · rcases mul_self_eq_one_iff.1 (negSign_mul_self (K := K) lam) with hc | hc
    · intro x y
      rw [hneg, hc, one_mul]
    · exfalso
      have hpos := Formalism.L2.DIV.pairPos K ι n lam (gramK emb 1) φ (fun τ => by
        have : ((gramK emb (1 : Matrix (Fin n) (Fin n) E) τ).map φ) = 1 := by
          ext i j
          simp [gramK, Matrix.one_apply]
        rw [this]
        exact Matrix.PosDef.one)
      obtain ⟨i⟩ := (bVV K lam).index_nonempty
      have h1 := hpos.diag_pos (i := i)
      simp only [Matrix.of_apply] at h1
      have h2 := h (bVV K lam i) (bVV K lam i)
      rw [hneg, hc, neg_one_mul, map_neg] at h2
      have h3 := inner_self_nonneg (𝕜 := ℂ) (x := c0 (bVV K lam i))
      rw [h2, map_neg, RCLike.re_to_complex] at h3
      have h4 := (Complex.lt_def.1 h1).1
      have h5 : (φ (pairV emb lam 1 (bVV K lam i) (bVV K lam i))).re =
          (φ (pairK lam (gramK emb 1) (bVV K lam i) (bVV K lam i))).re := rfl
      simp only [Complex.zero_re] at h4
      linarith
  · rw [not_nontrivial_iff_subsingleton] at hnt
    intro x y
    rw [Subsingleton.elim x 0]
    simp

end GlobalTheory.RowsSign

open GlobalTheory.RowsSign in
theorem GlobalTheory.RowsSign.pairV_gramR_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px), I.Ok → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W), cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) → Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) → (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) → ∀ x y, pairV (labLL X.toD7) (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) gramR x y = pairV (labLL X.toD7) (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) X.toD7.sp.X'.gram x y := by
  intro X px I hI cX gramR c0R hcX hg htie hinner x y
  have hJ : X.toD7.sp.X'.gram = 1 := by
    obtain ⟨hs, -, h2, -⟩ := hI.spaces
    change X.B.sp.X'.gram = 1
    rw [h2]
    refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
    simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]
  rcases hg with rfl | rfl
  · rfl
  · rw [hJ] at hinner ⊢
    exact pairV_neg_one_eq _ _ _ c0R hinner x y
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsLiftsHeckeOperatorsCommuteStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowsLifts_heckeOperators_commute : ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → ∀ a : I.ι,
  Formalism.L2.Col.HeckeCommAll (rowPts B.wts I.Ch I.sel (I.tup a)) ∅ ∧
    ∀ j : Fin B.R.m, Formalism.L2.Col.HeckeCommAll (liftPts B.wts I.Ch I.sel (I.tup a) (j.1 + 1)) ∅ := by
  first | exact @GlobalTheory.Mem.R3.Comm.rows_lifts_comm | exact GlobalTheory.Mem.R3.Comm.rows_lifts_comm | (intros; apply GlobalTheory.Mem.R3.Comm.rows_lifts_comm <;> assumption)
end

