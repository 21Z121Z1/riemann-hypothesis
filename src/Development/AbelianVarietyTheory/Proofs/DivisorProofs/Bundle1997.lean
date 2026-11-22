import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1988
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuAllData
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsTransportedActionFinitePointPreimage
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

open Topology Filter

namespace GlobalTheory.WeilTransNbhd

variable (F : Type) [Field F] [NumberField F]

theorem exists_compact_open_subgroup (κ : Type) [Fintype κ] {S : Set (κ → FiniteAdeleRing (𝓞 F) F)}
    (hS : S ∈ 𝓝 0) : ∃ U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ S := by
  classical
  have hS' : S ∈ 𝓝 (fun _ : κ => (0 : FiniteAdeleRing (𝓞 F) F)) := hS
  rw [nhds_pi, Filter.mem_pi] at hS'
  obtain ⟨I, -, t, ht, hsub⟩ := hS'
  have hO : (⋂ i, t i) ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F) := Filter.iInter_mem.2 ht
  have hbox : ∀ u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i, u i ∈ ⋂ i, t i) → u ∈ S :=
    fun u hu => hsub fun i _ => Set.mem_iInter.1 (hu i) i
  obtain ⟨N, hN, hNO⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hO
  let c : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((N : F)⁻¹)
  have hcN : (N : FiniteAdeleRing (𝓞 F) F) * c = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN.ne'), map_one]
  have hNc : c * (N : FiniteAdeleRing (𝓞 F) F) = 1 := by rw [mul_comm]; exact hcN
  let h : (κ → FiniteAdeleRing (𝓞 F) F) ≃ₜ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      invFun := fun u i => (N : FiniteAdeleRing (𝓞 F) F) * u i
      left_inv := fun u => funext fun i => by
        show (N : FiniteAdeleRing (𝓞 F) F) * (c * u i) = u i
        rw [← mul_assoc, hcN, one_mul]
      right_inv := fun u => funext fun i => by
        show c * ((N : FiniteAdeleRing (𝓞 F) F) * u i) = u i
        rw [← mul_assoc, hNc, one_mul]
      continuous_toFun := continuous_pi fun i => continuous_const.mul (continuous_apply i)
      continuous_invFun := continuous_pi fun i => continuous_const.mul (continuous_apply i) }
  let φ : (κ → FiniteAdeleRing (𝓞 F) F) →+ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun u i => c * u i
      map_zero' := by funext i; exact mul_zero c
      map_add' := fun u w => by funext i; exact mul_add c (u i) (w i) }
  let U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F) :=
    (AddSubgroup.pi Set.univ fun _ => (Formalism.UG.intAd F).toAddSubgroup).comap φ
  have hUset : (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) =
      h ⁻¹' Set.univ.pi fun _ => (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := rfl
  have hint_c : IsCompact (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.Col.rlt_isCompact_intAd
  have hint_o : IsOpen (Formalism.UG.intAd F : Set (FiniteAdeleRing (𝓞 F) F)) := Formalism.L2.SG.Pf.top_isOpen_intAd F
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hUset]; exact (isOpen_set_pi Set.finite_univ fun _ _ => hint_o).preimage h.continuous
  · rw [hUset]; exact h.isCompact_preimage.2 (isCompact_univ_pi fun _ => hint_c)
  · intro u hu
    refine hbox u fun i => ?_
    have hi : c * u i ∈ Formalism.UG.intAd F := hu i (Set.mem_univ i)
    have := hNO (c * u i) hi
    rwa [nsmul_eq_mul, ← mul_assoc, hcN, one_mul] at this

def finIdem : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))

variable {F}

theorem finIdem_smul_eq {κ : Type} (w : κ → AF F) :
    finIdem F • w = GlobalTheory.WeilCont.adeleJoin F 0 (fun i => (w i).2) := by
  funext i
  refine Prod.ext ?_ ?_
  · show (0 : InfiniteAdeleRing F) * (w i).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((0 : κ → mixedEmbedding.mixedSpace F) i)
    rw [zero_mul, Pi.zero_apply, map_zero]
  · show (1 : FiniteAdeleRing (𝓞 F) F) * (w i).2 = (w i).2
    exact one_mul _

theorem finIdem_smul_adeleJoin {κ : Type} (x : κ → FiniteAdeleRing (𝓞 F) F) :
    finIdem F • GlobalTheory.WeilCont.adeleJoin F 0 x = GlobalTheory.WeilCont.adeleJoin F 0 x :=
  finIdem_smul_eq _

theorem adeleJoin_zero_zero {κ : Type} :
    GlobalTheory.WeilCont.adeleJoin F (0 : κ → mixedEmbedding.mixedSpace F) 0 = 0 := by
  funext i
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((0 : κ → mixedEmbedding.mixedSpace F) i) = 0
  rw [Pi.zero_apply, map_zero]

theorem continuous_adeleJoin_zero {κ : Type} :
    Continuous fun x : κ → FiniteAdeleRing (𝓞 F) F => GlobalTheory.WeilCont.adeleJoin F 0 x :=
  continuous_pi fun i => (continuous_const.prodMk (continuous_apply i) :
    Continuous fun x : κ → FiniteAdeleRing (𝓞 F) F =>
      (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((0 : κ → mixedEmbedding.mixedSpace F) i), x i) :
        InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end GlobalTheory.WeilTransNbhd

end

noncomputable section

open Topology Filter

namespace GlobalTheory.WeilTransNbhd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem actAB_smul (σ : E →ₐ[F] E) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α (AF F ⊗[F] E)} {JB : Matrix β β (AF F ⊗[F] E)} (p : UG (cA σ) JA × UG (cA σ) JB) (r : AF F)
    (X : Matrix α β (AF F ⊗[F] E)) : actAB (cA σ) p (r • X) = r • actAB (cA σ) p X := by
  unfold actAB
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem actAB_mul_inv (σ : E →ₐ[F] E) {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α (AF F ⊗[F] E)} {JB : Matrix β β (AF F ⊗[F] E)} (p : UG (cA σ) JA × UG (cA σ) JB)
    (X : Matrix α β (AF F ⊗[F] E)) : actAB (cA σ) p (actAB (cA σ) p⁻¹ X) = X := by
  unfold actAB
  have h1 : ((p.1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * (((p⁻¹).1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) = 1 := by
    show ((p.1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * (((p.1)⁻¹ : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) = 1
    exact Units.mul_inv _
  have h2 : (((p⁻¹).2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ * ((p.2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ = 1 := by
    rw [← Matrix.transpose_mul]
    show ((p.2 : GL β (AF F ⊗[F] E)) * ((p.2)⁻¹ : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ = 1
    rw [Units.mul_inv, Matrix.transpose_one]
  calc _ = ((p.1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * (((p⁻¹).1 : GL α (AF F ⊗[F] E)) : Matrix α α (AF F ⊗[F] E)) * X *
        ((((p⁻¹).2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ * ((p.2 : GL β (AF F ⊗[F] E)) : Matrix β β (AF F ⊗[F] E))ᵀ) := by
        simp only [Matrix.mul_assoc]
    _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem exists_nhds_finite_preimage : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (a b : ℕ) (JA : Matrix (Fin a) (Fin a) E) (JB : Matrix (Fin b) (Fin b) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ) (L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
    IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) → IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ p0 : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB),
    ∃ N ∈ nhds p0, ∃ L₁' L₂' : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (L₁' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsOpen (L₂' : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ p ∈ N, ∀ x ∈ L₁', ∀ y ∈ L₂', ∃ x' ∈ L₁, ∃ y' ∈ L₂,
        co.e (actAB (cA σ) p (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 x', GlobalTheory.WeilCont.adeleJoin F 0 y'))) =
          (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) := by
  intro F E _ _ _ _ _ σ a b JA JB ξ κ _ co L₁ L₂ hL₁ hL₂ p0
  haveI hmt : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsModuleTopology (AF F) (Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) :=
    inferInstanceAs (IsModuleTopology (AF F) (Fin a → Fin b → AF F ⊗[F] E))
  haveI : ContinuousSMul (AF F) (Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) :=
    inferInstanceAs (ContinuousSMul (AF F) (Fin a → Fin b → AF F ⊗[F] E))
  have hce : Continuous co.e := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
  have hcs : Continuous co.e.symm := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap
  let Ψ : (UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) → (κ → AF F) × (κ → AF F) :=
    fun q => co.e (actAB (cA σ) q.1⁻¹ (co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 q.2.1, GlobalTheory.WeilCont.adeleJoin F 0 q.2.2)))
  let Φ : (UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) →
      (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) :=
    fun q => (fun i => ((Ψ q).1 i).2, fun i => ((Ψ q).2 i).2)
  have hinv : Continuous fun q : (UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) => q.1⁻¹ := continuous_fst.inv
  have hm1 : Continuous fun q : (UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) =>
      (((q.1⁻¹).1 : GL (Fin a) (AF F ⊗[F] E)) : Matrix (Fin a) (Fin a) (AF F ⊗[F] E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_fst.comp hinv))
  have hm2 : Continuous fun q : (UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) =>
      (((q.1⁻¹).2 : GL (Fin b) (AF F ⊗[F] E)) : Matrix (Fin b) (Fin b) (AF F ⊗[F] E)) :=
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_snd.comp hinv))
  have hv : Continuous fun q : (UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB)) ×
      ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)) =>
      co.e.symm (GlobalTheory.WeilCont.adeleJoin F 0 q.2.1, GlobalTheory.WeilCont.adeleJoin F 0 q.2.2) :=
    hcs.comp ((continuous_adeleJoin_zero.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_adeleJoin_zero.comp (continuous_snd.comp continuous_snd)))
  have hΨ : Continuous Ψ := hce.comp ((hm1.matrix_mul hv).matrix_mul hm2.matrix_transpose)
  have hΦ : Continuous Φ :=
    (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_fst.comp hΨ))).prodMk
      (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp (continuous_snd.comp hΨ)))
  have hΦ0 : Φ (p0, (0, 0)) = (0, 0) := by
    have : Ψ (p0, (0, 0)) = 0 := by
      simp only [Ψ, adeleJoin_zero_zero]
      rw [show ((0 : κ → AF F), (0 : κ → AF F)) = 0 from rfl, map_zero]
      rw [show actAB (cA σ) p0⁻¹ (0 : Matrix (Fin a) (Fin b) (AF F ⊗[F] E)) = 0 by
        unfold actAB; rw [Matrix.mul_zero, Matrix.zero_mul], map_zero]
    simp only [Φ, this]
    rfl
  have hopen : IsOpen (Φ ⁻¹' ((L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ×ˢ (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)))) :=
    (hL₁.prod hL₂).preimage hΦ
  have hmem : (p0, ((0 : κ → FiniteAdeleRing (𝓞 F) F), (0 : κ → FiniteAdeleRing (𝓞 F) F))) ∈
      Φ ⁻¹' ((L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ×ˢ (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F))) := by
    rw [Set.mem_preimage, hΦ0]
    exact ⟨L₁.zero_mem, L₂.zero_mem⟩
  obtain ⟨N, hN, V, hV, hNV⟩ := mem_nhds_prod_iff.1 (hopen.mem_nhds hmem)
  rw [← Prod.zero_eq_mk, nhds_prod_eq] at hV
  obtain ⟨V₁, hV₁, V₂, hV₂, hV12⟩ := mem_prod_iff.1 hV
  obtain ⟨L₁', hL₁'o, hL₁'c, hL₁'s⟩ := exists_compact_open_subgroup F κ hV₁
  obtain ⟨L₂', hL₂'o, -, hL₂'s⟩ := exists_compact_open_subgroup F κ hV₂
  refine ⟨N, hN, L₁', L₂', hL₁'o, hL₁'c, hL₂'o, fun p hp x hx y hy => ?_⟩
  have hin := hNV (Set.mk_mem_prod hp (hV12 (Set.mk_mem_prod (hL₁'s hx) (hL₂'s hy))))
  refine ⟨(Φ (p, (x, y))).1, hin.1, (Φ (p, (x, y))).2, hin.2, ?_⟩

  have hfin : (GlobalTheory.WeilCont.adeleJoin F 0 (Φ (p, (x, y))).1, GlobalTheory.WeilCont.adeleJoin F 0 (Φ (p, (x, y))).2) =
      Ψ (p, (x, y)) := by
    have e1 : Ψ (p, (x, y)) = finIdem F • Ψ (p, (x, y)) := by
      simp only [Ψ]
      conv_lhs => rw [← finIdem_smul_adeleJoin x, ← finIdem_smul_adeleJoin y, ← Prod.smul_mk, map_smul,
        actAB_smul, map_smul]
    rw [e1]
    refine Prod.ext ?_ ?_
    · rw [Prod.smul_fst, finIdem_smul_eq]
    · rw [Prod.smul_snd, finIdem_smul_eq]
  rw [hfin]
  simp only [Ψ, LinearEquiv.symm_apply_apply, actAB_mul_inv, LinearEquiv.apply_symm_apply]

end GlobalTheory.WeilTransNbhd

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupsSchroedingerFixContinuousChar
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

namespace GlobalTheory.SchrFixFin

variable {F : Type} [Field F] [NumberField F]

theorem nonarch_of_inducing {G S : Type} [AddGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
    [AddGroup S] [TopologicalSpace S] [IsTopologicalAddGroup S] (f : S →+ G) (hf : Topology.IsInducing f) :
    NonarchimedeanAddGroup S where
  is_nonarchimedean U hU := by
    rw [hf.nhds_eq_comap, map_zero, Filter.mem_comap] at hU
    obtain ⟨t, ht, hsub⟩ := hU
    obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean t ht
    exact ⟨V.comap f hf.continuous, fun x hx => hsub (hV hx)⟩

theorem nonarch_pi' {ι : Type} {G : ι → Type} [∀ i, AddGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanAddGroup (G i)] : NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, hI, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi I fun i => (K i : AddSubgroup (G i)), isOpen_set_pi hI fun i _ => (K i).isOpen⟩,
      fun x hx => hs fun i hi => hK i (hx i hi)⟩

variable (F) in

theorem nonarch_finAdeles : NonarchimedeanAddGroup (FiniteAdeleRing (𝓞 F) F) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), NonarchimedeanAddGroup (v.adicCompletionIntegers F) := fun v =>
    nonarch_of_inducing (v.adicCompletionIntegers F).subtype.toAddMonoidHom Topology.IsInducing.subtypeVal
  haveI := nonarch_pi' (G := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletionIntegers F)
  let f : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) →+ FiniteAdeleRing (𝓞 F) F :=
    { toFun := RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact NonarchimedeanAddGroup.nonarchimedean_of_emb f
    (RestrictedProduct.isOpenEmbedding_structureMap (fun v => Valued.isOpen_integer _))

def transFix {M : Type} [AddCommGroup M] (Φ : M → ℂ) : AddSubgroup M where
  carrier := {u | ∀ x, Φ (x + u) = Φ x}
  zero_mem' := fun x => by rw [add_zero]
  add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha x => by
    have := ha (x + -a)
    rw [neg_add_cancel_right] at this
    exact this.symm

theorem isOpen_transFix {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] {Φ : M → ℂ}
    (h1 : IsLocallyConstant Φ) (h2 : HasCompactSupport Φ) : IsOpen (transFix Φ : Set M) := by
  have h : ∀ᶠ u in nhds (0 : M), ∀ x ∈ tsupport Φ, Φ (x + u) = Φ x ∧ Φ (x - u) = Φ x := by
    apply h2.isCompact.eventually_forall_of_forall_eventually
    intro x _
    have a1 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 + z.1 by fun_prop)).eventually_eq (0, x)
    have a2 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 - z.1 by fun_prop)).eventually_eq (0, x)
    have a3 := (h1.comp_continuous (show Continuous fun z : M × M => z.2 by fun_prop)).eventually_eq (0, x)
    filter_upwards [a1, a2, a3] with z b1 b2 b3
    simp only [Function.comp, add_zero, sub_zero] at b1 b2 b3
    exact ⟨b1.trans b3.symm, b2.trans b3.symm⟩
  have key : ∀ᶠ u in nhds (0 : M), ∀ x, Φ (x + u) = Φ x := by
    filter_upwards [h] with u hu x
    by_cases hx : x ∈ tsupport Φ
    · exact (hu x hx).1
    · by_cases hx' : x + u ∈ tsupport Φ
      · have := (hu _ hx').2
        rw [add_sub_cancel_right] at this
        exact this.symm
      · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']
  exact AddSubgroup.isOpen_of_mem_nhds _ key

theorem adeleJoin_zero {κ : Type} (y : κ → FiniteAdeleRing (𝓞 F) F) (i : κ) :
    GlobalTheory.WeilCont.adeleJoin F 0 y i = ((0 : InfiniteAdeleRing F), y i) := by
  refine Prod.ext ?_ rfl
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0 = 0
  exact map_zero _

theorem dot_adeleJoin_zero {κ : Type} [Fintype κ] (v : κ → AdeleRing (𝓞 F) F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    v ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y = ((0 : InfiniteAdeleRing F), (fun i => (v i).2) ⬝ᵥ y) := by
  let p1 : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F := RingHom.fst _ _
  let p2 : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _
  have e1 : ∀ s : AdeleRing (𝓞 F) F, s.1 = p1 s := fun _ => rfl
  have e2 : ∀ s : AdeleRing (𝓞 F) F, s.2 = p2 s := fun _ => rfl
  refine Prod.ext ?_ ?_
  · rw [e1, dotProduct, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, adeleJoin_zero]
    exact mul_zero _
  · rw [e2, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, adeleJoin_zero]
    rfl

theorem exists_fix_pure (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ) (κ : Type) [Fintype κ]
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
      IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ x ∈ L₁, ∀ y ∈ L₂, schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) (pureA F f g) =
        pureA F f g := by
  haveI := nonarch_finAdeles F
  let χ : AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  have hχ : Continuous χ := hψ.comp (continuous_const.prodMk continuous_id)
  obtain ⟨H, hH⟩ := GlobalTheory.T.exists_subgroup_addChar_dotProduct_trivial_on_compact χ hχ κ (tsupport g) hg.2.isCompact
  let c : FiniteAdeleRing (𝓞 F) F := (⅟(2 : AdeleRing (𝓞 F) F)).2
  refine ⟨transFix g ⊓ (H : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)).comap
    (DistribSMul.toAddMonoidHom (κ → FiniteAdeleRing (𝓞 F) F) c), H, ?_, H.isOpen, ?_⟩
  · rw [AddSubgroup.coe_inf]
    exact (isOpen_transFix hg.1 hg.2).inter (H.isOpen.preimage (continuous_const_smul c))
  rintro x ⟨hx1, hx2⟩ y hy
  funext z
  have hf : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1 := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero]
    exact congrArg _ (add_zero (z i).1)
  have hgz : (fun i => ((z + GlobalTheory.WeilCont.adeleJoin F 0 x) i).2) = (fun i => (z i).2) + x := by
    funext i
    rw [Pi.add_apply, adeleJoin_zero]
    rfl
  have hz : pureA F f g (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = pureA F f g z := by
    simp only [pureA]
    rw [hf, hgz, hx1]
  simp only [schr]
  rw [hz]
  by_cases hg0 : g (fun i => (z i).2) = 0
  · simp only [pureA, hg0, mul_zero]
  have hzc : (fun i => (z i).2) ∈ tsupport g := subset_tsupport _ hg0
  have harg : z ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y + ⅟(2 : AdeleRing (𝓞 F) F) *
      (GlobalTheory.WeilCont.adeleJoin F 0 x ⬝ᵥ GlobalTheory.WeilCont.adeleJoin F 0 y) =
      ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) := by
    rw [dot_adeleJoin_zero, dot_adeleJoin_zero, smul_dotProduct]
    refine Prod.ext ?_ ?_
    · show (0 : InfiniteAdeleRing F) + (⅟(2 : AdeleRing (𝓞 F) F)).1 * 0 = 0
      rw [mul_zero, add_zero]
    · show (fun i => (z i).2) ⬝ᵥ y + c * ((fun i => (GlobalTheory.WeilCont.adeleJoin F 0 x i).2) ⬝ᵥ y) = _
      rfl
  rw [harg]
  have h1 : ψ ((0 : InfiniteAdeleRing F), (fun i => (z i).2) ⬝ᵥ y + (c • x) ⬝ᵥ y) = 1 :=
    hH _ hzc (c • x) hx2 y hy
  rw [h1, one_mul]

theorem exists_fix : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
      ∃ L₁ L₂ : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F),
        IsOpen (L₁ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsOpen (L₂ : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ x ∈ L₁, ∀ y ∈ L₂, schr ψ (GlobalTheory.WeilCont.adeleJoin F 0 x, GlobalTheory.WeilCont.adeleJoin F 0 y) Φ = Φ := by
  intro F _ _ ψ hψ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    exact exists_fix_pure ψ hψ κ f g hg
  | zero =>
    refine ⟨⊤, ⊤, isOpen_univ, isOpen_univ, fun x _ y _ => ?_⟩
    funext z
    simp [schr]
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h1
    obtain ⟨M₁, M₂, p₁, p₂, h'⟩ := h2
    refine ⟨L₁ ⊓ M₁, L₂ ⊓ M₂, by rw [AddSubgroup.coe_inf]; exact o₁.inter p₁,
      by rw [AddSubgroup.coe_inf]; exact o₂.inter p₂, fun x hx y hy => ?_⟩
    have e1 := h x hx.1 y hy.1
    have e2 := h' x hx.2 y hy.2
    funext z
    have a1 := congrFun e1 z
    have a2 := congrFun e2 z
    simp only [schr, Pi.add_apply] at a1 a2 ⊢
    rw [mul_add, a1, a2]
  | smul a Φ _ h =>
    obtain ⟨L₁, L₂, o₁, o₂, h⟩ := h
    refine ⟨L₁, L₂, o₁, o₂, fun x hx y hy => ?_⟩
    funext z
    have a1 := congrFun (h x hx y hy) z
    simp only [schr, Pi.smul_apply, smul_eq_mul] at a1 ⊢
    rw [mul_left_comm, a1]

end GlobalTheory.SchrFixFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedDictionaryBound
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevGeo.MassLev

theorem mass_components_le : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → ∑ k, muF ((U σ).X k) (x0 k) (FF k) ≤ ENNReal.ofReal (massLev D.host.E D.R.r l.M) := by
  intro hMB hTB D j H Dw l Xo c U dict hL σ hσ x0 FF hF
  obtain ⟨G, Λ, g, Λk, u, hSD, hk, hdist⟩ := GlobalTheory.T.principalLevel_components_doubleCosets_congruence D j H Dw l Xo c U dict hL σ hσ
  have hX' := fun k => GlobalTheory.T.exists_flagDomainData_principalCongruenceLevel D.host.E D.R.r l.M ((U σ).X k) (Λk k) l.three_le (hk k).2.2.2.1 (hk k).2.2.2.2.1
  choose X' hX'Gm hX'Ψ hX'p0 hX'Λ hX'Γ using hX'
  have hfm : ∀ k, ∃ y, IsOrth (X' k) y ∧ ∃ FF', IsFundSet (X' k) y FF' ∧ muF (X' k) y FF' < ⊤ :=
    fun k => GlobalTheory.finMu_all_data D.host.E D.R.r (X' k)
  choose y hy FF' hFF' _ using hfm
  have hμ : ∀ k, muF ((U σ).X k) (x0 k) (FF k) = muF (X' k) (y k) (FF' k) := by
    intro k
    obtain ⟨hGm, -, -, -, -, hgram, hfw, hbw⟩ := hk k
    refine GlobalTheory.T.covolume_eq_of_realUnitary_conj D.host.E D.R.r ((U σ).X k) (X' k) (hX'Ψ k) (u k) (x0 k) (y k) (FF k) (FF' k)
      (hX'Gm k) (hX'p0 k) (by rw [hGm]; exact hgram) ?_ ?_ (hF k).1 (hy k) (hF k).2 (hFF' k)
    · intro γ hγ
      obtain ⟨γ', hγ', hc⟩ := hfw γ hγ
      exact ⟨γ', (hX'Γ k γ').2 (by rw [hGm]; exact hγ'), hc⟩
    · intro γ' hγ'
      have := (hX'Γ k γ').1 hγ'
      rw [hGm] at this
      exact hbw γ' this
  have hunf := hL.unf σ hσ
  set Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.filter (fun τ => τ (H.rt : D.host.E) = H.rt0) with hΨdef
  have hΨ : ∀ k, (X' k).Ψ = Ψ := by
    intro k
    rw [hX'Ψ k]
    ext τ
    rw [(hunf.2.1 k).2 τ, hΨdef, Finset.mem_filter]
    simp
  rw [Finset.sum_congr rfl (fun k _ => hμ k)]
  set e := Fintype.equivFin (U σ).Comp
  rw [← e.symm.sum_comp]
  have hr : 2 ≤ D.R.r := Formalism.L2.Geo.two_le_r D
  have hTor := hTB D.host.E D.R.r l.M G Λ (by omega) (by have := l.three_le; omega) H.unram hSD
  exact hMB D.host.E D.R.r l.M _ _ G Λ Ψ (fun i => X' (e.symm i)) (fun i => g (e.symm i)) (fun i => y (e.symm i))
    (fun i => FF' (e.symm i)) hr l.three_le H.unram hSD hTor (fun i => (hk (e.symm i)).2.1)
    (fun i i' h => e.symm.injective (hdist _ _ h))
    (fun i => ⟨(hX'Gm _).trans (hk _).1, hΨ _, by rw [hX'Λ]; exact (hk _).2.2.1, fun γ => by rw [hX'Λ, hX'Γ, (hk _).1],
      hy _, hFF' _⟩)

end GlobalTheory.LevGeo.MassLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridRowLevelZeroInfUnitaryEqDatumLevelStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridRowLevel_zero_inf_unitary_eq_datumLevel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T} (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (h : 0 ≤ D.R.m), HEq (S.levRow t 0 h ⊓ UA D.sp.cm (G.V (.grid 0 D.R.m)).gram) (lev D.sp.cm D.sp.X'.gram L.βX (L.datXt t)) := by
  first | exact @GlobalTheory.FunObj.levRow_zero_eq_lev | exact GlobalTheory.FunObj.levRow_zero_eq_lev | (intros; apply GlobalTheory.FunObj.levRow_zero_eq_lev <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeTate_inclusion_raynaudExtension_algebraicPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg → ∀ (k : T.Fr →+* C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left), (letI := io.toAlgebra; PointOver P y₀.1.x k kO ψ) → HTChar p v P.Gt := by
  first | exact @GlobalTheory.CompHt.htChar_of_pointOver | exact GlobalTheory.CompHt.htChar_of_pointOver | (intros; apply GlobalTheory.CompHt.htChar_of_pointOver <;> assumption)
end

