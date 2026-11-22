import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1324
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1522
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0063
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1745
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorFormValuesMemISupFixedParts
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FrameAut.VecSemis

open GlobalTheory.UnitarySemisimple

theorem exists_irred_le_orbSpan {H V : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ H V) (B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u)
    (hp : ∀ v, 0 ≤ (B v v).re) (hd : ∀ v, B v v = 0 → v = 0) (hi : ∀ g u v, B (ρ g u) (ρ g v) = B u v)
    (hK0 : ∃ K : Subgroup H, IsOpen (K : Set H) ∧ IsCompact (K : Set H))
    (hsm : ∀ w, IsOpen {k : H | ρ k w = w})
    (hfd : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρ K))
    (y : V) (hy : y ≠ 0) :
    ∃ U : Submodule ℂ V, U ≠ ⊥ ∧ U ≤ (orbSpan ρ y).toSubmodule ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧
      (∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U) := by
  classical
  set O := orbSpan ρ y with hO
  let ρO := O.toRepresentation
  have hρO : ∀ g (w : O.toSubmodule), (ρO g w : V) = ρ g w := fun _ _ => rfl
  let BO : O.toSubmodule →ₗ⋆[ℂ] O.toSubmodule →ₗ[ℂ] ℂ := (B.comp O.toSubmodule.subtype).compl₂ O.toSubmodule.subtype
  have hBO : ∀ u w : O.toSubmodule, BO u w = B u w := fun _ _ => rfl
  have hsmO : ∀ w : O.toSubmodule, IsOpen {k : H | ρO k w = w} := by
    intro w
    convert hsm w.1 using 1
    ext k
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => by rw [← hρO, h], fun h => Subtype.ext (by rw [hρO, h])⟩
  have hfdO : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ (GlobalTheory.PRep.fixed ρO K) := by
    intro K hK
    haveI := hfd K hK
    have hle : (GlobalTheory.PRep.fixed ρO K).map O.toSubmodule.subtype ≤ GlobalTheory.PRep.fixed ρ K := by
      rintro _ ⟨w, hw, rfl⟩ k
      have h1 := hw k
      show ρ k w.1 = ((1 : K →* ℂˣ) k : ℂ) • w.1
      rw [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
      rw [← hρO, h1]
    haveI : FiniteDimensional ℂ ((GlobalTheory.PRep.fixed ρO K).map O.toSubmodule.subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ O.toSubmodule.injective_subtype _).symm
  have hy0 : (⟨y, mem_orbSpan ρ y⟩ : O.toSubmodule) ≠ 0 := fun h => hy (congrArg Subtype.val h)
  obtain ⟨U', P, hU0, hUst, hUirr, -, -, -⟩ :=
    GlobalTheory.AdmissibleProjection.exists_irreducible_equivariant_projection H O.toSubmodule ρO BO
      (fun u w => hh u w) (fun v => hp v) (fun v h => Subtype.ext (hd v h)) (fun g u w => hi g u w)
      hK0 hsmO hfdO _ hy0
  refine ⟨U'.map O.toSubmodule.subtype, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hU0
    rw [Submodule.eq_bot_iff]
    intro u hu
    have : u.1 ∈ U'.map O.toSubmodule.subtype := ⟨u, hu, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · rintro g _ ⟨u, hu, rfl⟩
    exact ⟨ρO g u, hUst g u hu, rfl⟩
  · intro N hNU hN
    let N' : Submodule ℂ O.toSubmodule := N.comap O.toSubmodule.subtype
    have hN'U : N' ≤ U' := by
      intro u hu
      obtain ⟨w, hw, hwu⟩ := hNU hu
      rw [← Subtype.ext hwu]
      exact hw
    have hN'st : ∀ g, ∀ u ∈ N', ρO g u ∈ N' := fun g u hu => hN g u.1 hu
    have hNe : N'.map O.toSubmodule.subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hNU.trans (Submodule.map_subtype_le _ _))
    rcases hUirr N' hN'U hN'st with h | h
    · left; rw [← hNe, h, Submodule.map_bot]
    · right; rw [← hNe, h]

end GlobalTheory.FrameAut.VecSemis

namespace GlobalTheory.FrameAut.VecSemis

open GlobalTheory.UnitarySemisimple GlobalTheory.DefU GlobalTheory.FrameAut.VecProj

theorem mem_iSup_of_form (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ) (hh : ∀ u v, star (B u v) = B v u) (hp : ∀ v, 0 ≤ (B v v).re)
    (hd : ∀ v, B v v = 0 → v = 0) (hi : ∀ g u v, B (autRep E n g u) (autRep E n g v) = B u v)
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W)
    (hsp : Submodule.span ℂ (Set.range ρ) = ⊤) (K : Subgroup (finU E n)) (hK : IsOpen (K : Set (finU E n)))
    (f : W →ₗ[ℂ] (UA E n → ℂ)) (hfa : ∀ u, IsAutFormU (f u)) (hfe : ∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u))
    (hfK : ∀ u, f u ∈ fixed (RF E n) K) :
    ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧
      (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := by
  classical
  set T : Submodule ℂ (UA E n → ℂ) := ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧
    ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)),
    π ⊓ fixed (RF E n) K with hT
  let Y : Submodule ℂ (forms ρ) :=
    { carrier := {g | ∀ u, g.1 u ∈ T}
      add_mem' := fun ha hb u => by
        rw [Submodule.coe_add, LinearMap.add_apply]; exact add_mem (ha u) (hb u)
      zero_mem' := fun u => by simp
      smul_mem' := fun c g hg u => by
        rw [Submodule.coe_smul, LinearMap.smul_apply]; exact T.smul_mem c (hg u) }
  let X := GlobalTheory.PRep.fixed (rep ρ) K
  haveI : FiniteDimensional ℂ X := rep_fd ρ K hK
  haveI : FiniteDimensional ℂ (X ⊓ Y : Submodule ℂ (forms ρ)) := Submodule.finiteDimensional_of_le inf_le_left
  let Bf := form B ρ
  have hBh := form_herm B hh ρ
  have hBp := form_nonneg B hp ρ
  have hBd := form_def B hh hp hd ρ
  have hBi := form_inv B hi ρ
  have memX : ∀ g : forms ρ, (∀ k ∈ K, rep ρ k g = g) → g ∈ X := by
    intro g hg k
    show rep ρ k g = ((1 : K →* ℂˣ) k : ℂ) • g
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    exact hg k k.2
  have ofX : ∀ g ∈ X, ∀ k ∈ K, rep ρ k g = g := by
    intro g hg k hk
    have h1 := hg ⟨k, hk⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact h1
  have hfA : f ∈ forms ρ := ⟨fun v => hfa v, hfe⟩
  let ff : forms ρ := ⟨f, hfA⟩
  have hffX : ff ∈ X := by
    refine memX ff fun k hk => Subtype.ext (LinearMap.ext fun u => ?_)
    have h1 := hfK u ⟨k, hk⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at h1
    exact h1
  suffices hY : ff ∈ Y from hY
  by_contra hffY
  obtain ⟨m, hm, hmo⟩ := exists_orth_proj Bf hBd (X ⊓ Y) ff
  obtain ⟨y, hy⟩ : ∃ y, y = ff - m := ⟨_, rfl⟩
  have hyX : y ∈ X := hy ▸ sub_mem hffX (Submodule.mem_inf.1 hm).1
  have hy0 : y ≠ 0 := by
    intro h
    apply hffY
    rw [hy, sub_eq_zero] at h
    rw [h]
    exact (Submodule.mem_inf.1 hm).2
  obtain ⟨U, hU0, hUO, hUst, hUirr⟩ := exists_irred_le_orbSpan (rep ρ) Bf hBh hBp hBd hBi (GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact E n)
    (rep_smooth ρ) (rep_fd ρ) y hy0
  have hadm := GlobalTheory.AdmissibleProjection.hadm_of (rep ρ) (GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact E n) (rep_smooth ρ) (rep_fd ρ)
  let Z : Subrepresentation (rep ρ) := ⟨U, fun g _ hv => hUst g _ hv⟩
  obtain ⟨P, hP1, hP2, hP3⟩ := GlobalTheory.AdmissibleProjection.exists_proj (rep ρ) Bf hBd hBi hadm Z
  obtain ⟨z, hz⟩ : ∃ z, z = P y := ⟨_, rfl⟩
  have hzU : z ∈ U := hz ▸ hP1 y
  have hzX : z ∈ X := memX z fun k hk => by rw [hz, ← hP3, ofX y hyX k hk]
  have hz0 : z ≠ 0 := by
    intro h0
    apply hU0
    have hyo : ∀ w ∈ Z.toSubmodule, Bf w y = 0 := by
      intro w hw
      have := hP2 y w hw
      rwa [← hz, h0, sub_zero] at this
    rw [Submodule.eq_bot_iff]
    intro w hw
    have hle : (orbSpan (rep ρ) y).toSubmodule ≤ LinearMap.ker (Bf w) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      exact orth_stable (rep ρ) Bf hBi Z y hyo g w hw
    exact hBd _ (hle (hUO hw))

  let M : Submodule ℂ (W →ₗ[ℂ] (UA E n → ℂ)) := U.map (forms ρ).subtype
  have hM0 : M ≠ ⊥ := by
    intro h
    apply hU0
    rw [Submodule.eq_bot_iff]
    intro u hu
    have : u.1 ∈ M := ⟨u, hu, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  have hMf : ∀ g ∈ M, (∀ v, IsAutFormU (g v)) ∧ ∀ (x : infU E n) v, g (ρ x v) = RU E n x (g v) := by
    rintro _ ⟨u, -, rfl⟩
    exact ⟨fun v => u.2.1 v, u.2.2⟩
  have hMk : ∀ k ∈ finU E n, ∀ g ∈ M, (RU E n k) ∘ₗ g ∈ M := by
    rintro k hk _ ⟨u, hu, rfl⟩
    exact ⟨rep ρ ⟨k, hk⟩ u, hUst _ u hu, rfl⟩
  have hMirr : ∀ N ≤ M, (∀ k ∈ finU E n, ∀ g ∈ N, (RU E n k) ∘ₗ g ∈ N) → N = ⊥ ∨ N = M := by
    intro N hNM hN
    let N' : Submodule ℂ (forms ρ) := N.comap (forms ρ).subtype
    have hN'U : N' ≤ U := by
      intro u hu
      obtain ⟨w, hw, hwu⟩ := hNM hu
      rw [← Subtype.ext hwu]
      exact hw
    have hN'st : ∀ g, ∀ u ∈ N', rep ρ g u ∈ N' := fun g u hu => hN g.1 g.2 u.1 hu
    have hNe : N'.map (forms ρ).subtype = N := by
      rw [Submodule.map_comap_subtype]
      exact inf_eq_right.2 (hNM.trans (Submodule.map_subtype_le _ _))
    rcases hUirr N' hN'U hN'st with h | h
    · left; rw [← hNe, h, Submodule.map_bot]
    · right; rw [← hNe, h]
  have hπ := GlobalTheory.FrameAut.VecForms.isAutRepU_span_values E n W ρ hsp M hM0 hMf hMk hMirr
  have hzY : z ∈ Y := by
    intro u
    have hmemπ : z.1 u ∈ Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ} :=
      Submodule.subset_span ⟨z.1, ⟨z, hzU, rfl⟩, u, rfl⟩
    have hfixu : z.1 u ∈ fixed (RF E n) K := by
      intro k
      rw [MonoidHom.one_apply, Units.val_one, one_smul]
      have h1 := congrArg (fun g : forms ρ => g.1 u) (ofX z hzX k k.2)
      exact h1
    have hidx : IsAutRepU (Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) ∧
        ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) ∧
          ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u) :=
      ⟨hπ, z.1, fun h => hz0 (Subtype.ext h), fun v => Submodule.subset_span ⟨z.1, ⟨z, hzU, rfl⟩, v, rfl⟩, z.2.2⟩
    exact (le_iSup₂ (f := fun (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧
      ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)) =>
      π ⊓ fixed (RF E n) K) _ hidx) ⟨hmemπ, hfixu⟩
  have hzm : Bf z y = 0 := hy ▸ hmo z ⟨hzX, hzY⟩
  have hzz : Bf z z = 0 := by
    have h2 := hP2 y z hzU
    rw [← hz, map_sub, hzm, zero_sub, neg_eq_zero] at h2
    exact h2
  exact hz0 (hBd z hzz)

end GlobalTheory.FrameAut.VecSemis

namespace GlobalTheory.FrameAut.VecSemis

open GlobalTheory.DefU

theorem mem_iSup_fixed_autRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (infU E n) W), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ (K : Subgroup (finU E n)), IsOpen (K : Set (finU E n)) → ∀ f : W →ₗ[ℂ] (UA E n → ℂ), (∀ u, IsAutFormU (f u)) → (∀ (x : infU E n) u, f (ρ x u) = RU E n x (f u)) → (∀ u, f u ∈ fixed (RF E n) K) → ∀ u, f u ∈ ⨆ (π : Submodule ℂ (UA E n → ℂ)) (_ : IsAutRepU π ∧ ∃ f' : W →ₗ[ℂ] (UA E n → ℂ), f' ≠ 0 ∧ (∀ u, f' u ∈ π) ∧ ∀ (x : infU E n) u, f' (ρ x u) = RU E n x (f' u)), π ⊓ fixed (RF E n) K := by
  intro E _ _ _ n W _ _ _ ρ hsp K hK f hfa hfe hfK
  obtain ⟨B, hh, hp, hd, hi⟩ := GlobalTheory.T.exists_invariant_positive_petersson_form E n
  exact mem_iSup_of_form E n B hh hp hd hi W ρ hsp K hK f hfa hfe hfK

end GlobalTheory.FrameAut.VecSemis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointsOverComponentOpenSet
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

namespace GlobalTheory.FramesUnion

theorem framesOn_of_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ), IsUnf (U σ) → ∀ (Z : Comp Xo c) (k : (U σ).Comp) (y y' : Frame ((U σ).X k).Ψ r), y' ∈ ((U σ).X k).dom → (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z → (⟨k, y'⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z := by
  intro E _ _ _ H Dw l Xo c r U σ hU Z k y y' hy' hyZ
  obtain ⟨hy, hZ⟩ := hyZ
  have hd : Dom (E := E) 0 0 := ⟨fun _ _ _ _ => le_rfl, Even.zero⟩
  have hsec := hU.2.2.2.2.1 0 0 hd (GlobalTheory.FlatLine.idem Z) (GlobalTheory.CompRestr.idem_mem_sec Z) k
  obtain ⟨w, hw⟩ := GlobalTheory.CompRat.const_of_idem_on
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r ((U σ).X k)).isPreconnected hsec.1.continuousOn fun x _ => by
      rw [← GlobalTheory.CompRat.rdU_mul_apply', GlobalTheory.FlatLine.idem_mul_idem]
  have hA : AllTest Xo c := (GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c).1.test
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  have e1 : ∀ (g : Rul Xo c) (x : Frame ((U σ).X k).Ψ r) (h : x ∈ ((U σ).X k).dom),
      rdU (U σ) g k x = toC (evR Xo c g ((U σ).un k ⟨x, h⟩)) := fun g x h => dif_pos h
  have h1 : rdU (U σ) (GlobalTheory.FlatLine.idem Z) k y = 1 := by
    rw [e1 _ _ hy, GlobalTheory.FlatLine.evR_idem hZ (hA _ _)]
    rfl
  have h1' : rdU (U σ) (GlobalTheory.FlatLine.idem Z) k y' = 1 := (hw y' hy').trans ((hw y hy).symm.trans h1)
  refine ⟨hy', ?_⟩
  by_contra hn
  have hoff : LiesOff Z ((U σ).un k ⟨y', hy'⟩) := by
    intro s hs
    apply hn
    intro s'
    have : s = s' := Subsingleton.elim (α := PrimeSpectrum ℂ) s s'
    exact this ▸ hs
  have h0 := GlobalTheory.FlatLine.idem_mem_suppOn Z (CAt σ) _ hoff
  rw [e1 _ _ hy', h0] at h1'
  exact zero_ne_one (α := ℂ) h1'

end GlobalTheory.FramesUnion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupLiftTangentPhiLinear
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj MonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstDeform

theorem act_const : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A'] (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (q : A'.left ⟶ A.left), IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i → IsGrpPullback A Xo.univ.t.G y.x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π → i ≫ q = 𝟙 _ → IsGrpPullback A' A (spMap (algebraMap K (DualNumber K))) q → ∀ (o : Obj Dw l (baseKA l) (x' ≫ Xo.s)) (m : ObjMap o Xo.univ x') (g : o.t.G.left ⟶ A'.left), g ≫ π' = m.cm.F → g ≫ A'.hom = o.t.G.hom → ∀ hF : IsGrpPullback o.t.G Xo.univ.t.G (constPt x') (g ≫ q ≫ π), ∀ a, (o.t.act.act a).left ≫ (g ≫ q ≫ π) = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by
  intro hP hGD E _ _ _ H Dw l Xo c K _ _ y x' hpq hT A _ A' _ π π' i q hi hπ hπ' hiπ hiq hq o m g hg hgw hF a
  haveI := Xo.univ.t.act.hom a
  have wβ : (π ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A.hom ≫ y.x := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ.1.w]
  let β : A ⟶ A := Over.homMk (hπ.1.lift _ A.hom wβ) (hπ.1.lift_snd _ _ _)
  have hβ : β.left ≫ π = π ≫ (Xo.univ.t.act.act a).left := hπ.1.lift_fst _ _ _
  haveI : IsMonHom β := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ hπ (Xo.univ.t.act.act a) β hβ
  have wα : (π' ≫ (Xo.univ.t.act.act a).left) ≫ Xo.univ.t.G.hom = A'.hom ≫ x' := by
    rw [Category.assoc, Over.w (Xo.univ.t.act.act a), hπ'.1.w]
  let α : A' ⟶ A' := Over.homMk (hπ'.1.lift _ A'.hom wα) (hπ'.1.lift_snd _ _ _)
  have hα : α.left ≫ π' = π' ≫ (Xo.univ.t.act.act a).left := hπ'.1.lift_fst _ _ _
  haveI : IsMonHom α := GlobalTheory.UU.isMonHom_of_over_isMonHom hπ' hπ' (Xo.univ.t.act.act a) α hα
  have wδ : (q ≫ β.left) ≫ A.hom = A'.hom ≫ spMap (algebraMap K (DualNumber K)) := by
    rw [Category.assoc, Over.w β, hq.1.w]
  let δ : A' ⟶ A' := Over.homMk (hq.1.lift _ A'.hom wδ) (hq.1.lift_snd _ _ _)
  have hδ : δ.left ≫ q = q ≫ β.left := hq.1.lift_fst _ _ _
  haveI : IsMonHom δ := GlobalTheory.UU.isMonHom_of_over_isMonHom hq hq β δ hδ
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  have LH := (hGD.at_dualNumber K).2.2
  have e1 : i ≫ α.left = β.left ≫ i := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, reassoc_of% hiπ, hiπ, hβ]
    · simp only [Category.assoc]
      rw [Over.w α, hi.1.w, reassoc_of% (Over.w β)]
  have e2 : i ≫ δ.left = β.left ≫ i := by
    apply hq.1.hom_ext
    · simp only [Category.assoc]
      rw [hδ, reassoc_of% hiq, hiq, Category.comp_id]
    · simp only [Category.assoc]
      rw [Over.w δ, hi.1.w, reassoc_of% (Over.w β)]
  have hαδ : α = δ := GlobalTheory.Published.GrothendieckMessing.LiftHom.unique LH hi hA' gA' hi hA' gA' β e1 e2
  have hga : (o.t.act.act a).left ≫ g = g ≫ α.left := by
    apply hπ'.1.hom_ext
    · simp only [Category.assoc]
      rw [hα, hg, reassoc_of% hg]
      exact m.act a
    · simp only [Category.assoc]
      rw [hgw, Over.w α, hgw, Over.w (o.t.act.act a)]
  calc (o.t.act.act a).left ≫ (g ≫ q ≫ π) = g ≫ α.left ≫ q ≫ π := by rw [reassoc_of% hga]
    _ = g ≫ q ≫ π ≫ (Xo.univ.t.act.act a).left := by rw [hαδ, reassoc_of% hδ, hβ]
    _ = (g ≫ q ≫ π) ≫ (Xo.univ.t.act.act a).left := by simp only [Category.assoc]

end GlobalTheory.ConstDeform
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLValueUpperBoundPermutedWeightsOfFE
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.SqTop GlobalTheory.FunObj GlobalTheory.FunObj.SqNum Formalism.BasicNotions GlobalTheory.ChiGrid Formalism.IndefR.Links

namespace GlobalTheory.SqTop

theorem lBound_of : GlobalTheory.Published.HeckeFunctionalEquationAbs → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.CompletedLBoundedInStrips → FieldDat → LBound := by
  intro hFE hS hFD
  set c : ℝ := max 0 (Real.log ‖riemannZeta (3 / 2)‖) with hc
  obtain ⟨CF1, hB⟩ := GlobalTheory.T.gridSizes_log_bound c
  obtain ⟨CF2, hF⟩ := hFD
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, hB⟩ := hB ε CF (le_of_max_le_left hCF)
  obtain ⟨C2, x2, hF⟩ := hF ε CF (le_of_max_le_right hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ hL G => ?_⟩
  have hb := hB C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hL G
  obtain ⟨hCM, hAb, hFd, hBase, -⟩ := hF C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hL G
  intro i j s hs1 hs2 π χ Λ hχ hΛ
  set κ := kap D (⟨1, CF, large₂.sc.b⟩ : Consts).cGap i j s with hκ
  set n : ℕ := Module.finrank ℚ D.host.E with hn
  have key : c * (n : ℝ) + Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) +
      ∑ τ, Real.log (1 + ((κ τ : ℝ) + s)) ≤ bTH D C large₂.sc.x large₂.sc.b := hb i j s hs1 hs2
  have hc0 : 0 ≤ c := le_max_left _ _
  have hcz : Real.log ‖riemannZeta (3 / 2)‖ ≤ c := le_max_right _ _
  have hd0 : 0 ≤ Real.log |((discr D.host.E : ℤ) : ℝ)| := Real.log_nonneg (by
    have := Int.one_le_abs (NumberField.discr_ne_zero D.host.E); exact_mod_cast this)
  have hq0 : 0 ≤ Real.log (levQ G.pl : ℝ) := Real.log_natCast_nonneg _
  have hk0 : 0 ≤ ∑ τ, Real.log (1 + ((κ τ : ℝ) + s)) :=
    Finset.sum_nonneg fun τ _ => Real.log_nonneg (by have : (0:ℝ) ≤ κ τ := Nat.cast_nonneg _; have : (0:ℝ) ≤ s := Nat.cast_nonneg _; linarith)
  have hn0 : (0 : ℝ) ≤ c * n := mul_nonneg hc0 (Nat.cast_nonneg _)
  by_cases h0 : Λ s = 0
  · rw [h0, norm_zero, Real.log_zero]
    linarith
  have hpos : 0 < ‖Λ s‖ := norm_pos_iff.2 h0
  have hz : 0 < ‖riemannZeta (3 / 2)‖ := norm_pos_iff.2 (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  rcases (by omega : s = 1 ∨ 2 ≤ s) with rfl | h2
  · obtain ⟨a, ha, haN⟩ := GlobalTheory.T.exists_cmValueCharacter_conductorExponents D G 1 _ χ hχ
    have hA := GlobalTheory.T.norm_completedHeckeL_CM_one_le_phragmenLindelof D.host.E D.what₂.Tau (cmPhi D) hFE hS hFd.2.2.2.2.2.2.1 χ (fun τ => ((κ (π τ) : ℕ) : ℤ) + ((1 : ℕ) : ℤ)) a Λ
      hχ.1 hχ.2.1 hχ.2.2.1 (fun τ => by positivity) ha hΛ
    simp only [Nat.cast_one] at hpos h0 ⊢
    set N : ℕ := (discr D.host.E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k with hN
    set P : ℝ := ∏ τ, (1 + ((((κ (π τ) : ℕ) : ℤ) + ((1 : ℕ) : ℤ) : ℤ) : ℝ)) with hP
    have hP0 : 0 < P := Finset.prod_pos fun τ _ => by push_cast; positivity
    have hN0 : (0 : ℝ) < N := by
      by_contra hc'
      have : (N : ℝ) = 0 := le_antisymm (not_lt.1 hc') (Nat.cast_nonneg _)
      rw [this, mul_zero, zero_mul] at hA
      linarith
    have hNle : (N : ℝ) ≤ |((discr D.host.E : ℤ) : ℝ)| * (levQ G.pl : ℝ) ^ 2 := by
      rw [hN, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact_mod_cast haN
    have hQ0 : (0 : ℝ) < levQ G.pl := by
      by_contra hc'
      have : (levQ G.pl : ℝ) = 0 := le_antisymm (not_lt.1 hc') (Nat.cast_nonneg _)
      rw [this, zero_pow two_ne_zero, mul_zero] at hNle; linarith
    have hD0 : (0 : ℝ) < |((discr D.host.E : ℤ) : ℝ)| := by
      have := Int.one_le_abs (NumberField.discr_ne_zero D.host.E)
      have : (1 : ℝ) ≤ |((discr D.host.E : ℤ) : ℝ)| := by exact_mod_cast this
      linarith
    have h1 : Real.log ‖Λ 1‖ ≤ Real.log (‖riemannZeta (3 / 2)‖ ^ n) + Real.log N + Real.log P := by
      rw [← Real.log_mul (by positivity) hN0.ne', ← Real.log_mul (by positivity) hP0.ne']
      exact Real.log_le_log hpos hA
    have h2 : Real.log N ≤ Real.log |((discr D.host.E : ℤ) : ℝ)| + 2 * Real.log (levQ G.pl) := by
      calc Real.log N ≤ Real.log (|((discr D.host.E : ℤ) : ℝ)| * (levQ G.pl : ℝ) ^ 2) := Real.log_le_log hN0 hNle
        _ = _ := by rw [Real.log_mul hD0.ne' (by positivity), Real.log_pow]; push_cast; ring
    have h3 : Real.log P = ∑ τ, Real.log (1 + ((κ τ : ℝ) + ((1 : ℕ) : ℝ))) := by
      rw [hP, Real.log_prod (fun τ _ => by push_cast; positivity)]
      rw [← Equiv.sum_comp π (fun τ => Real.log (1 + ((κ τ : ℝ) + ((1 : ℕ) : ℝ))))]
      refine Finset.sum_congr rfl fun τ _ => ?_
      push_cast; ring_nf
    have h4 : Real.log (‖riemannZeta (3 / 2)‖ ^ n) ≤ c * n := by
      rw [Real.log_pow]; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith
  · have h := GlobalTheory.T.norm_heckeLFunction_le_zeta_three_halves_pow D.host.E χ Λ s hχ.1 hΛ (by
      simp only [Complex.natCast_re]; have : (2 : ℝ) ≤ s := by exact_mod_cast h2
      linarith)
    have h4 : Real.log ‖Λ s‖ ≤ c * n := by
      calc Real.log ‖Λ s‖ ≤ Real.log (‖riemannZeta (3 / 2)‖ ^ n) := Real.log_le_log hpos h
        _ = n * Real.log ‖riemannZeta (3 / 2)‖ := Real.log_pow _ _
        _ ≤ c * n := by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    linarith

end GlobalTheory.SqTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntOffOfUnramPts
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FlatTw

theorem intOff_of_unramPts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (B : Finset ℕ), UnramPts Xo c B → ∀ (Z : Comp Xo c) (la : Weight Dw) (δ : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : ConstSec U x Z la δ), IntOff B (δ + s.rho_vw) := by
  intro E _ _ _ H Dw l Xo c r U x B hB Z la δ s w hw
  obtain ⟨v, hv, hint⟩ := hB Z w hw
  have he := s.val_eq hv
  rcases hint s.sig with h | ⟨n, hn⟩
  · rw [he] at h; exact absurd h (EReal.coe_ne_top _)
  · rw [he] at hn
    exact ⟨n, EReal.coe_eq_coe_iff.1 hn⟩

end GlobalTheory.FlatTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberCurveOfClassEqSmulAdd
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory

theorem interNumRed_of_cls_eq_nsmul_add : ∀ (k : Type) [Field k] (X : Scheme.{0}) (q : X ⟶ Sp k), IsProjOver q → letI := algebraΓOfHom q; ∀ (L M M' : LB X) (hL : L.IsLB) (hM : M.IsLB) (hM' : M'.IsLB) (a b : ℕ) (C : Closeds X), IsCompleteCurve k C → cls L hL = a • cls M hM + b • cls M' hM' → interNumRed k C ![L] = a * interNumRed k C ![M] + b * interNumRed k C ![M'] := by
  intro k _ X q hq
  letI := algebraΓOfHom q
  intro L M M' hL hM hM' a b C hC e
  obtain ⟨H, hH⟩ := exists_isAmpleLB_of_isProjOver hq
  rw [hC.interNumRed_of_cls_eq_add hH hL (isLB_lbPow hM a) (isLB_lbPow hM' b)
    (by rw [cls_lbPow hM, cls_lbPow hM', e]),
    hC.interNumRed_lbPow hH hM, hC.interNumRed_lbPow hH hM']

end GlobalTheory
end

