import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFive
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHtHalfSub
section
noncomputable section

open NumberField Matrix
open scoped NumberField.AdeleRing
open PositivityTheory.RgEis PositivityTheory.RgEis.So GroundTheory.Global

namespace GlobalTheory.CompanionTheory.EisJMir

section Gen

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

theorem isHt_pull (j : G →* G') (hj : Continuous j) {Γ K P : Subgroup G} {Γ' K' P' : Subgroup G'} {η : G' → ℝ}
    (h : IsHt Γ' K' P' η) (hΓ : ∀ γ ∈ Γ, j γ ∈ Γ') (hK : ∀ k ∈ K, j k ∈ K') (hP : ∀ p ∈ P, j p ∈ P') :
    IsHt Γ K P (fun x => η (j x)) := by
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hγP => ?_, h.cont.comp hj⟩
  · rw [map_mul]
    exact h.left (j p) (hP p hp) (j g)
  · rw [map_mul]
    exact h.right (j g) (j k) (hK k hk)
  · exact h.rat (j γ) (hΓ γ hγ) (hP γ hγP)

theorem isHt_of_top {Γ K P : Subgroup G} {η : G → ℝ} (h : IsHt Γ K ⊤ η) : IsHt Γ K P η := by
  exact ⟨fun p _ g => h.left p (Subgroup.mem_top p) g, h.right, fun γ hγ _ => h.rat γ hγ (Subgroup.mem_top γ),
    h.cont⟩

theorem isHt_half_add {Γ K P : Subgroup G} {a b : G → ℝ} (ha : IsHt Γ K P a) (hb : IsHt Γ K P b) :
    IsHt Γ K P (fun x => (a x + b x) / 2) := by
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hγP => ?_, (ha.cont.add hb.cont).div_const 2⟩
  · rw [ha.left p hp g, hb.left p hp g]
    ring
  · rw [ha.right g k hk, hb.right g k hk]
  · rw [ha.rat γ hγ hγP, hb.rat γ hγ hγP]
    norm_num

theorem isHt_half_sub {Γ K P : Subgroup G} {a b : G → ℝ} (ha : IsHt Γ K P a) (hb : IsHt Γ K P b) :
    IsHt Γ K P (fun x => (a x - b x) / 2) := by
  refine ⟨fun p hp g => ?_, fun g k hk => ?_, fun γ hγ hγP => ?_, (ha.cont.sub hb.cont).div_const 2⟩
  · rw [ha.left p hp g, hb.left p hp g]
    ring
  · rw [ha.right g k hk, hb.right g k hk]
  · rw [ha.rat γ hγ hγP, hb.rat γ hγ hγP]
    norm_num

theorem isCh_pull (j : G →* G') (hj : Continuous j) {Γ P : Subgroup G} {Γ' P' : Subgroup G'} {u : G' → ℂ} {c : G → ℂ}
    (hu : IsCh Γ' P' u) (hc : IsCh Γ ⊤ c) (hΓ : ∀ γ ∈ Γ, j γ ∈ Γ') (hP : ∀ p ∈ P, j p ∈ P') :
    IsCh Γ P (fun x => u (j x) * (c x)⁻¹) := by
  have hc0 : ∀ x, c x ≠ 0 := fun x h0 => by
    have h1 := hc.norm x (Subgroup.mem_top x)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  refine ⟨fun p hp q hq => ?_, fun p hp => ?_, fun γ hγ hγP => ?_, ?_⟩
  · rw [map_mul, hu.mul (j p) (hP p hp) (j q) (hP q hq), hc.mul p (Subgroup.mem_top p) q (Subgroup.mem_top q),
      mul_inv]
    ring
  · rw [norm_mul, norm_inv, hu.norm (j p) (hP p hp), hc.norm p (Subgroup.mem_top p)]
    norm_num
  · rw [hu.rat (j γ) (hΓ γ hγ) (hP γ hγP), hc.rat γ hγ (Subgroup.mem_top γ)]
    norm_num
  · refine (hu.cont.comp hj.continuousOn (fun x hx => hP x hx)).mul ?_
    exact (hc.cont.mono (fun x _ => Subgroup.mem_top x)).inv₀ (fun x _ => hc0 x)

end Gen

theorem jmir : StdGood → GrpTop → BdetLaw → ExtLaw → ParLaw → JTop → JCpt → JPar → JIwa → JRat → JCh → JMir := by
  intro hStd hGT hBd hExt hPar hJT hJC hJP hJI hJR hJCh F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hA hB
    hi hJ hIwa
  obtain ⟨hjc, -, -, -⟩ := hJT F E R A ε ν r δ α ω ι i j hA hB hi hJ
  have hcK := hJC F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hst, hQeq, hbd⟩ := hJP F E R A ε ν r δ α ω ι i j hA hB hi hJ
  have hIw := hJI F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hmapΓ, htr⟩ := hJR F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hc0, hld⟩ := hJCh F E R A ε ν r δ α ω ι i j hA hB hi hJ
  obtain ⟨hparU, hhtU, -⟩ := (hPar E R A hA ι ε Set.univ).2 (by rw [inf_idem]; exact hIwa)
  rw [inf_idem] at hparU
  have hGL := hA.toGoodL
  have hSG := (hStd F).lgmul
  have hlg1 : A.lg 1 = 0 := by
    have h := hGL.lgmul 1 1
    rw [mul_one] at h
    linarith
  have hP : ∀ p ∈ Subgroup.comap (prj A ν ι) (stab 𝔸[𝓞 F, F] {(Sum.inl i : ι ⊕ ι)}),
      j p ∈ A.uQ ε Set.univ := by
    intro p hp
    rw [← hQeq] at hp
    exact hp
  have hK : ∀ k ∈ cK α j, j k ∈ A.uK ε ι := fun k hk => (Subgroup.mem_inf.1 hk).1
  have hΓ : ∀ γ ∈ cΓ A ν ι, j γ ∈ A.uΓ ε ι := by
    intro γ hγ
    rw [← hmapΓ]
    exact Subgroup.mem_map_of_mem j hγ
  have hωsq : ∀ y : IdeleGroup F, ω.toIdele y * ω.toIdele y = 1 := by
    intro y
    rw [hB.ωχ, mul_eq_one_iff_eq_inv]
    have h1 := hA.χσ (Units.map (ν : 𝔸[𝓞 F, F] →* R) y)
    convert h1 using 2
    all_goals (ext; simp [hB.fix])
  have hcov : ∀ x : cover A ν ι, A.lg (x : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 =
      -(adStd F).lg (Matrix.GeneralLinearGroup.det (prj A ν ι x)) ∧
      A.χ (Units.map (ν : 𝔸[𝓞 F, F] →* R) (Matrix.GeneralLinearGroup.det (prj A ν ι x))) = 1 := by
    intro x
    have hx := MonoidHom.mem_ker.1 x.2
    simp only [MonoidHom.mul_apply, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst,
      MonoidHom.coe_snd] at hx
    constructor
    · have h := congrArg A.lg hx
      rw [hGL.lgmul, hGL.lgmul, hB.lgσ, hB.lg, hlg1] at h
      show A.lg (x : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 = -(adStd F).lg (Matrix.GeneralLinearGroup.det (x : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).2)
      linarith
    · have h := congrArg A.χ hx
      rw [map_mul, map_mul, hA.χσ, map_one, mul_inv_cancel, one_mul] at h
      exact h
  have hext : ∀ x ∈ Subgroup.comap (prj A ν ι) (stab 𝔸[𝓞 F, F] {(Sum.inl i : ι ⊕ ι)}),
      A.uH ε Set.univ (j x) = A.lg (bdet (Sum.inl '' (Set.univ : Set ι)) ((j x : A.U ε ι) : GL (ι ⊕ ι) R)) := by
    intro x hx
    obtain ⟨-, -, -, hT2U, -, -, hKc⟩ := hGT E R A hA ι ε
    haveI := hT2U
    obtain ⟨-, hmulS, hcontS, hratS, hkS, -⟩ := hBd E R A hGL (ι ⊕ ι) (Sum.inl '' (Set.univ : Set ι))
    have h := (hExt (A.U ε ι) (A.uΓ ε ι) (A.uK ε ι) (A.uQ ε Set.univ)
      (fun p => A.lg (bdet (Sum.inl '' (Set.univ : Set ι)) (p : GL (ι ⊕ ι) R))) hKc hparU.closed hIwa
      (fun p hp q hq => by
        show A.lg (bdet _ ((p * q : A.U ε ι) : GL (ι ⊕ ι) R)) = _
        rw [Subgroup.coe_mul, hmulS _ (Subgroup.mem_subgroupOf.1 hp) _ (Subgroup.mem_subgroupOf.1 hq), hGL.lgmul])
      (hGL.lgcont.comp_continuousOn (hcontS.comp continuous_subtype_val.continuousOn
        (fun p hp => Subgroup.mem_subgroupOf.1 hp)))
      (fun p hp hk => hkS _ (Subgroup.mem_subgroupOf.1 hp) (Subgroup.mem_subgroupOf.1 hk))
      (fun p hp hg => by
        obtain ⟨e, he⟩ := hratS _ (Subgroup.mem_subgroupOf.1 hp) (Subgroup.mem_subgroupOf.1 hg)
        show A.lg _ = 0
        rw [he]
        exact hGL.lgi e)).2 (j x) (hP x hx) 1 (Subgroup.one_mem _)
    rw [mul_one] at h
    exact h
  refine ⟨?_, ?_, ?_, hcK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hld, ?_, ?_, fun g => rfl⟩
  · have h1 : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
    rw [Fintype.card_sum]
    omega
  · refine ContinuousMonoidHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact hωsq y
  · exact continuous_snd.comp continuous_subtype_val
  · intro κ hκ
    obtain ⟨κ', hκ', hEq⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hκ).2)
    refine ⟨κ', hκ', ?_⟩
    have hd : (fun k : ι ⊕ ι => ((Sum.elim (fun _ => (1 : IdeleGroup F)) (fun _ => α) k : IdeleGroup F) : 𝔸[𝓞 F, F])) =
        (Sum.elim (fun _ => 1) (fun _ => (α : 𝔸[𝓞 F, F])) : ι ⊕ ι → 𝔸[𝓞 F, F]) := by
      funext k
      rcases k with k | k <;> rfl
    rw [hd]
    change ((prj A ν ι κ : GL (ι ⊕ ι) 𝔸[𝓞 F, F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F]) * ((dg ι α : GL (ι ⊕ ι) 𝔸[𝓞 F, F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F]) =
      ((dg ι α : GL (ι ⊕ ι) 𝔸[𝓞 F, F]) : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F]) * (κ' : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[𝓞 F, F])
    rw [← hEq]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
  · intro γ hγ
    exact (Subgroup.mem_prod.1 (Subgroup.mem_subgroupOf.1 hγ)).2
  · intro s hs g hg
    obtain ⟨γ, hγ, h⟩ := htr g hg
    refine ⟨γ, hγ, ?_⟩
    rcases hs with rfl | rfl
    · exact h
    · rw [hst]
      exact h
  · refine ⟨?_, hIw, isCh_pull j hjc hparU.ch hc0 hΓ hP⟩
    rw [← hQeq, Subgroup.coe_comap]
    exact hparU.closed.preimage hjc
  · rw [hst]
    refine ⟨?_, hIw, isCh_pull j hjc hparU.ch hc0 hΓ hP⟩
    rw [← hQeq, Subgroup.coe_comap]
    exact hparU.closed.preimage hjc
  · exact isHt_half_add (isHt_pull j hjc hhtU hΓ hK hP) (isHt_of_top hld)
  · rw [hst]
    exact isHt_half_sub (isHt_pull j hjc hhtU hΓ hK hP) (isHt_of_top hld)
  · intro p hp
    obtain ⟨hb1, -⟩ := hbd p hp
    obtain ⟨hl, -⟩ := hcov p
    refine ⟨?_, ?_⟩
    · show (A.χ (bdet (Sum.inl '' Set.univ) ((j p : A.U ε ι) : GL (ι ⊕ ι) R)) : ℂ) *
          ((A.χ (p : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 : ℂ))⁻¹ = _
      rw [hb1, map_mul, Circle.coe_mul, hB.ωχ, mul_comm, ← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _),
        one_mul]
    · show (A.uH ε Set.univ (j p) + ld p) / 2 = _
      rw [hext p hp, hb1, hGL.lgmul, hB.lg, hl]
      simp only [So.ld]
      ring
  · intro p hp
    rw [hst] at hp
    obtain ⟨hb1, hb2⟩ := hbd p hp
    obtain ⟨hl, hχ⟩ := hcov p
    have hωb : ω.toIdele (bdet {Sum.inl i} (prj A ν ι p)) = ω.toIdele (bdet {Sum.inr i} (prj A ν ι p)) := by
      have h3 : ω.toIdele (bdet {Sum.inl i} (prj A ν ι p)) * ω.toIdele (bdet {Sum.inr i} (prj A ν ι p)) = 1 := by
        rw [hB.ωχ, hB.ωχ, ← map_mul, ← map_mul, ← hb2]
        exact hχ
      exact mul_right_cancel (h3.trans (hωsq _).symm)
    refine ⟨?_, ?_⟩
    · show (A.χ (bdet (Sum.inl '' Set.univ) ((j p : A.U ε ι) : GL (ι ⊕ ι) R)) : ℂ) *
          ((A.χ (p : Rˣ × GL (ι ⊕ ι) 𝔸[𝓞 F, F]).1 : ℂ))⁻¹ = _
      rw [hb1, map_mul, Circle.coe_mul, ← hωb, hB.ωχ, mul_comm, ← mul_assoc,
        inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]
    · show (A.uH ε Set.univ (j p) - ld p) / 2 = _
      rw [hext p hp, hb1, hGL.lgmul, hB.lg, hl]
      simp only [So.ld]
      rw [hb2, hSG]
      ring

end GlobalTheory.CompanionTheory.EisJMir
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Jcpt
section
open PositivityTheory.RgEis PositivityTheory.RgEis.So

namespace GlobalTheory.CompanionTheory.RgEisSo

theorem jcpt : StdGood → GrpTop → JTop → JCpt := by
  intro hS hG hT F E R _ _ _ _ _ _ _ _ _ _ A ε ν r δ α ω ι _ _ i j hGood hB hi hJ
  show IsCompact (cK α j : Set (cover A ν ι))
  have hj : Continuous j := (hT F E R A ε ν r δ α ω ι i j hGood hB hi hJ).1
  obtain ⟨-, -, -, hUT2, -, -, hUK⟩ := hG E R A hGood ι ε
  have hν : Continuous ν := hB.cont

  have hmapν : Continuous (Matrix.GeneralLinearGroup.map (n := ι ⊕ ι) ν) := by
    refine Continuous.units_map _ ?_
    exact Continuous.matrix_map continuous_id hν
  let D : GL (ι ⊕ ι) R := dg ι (Units.map A.i.toMonoidHom δ)
  let M : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → GL (ι ⊕ ι) R :=
    fun h => D⁻¹ * Matrix.GeneralLinearGroup.map ν h * D
  have hM : Continuous M := (continuous_const.mul hmapν).mul continuous_const
  let φ : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → R :=
    fun p => ((p.1.1 * (M p.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)
  let ψ : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) → R :=
    fun p => ((M p.2 * (p.1.1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i)
  have hval : Continuous (Subtype.val : A.U ε ι → GL (ι ⊕ ι) R) := continuous_subtype_val
  have hφ : Continuous φ := by
    have : Continuous fun p : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (p.1.1 * (M p.2)⁻¹ : GL (ι ⊕ ι) R) :=
      (hval.comp continuous_fst).mul (hM.comp continuous_snd).inv
    exact (Units.continuous_val.comp this).matrix_elem _ _
  have hψ : Continuous ψ := by
    have : Continuous fun p : A.U ε ι × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (M p.2 * (p.1.1)⁻¹ : GL (ι ⊕ ι) R) :=
      (hM.comp continuous_snd).mul (hval.comp continuous_fst).inv
    exact (Units.continuous_val.comp this).matrix_elem _ _

  have hrel : ∀ x : cover A ν ι, ((j x).1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (x.1.1 : R) • (M x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) :=
    fun x => hJ x
  have hφv : ∀ x : cover A ν ι, φ (j x, x.1.2) = (x.1.1 : R) := by
    intro x
    have e : (((j x).1 * (M x.1.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = (x.1.1 : R) • 1 := by
      rw [Units.val_mul, hrel x, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    show (((j x).1 * (M x.1.2)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i) = _
    rw [e]; simp
  have hψv : ∀ x : cover A ν ι, ψ (j x, x.1.2) = ((x.1.1⁻¹ : Rˣ) : R) := by
    intro x
    have e0 : (x.1.1 : R) • ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = 1 := by
      rw [Units.val_mul, ← Matrix.smul_mul, ← hrel x, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e : ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) = ((x.1.1⁻¹ : Rˣ) : R) • 1 := by
      rw [← e0, smul_smul, Units.inv_mul, one_smul]
    show ((M x.1.2 * ((j x).1)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl i) (Sum.inl i) = _
    rw [e]; simp

  let C₂ : Set (GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :=
    ((((adStd F).kGL (ι ⊕ ι)).map (MulAut.conj (dg ι α)).toMonoidHom : Subgroup _) : Set _)
  have hC₂ : IsCompact C₂ := by
    have h0 := ((hS F).kcpt (ι ⊕ ι)).image
      (f := fun k => (MulAut.conj (dg ι α)).toMonoidHom k)
      (by
        show Continuous fun k => dg ι α * k * (dg ι α)⁻¹
        exact (continuous_const.mul continuous_id).mul continuous_const)
    exact h0
  let C₁ : Set (A.U ε ι) := (A.uK ε ι : Set (A.U ε ι))
  have hC : IsCompact (C₁ ×ˢ C₂) := hUK.prod hC₂
  have hS₁ := hC.image hφ
  have hS₂ : IsCompact (MulOpposite.op '' (ψ '' (C₁ ×ˢ C₂))) := (hC.image hψ).image MulOpposite.continuous_op
  let B : Set Rˣ := Units.embedProduct R ⁻¹' ((φ '' (C₁ ×ˢ C₂)) ×ˢ (MulOpposite.op '' (ψ '' (C₁ ×ˢ C₂))))
  have hBc : IsCompact B := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS₁.prod hS₂)

  have hdet : Continuous (Matrix.GeneralLinearGroup.det (n := ι ⊕ ι) (R := NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · show Continuous fun g : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        (g : Matrix (ι ⊕ ι) (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)).det
      exact Continuous.matrix_det Units.continuous_val
    · show Continuous fun g : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        ((g⁻¹ : GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)) :
          Matrix (ι ⊕ ι) (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)).det
      exact Continuous.matrix_det (Units.continuous_val.comp continuous_inv)
  have hσ : Continuous A.σ := hGood.σcont
  have hUσ : Continuous (Units.map A.σ.toMonoidHom) := Continuous.units_map _ hσ
  have hUν : Continuous (Units.map ν.toMonoidHom) := Continuous.units_map _ hν
  have hcl : IsClosed ((cover A ν ι : Subgroup _) : Set (Rˣ × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) := by
    have hf : Continuous fun p : Rˣ × GL (ι ⊕ ι) (NumberField.AdeleRing (NumberField.RingOfIntegers F) F) =>
        p.1 * Units.map A.σ.toMonoidHom p.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det p.2) :=
      (continuous_fst.mul (hUσ.comp continuous_fst)).mul (hUν.comp (hdet.comp continuous_snd))
    exact isClosed_singleton.preimage hf
  have hemb := hcl.isClosedEmbedding_subtypeVal
  have hP : IsCompact ((Subtype.val : cover A ν ι → _) ⁻¹' (B ×ˢ C₂)) :=
    hemb.isCompact_preimage (hBc.prod hC₂)
  have hprj : Continuous (prj A ν ι) := continuous_snd.comp continuous_subtype_val
  have hclK : IsClosed (cK α j : Set (cover A ν ι)) :=
    (hUK.isClosed.preimage hj).inter (hC₂.isClosed.preimage hprj)
  refine hP.of_isClosed_subset hclK ?_
  intro x hx
  have h1 : j x ∈ C₁ := hx.1
  have h2 : x.1.2 ∈ C₂ := hx.2
  refine ⟨?_, h2⟩
  refine ⟨⟨(j x, x.1.2), ⟨h1, h2⟩, hφv x⟩, ⟨ψ (j x, x.1.2), ⟨(j x, x.1.2), ⟨h1, h2⟩, rfl⟩, ?_⟩⟩
  rw [hψv x]
  rfl

end GlobalTheory.CompanionTheory.RgEisSo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Jtop
section
open PositivityTheory.RgEis PositivityTheory.RgEis.So
open NumberField Matrix
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.EisSo

theorem jtop : JTop := by
  intro F E R _ _ _ _ _ _ _ _ _ _ A ε ν _ δ _ _ ι _ _ _ j hA hB _ hJ
  have hcv : Continuous ν := hB.cont

  have hval : Continuous fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) := by
    have e : (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) = fun x =>
        (x.1.1 : R) • ((((dg ι (Units.map A.i.toMonoidHom δ))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) *
          ((x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]).map ν) *
          ((dg ι (Units.map A.i.toMonoidHom δ) : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) := by
      funext x; rw [hJ x]; rfl
    rw [e]
    have h1 : Continuous fun x : cover A ν ι => (x.1.1 : R) :=
      Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
    have h2 : Continuous fun x : cover A ν ι => (x.1.2 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) :=
      Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
    exact h1.smul ((continuous_const.matrix_mul (h2.matrix_map hcv)).matrix_mul continuous_const)
  have hjGL : Continuous fun x : cover A ν ι => ((j x).1 : GL (ι ⊕ ι) R) := by
    refine Units.continuous_iff.2 ⟨hval, ?_⟩
    have e : (fun x : cover A ν ι => (((((j x).1 : GL (ι ⊕ ι) R))⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) =
        (fun x : cover A ν ι => (((j x).1 : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R)) ∘ fun x => x⁻¹ := by
      funext x; simp [map_inv]
    rw [e]; exact hval.comp continuous_inv
  have hum : ∀ {S T : Type} [CommRing S] [CommRing T] [TopologicalSpace S] [TopologicalSpace T]
      [IsTopologicalRing S] (φ : S →+* T), Continuous φ → Continuous (Units.map φ.toMonoidHom) := by
    intro S T _ _ _ _ _ φ hφ
    exact Units.continuous_iff.2 ⟨hφ.comp Units.continuous_val, hφ.comp (Units.continuous_val.comp continuous_inv)⟩
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : GL (ι ⊕ ι) 𝔸[F] → 𝔸[F]ˣ) :=
    Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, (Units.continuous_val.comp continuous_inv).matrix_det⟩
  haveI : SecondCountableTopology Rᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F]) := inferInstanceAs (SecondCountableTopology (ι ⊕ ι → ι ⊕ ι → 𝔸[F]))
  haveI : SecondCountableTopology (Matrix (ι ⊕ ι) (ι ⊕ ι) 𝔸[F])ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology Rˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology (GL (ι ⊕ ι) 𝔸[F]) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : LocallyCompactSpace Rˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (ι ⊕ ι) 𝔸[F]) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have hf : Continuous fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
      x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2) :=
    (continuous_fst.mul ((hum A.σ hA.σcont).comp continuous_fst)).mul ((hum ν hcv).comp (hdet.comp continuous_snd))
  have hcl : IsClosed (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) := by
    have e : (cover A ν ι : Set (Rˣ × GL (ι ⊕ ι) 𝔸[F])) = (fun x : Rˣ × GL (ι ⊕ ι) 𝔸[F] =>
        x.1 * Units.map A.σ.toMonoidHom x.1 * Units.map ν.toMonoidHom (Matrix.GeneralLinearGroup.det x.2)) ⁻¹' {1} :=
      Set.ext fun x => Iff.rfl
    rw [e]; exact isClosed_singleton.preimage hf
  haveI : SecondCountableTopology (Rˣ × GL (ι ⊕ ι) 𝔸[F]) := inferInstance
  exact ⟨hjGL.subtype_mk _, inferInstance, hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    Topology.IsEmbedding.subtypeVal.secondCountableTopology⟩

end GlobalTheory.CompanionTheory.EisSo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionClosedCell
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem locSec_parab_mir_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (ht : 0 < t) :
    LocSec (parab k (two (stdSum h))) (Mir k (i + t)) 1 := by
  set e := GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum h) with he
  obtain ⟨b, hbc, hb1, hbw⟩ := GlobalTheory.CompanionTheory.BZRes.exists_rowSec (k := k) (Fin.last (i + t))
  obtain ⟨W, hW⟩ : ∃ W : GL (Fin (i + t + 1)) k → Fin (i + t + 1) → k,
      ∀ u, W u = (↑u⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) :=
    ⟨fun u : GL (Fin (i + t + 1)) k => (↑u⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)),
      fun _ => rfl⟩
  have hWc : Continuous W := by
    have hWeq : W = fun u : GL (Fin (i + t + 1)) k => (↑u⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) :=
      funext hW
    rw [hWeq]
    exact continuous_pi fun j =>
      (Units.continuous_coe_inv (M := Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k)).matrix_elem
        (Fin.last (i + t)) j
  have hone : (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) =
      GlobalTheory.BZMir.eLast k (i + t) := by
    funext j
    by_cases hj : j = Fin.last (i + t)
    · subst hj
      simp [GlobalTheory.BZMir.eLast]
    · simp [GlobalTheory.BZMir.eLast, Matrix.one_apply, Pi.single_apply, hj, Ne.symm hj]
  have hrow : ∀ q p : GL (Fin (i + t + 1)) k, p ∈ GlobalTheory.BZMir.Mir k (i + t) →
      (↑(q * p)⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) =
        (↑q⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) := by
    intro q p hp
    have hp' := (GlobalTheory.BZMir.mem_Mir_iff k p⁻¹).1 (Subgroup.inv_mem _ hp)
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mul_apply_eq_vecMul, hp']
    simp only [GlobalTheory.BZMir.eLast, Matrix.single_one_vecMul]
    rfl
  have hW1 : W 1 = Pi.single (Fin.last (i + t)) 1 := by
    rw [hW, inv_one, Units.val_one, hone]
    rfl
  have hbW : ContinuousAt (fun u => b (W u)) 1 := by
    refine ContinuousAt.comp (f := W) (g := b) ?_ hWc.continuousAt
    rw [hW1]
    exact hbc
  have hbW1 : b (W 1) = 1 := by rw [hW1, hb1]
  unfold GlobalTheory.CompanionTheory.BZRes.LocSec
  intro OQ hOQ OP hOP
  have h1 : (fun u => (b (W u))⁻¹) ⁻¹' OQ ∈ 𝓝 (1 : GL (Fin (i + t + 1)) k) :=
    hbW.inv.preimage_mem_nhds (by
      show OQ ∈ 𝓝 (b (W 1))⁻¹
      rw [hbW1, inv_one]
      exact hOQ)
  have h2 : (fun u => b (W u) * u) ⁻¹' OP ∈ 𝓝 (1 : GL (Fin (i + t + 1)) k) :=
    (hbW.mul continuousAt_id).preimage_mem_nhds (by
      show OP ∈ 𝓝 (b (W 1) * 1)
      rw [hbW1, mul_one]
      exact hOP)
  have h3 : (fun u => W u (Fin.last (i + t))) ⁻¹' {x | x ≠ 0} ∈ 𝓝 (1 : GL (Fin (i + t + 1)) k) :=
    ((continuous_apply _).comp hWc).continuousAt.preimage_mem_nhds
      (isOpen_ne.mem_nhds (by simp [hW1]))
  refine ⟨_, Filter.inter_mem h1 (Filter.inter_mem h2 h3), ?_⟩
  rintro u ⟨hu1, hu2, hu3⟩ hu
  unfold GlobalTheory.CompanionTheory.BZRes.dcos at hu
  obtain ⟨q, hq, p, hp, hqp⟩ := hu
  simp only [one_mul, mul_one] at hqp
  have hbw' := hbw (W u) hu3
  have hWu : W u = (↑q⁻¹ : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (Fin.last (i + t)) := by
    rw [hW, hqp]
    exact hrow q p hp
  have hbQ : b (W u) ∈ GlobalTheory.SmGL.parab k e := by
    rw [GlobalTheory.SmGL.mem_parab_iff]
    rintro (_ | _) (_ | _) r c hlt
    all_goals first | exact absurd hlt (by decide) | skip
    rw [hbw']
    by_cases hr : e ⟨true, r⟩ = Fin.last (i + t)
    · rw [hr, Matrix.updateRow_self, hWu, ← hr]
      exact (GlobalTheory.SmGL.mem_parab_iff.1 (Subgroup.inv_mem _ hq)) true false r c hlt
    · rw [Matrix.updateRow_ne hr, Matrix.one_apply_ne]
      intro hrc
      exact absurd (e.injective hrc) (by simp)
  have hpP : b (W u) * u ∈ GlobalTheory.BZMir.Mir k (i + t) := by
    rw [GlobalTheory.BZMir.mem_Mir_iff, Units.val_mul, Matrix.mul_apply_eq_vecMul, hbw', Matrix.updateRow_self, hW,
      ← Matrix.mul_apply_eq_vecMul, Units.inv_mul, hone]
  refine ⟨(b (W u))⁻¹, Subgroup.inv_mem _ hbQ, hu1, b (W u) * u, hpP, hu2, ?_⟩
  simp

end GlobalTheory.CompanionTheory.BZRes

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemHPGIffConjugateParabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem wGL_conj_apply (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (g : GL (Fin (i + t + 1)) k) (a b : Fin (i + t + 1)) :
    ((wGL k h * g * (wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) a b =
      (g : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) (wPerm h a) (wPerm h b) := by
  have e1 : ((wGL k h : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix (wPerm h) id := rfl
  have e2 : (((wGL k h)⁻¹ : GL (Fin (i + t + 1)) k) : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k) = (1 : Matrix (Fin (i + t + 1)) (Fin (i + t + 1)) k).submatrix id (wPerm h) := rfl
  rw [Units.val_mul, Units.val_mul, e1, e2]
  simp [Matrix.mul_apply, Matrix.one_apply]

theorem wPerm_two {i t : ℕ} (h : (i + 1) + t = i + t + 1) (x : Σ x, Two (Fin (i + 1)) (Fin t) x) :
    wPerm h (two (stdSum h) x) = ePG i t x := by
  simp [wPerm]

theorem mem_HPG_iff_conj_mem_parab (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {i t : ℕ} (h : (i + 1) + t = i + t + 1) (p : Mir k (i + t)) :
    p ∈ HPG k i t ↔ wGL k h * (p : GL (Fin (i + t + 1)) k) * (wGL k h)⁻¹ ∈ parab k (two (stdSum h)) := by
  show (p : GL (Fin (i + t + 1)) k) ∈ parab k (ePG i t) ↔ _
  rw [mem_parab_iff, mem_parab_iff]
  refine forall_congr' fun a => forall_congr' fun b => forall_congr' fun x => forall_congr' fun y => ?_
  rw [wGL_conj_apply, wPerm_two, wPerm_two]

end GlobalTheory.CompanionTheory.BZRes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFiveStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_five : PositivityTheory.SiegelWeilFormula.Gunr.Q5 := by
  first | exact @GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot | exact GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot | (intros; apply GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot <;> assumption)
end

