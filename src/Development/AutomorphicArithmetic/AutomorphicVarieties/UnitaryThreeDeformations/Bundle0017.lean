import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0016
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0050
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0027

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrCyc
section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)

private theorem schur {G κ : Type} [Group G] [Field κ] [IsAlgClosed κ] {m : ℕ} [NeZero m] (U : Subgroup G)
    (a : G → Matrix (Fin m) (Fin m) κ) (h : MatIrr U a) (M : Matrix (Fin m) (Fin m) κ)
    (hM : ∀ g ∈ U, M * a g = a g * M) : ∃ x : κ, M = x • 1 := by
  obtain ⟨x, hx⟩ := Module.End.exists_eigenvalue (Matrix.toLin' M)
  have htop : Module.End.eigenspace (Matrix.toLin' M) x = ⊤ := by
    refine (h _ fun g hg v hv => ?_).resolve_left hx
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hM g hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  refine ⟨x, Matrix.toLin'.injective (LinearMap.ext fun v => ?_)⟩
  have : v ∈ Module.End.eigenspace (Matrix.toLin' M) x := by rw [htop]; trivial
  rw [Module.End.mem_eigenspace_iff.1 this]
  simp

private theorem abs_irr {G κ B : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [Field κ] [IsAlgClosed κ] [CharZero κ] [TopologicalSpace κ] [IsTopologicalRing κ] [T2Space κ] [CommGroup B]
    (η : G →* ℤˣ) (hη : IsOpen (η.ker : Set G)) (r : G →* GG 3 κ) (hm : HasMult η r) (hc : Continuous (mats r))
    (χ : G →* B) (ho : ∀ U : Subgroup G, IsOpen (U : Set G) → U ≤ η.ker → MatIrr U (mats r)) :
    MatIrr (η.ker ⊓ χ.ker) (mats r) := by
  by_contra hred
  let ρ := glPart η r hm
  have hρ : ∀ g : η.ker, (ρ g : Matrix (Fin 3) (Fin 3) κ) = mats r g := fun _ => rfl
  obtain ⟨φ, hφ1, -, hφ3, M, hM⟩ := exists_selfTwist ρ (χ.comp η.ker.subtype).ker
    (fun a b => by simp [MonoidHom.mem_ker, mul_right_comm])
    (fun W hW => ho _ hη le_rfl W fun g hg => hW ⟨g, hg⟩ trivial)
    (fun h => hred fun W hW => h W fun g hg => hW g ⟨g.2, hg⟩)
  have hiff : ∀ g, φ g = 1 ↔ (M : Matrix (Fin 3) (Fin 3) κ) * mats r g = mats r g * M := by
    intro g
    have h1 := hM g trivial
    simp only [hρ] at h1
    refine ⟨fun h => by simpa [h] using h1, fun h => ?_⟩
    rw [← h, Matrix.mul_smul] at h1
    have hu : IsUnit ((M : Matrix (Fin 3) (Fin 3) κ) * mats r g) := (M * ρ g).isUnit
    exact Units.ext (smul_left_injective κ hu.ne_zero (h1.trans (one_smul _ _).symm))
  have hcl : IsClosed (φ.ker : Set η.ker) := by
    have : (φ.ker : Set η.ker) = {g : η.ker | (M : Matrix (Fin 3) (Fin 3) κ) * mats r g = mats r g * M} :=
      Set.ext hiff
    rw [this]
    have hc' := hc.comp (continuous_subtype_val (p := fun g => g ∈ η.ker))
    exact isClosed_eq (continuous_const.mul hc') (hc'.mul continuous_const)
  haveI : φ.ker.FiniteIndex := by
    haveI : Finite φ.range := Finite.of_injective
      (fun x => (⟨x.1, by
        obtain ⟨_, g, rfl⟩ := x
        exact DFunLike.congr_fun hφ3 g⟩ : rootsOfUnity 3 κ))
      (fun x y h => Subtype.ext (Subtype.mk.inj h))
    exact Subgroup.finiteIndex_ker φ
  have hop : IsOpen (φ.ker.map η.ker.subtype : Set G) :=
    hη.isOpenMap_subtype_val _ (Subgroup.isOpen_of_isClosed_of_finiteIndex (G := η.ker) φ.ker hcl)
  obtain ⟨x, hx⟩ := schur _ _ (ho _ hop (Subgroup.map_subtype_le _)) M (by
    rintro _ ⟨g, hg, rfl⟩
    exact (hiff g).1 hg)
  exact hφ1 (MonoidHom.ext fun g => (hiff g).2 (by simp [hx]))

theorem UpperTheory.V.UnitaryThreeInertia.matIrr_cyc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (c : Coef l) {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (o₁ : ℕ), HostData l e ψ o₁ →
    ∀ (S : Finset Pl) (A : S → ValuationSubring Ω) (F : Frame c.O (Formalism.ConjugateSelfDual.G ℚ Ω) (Gam Ω S) S), IsHostFrame Ω c e ψ S A F →
    ∀ (g₁ : Gam Ω S), F.Marked g₁ → ∀ r : Gam Ω S →* GG 3 (PadicAlgCl l), F.IsCharZeroPt g₁ r → TypeI F.η r → MatIrr ((eta4 Ω).ker ⊓ (cycZ ℚ Ω l).ker) fun s => (r (toGS Ω _ s)).mat := by
  intro Ω _ _ _ l _ c N _ e ψ o₁ h S A F hF g₁ hg r hr hI
  have hok := hostFrame_ok Ω c e ψ o₁ h S A F hF
  haveI hcl := isClosed_NS Ω (S : Set Pl)
  haveI : TotallyDisconnectedSpace (Gam Ω S) := totDisc_quot _ hcl
  obtain ⟨hm, -, hc, -⟩ := isCharZeroPt_basic F hok g₁ hg r hr
  have hη : ∀ s, F.η (toGS Ω _ s) = eta4 Ω s := fun s => by rw [← hF.η, hF.π]; rfl
  refine abs_irr (eta4 Ω) ?_ (r.comp (toGS Ω _)) (fun s => (hm _).trans (hη s)) (hc.comp (continuous_toGS Ω _))
    (cycZ ℚ Ω l) (matIrr_open Ω c e ψ o₁ h S A F hF g₁ hg r hr hI)
  rw [← hF.η]
  exact (hok.η_cont.comp_continuous hok.π_cont).isOpen_fiber 1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigEig
section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem norm_le_one_of_int (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.NormLeOneOfIsIntegral.norm_le_one_of_isIntegral l x hx

private theorem dvr_norm {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (f : A →+* PadicAlgCl l) (hle : ∀ x, ‖f x‖ ≤ 1) :
    (∀ u : A, IsUnit u → ‖f u‖ = 1) ∧
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ (n : ℕ) (x : A), x ∈ maximalIdeal A ^ n → ‖f x‖ ≤ q ^ n := by
  have hu : ∀ u : Aˣ, ‖f u‖ = 1 := by
    intro u
    have h1 : ‖f u‖ * ‖f ((u⁻¹ : Aˣ) : A)‖ = 1 := by
      rw [← norm_mul, ← map_mul, Units.mul_inv]; simp
    have h2 := hle u
    have h3 := hle (u⁻¹ : Aˣ)
    have h4 := norm_nonneg (f u)
    nlinarith
  refine ⟨fun u ⟨v, hv⟩ => hv ▸ hu v, ?_⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hl0 : (l : A) ≠ 0 := by
    intro h
    have h' : f l = 0 := by rw [h, map_zero]
    have : (l : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  have hl : ‖f l‖ < 1 := by
    have : f l = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [this, norm_algebraMap']
    exact Padic.norm_p_lt_one
  refine ⟨‖f ϖ‖, norm_nonneg _, ?_, fun n x hx => ?_⟩
  · obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
    rw [h, map_mul, norm_mul, hu, one_mul, map_pow, norm_pow] at hl
    by_contra hc
    exact absurd hl (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))
  · rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx
    obtain ⟨y, rfl⟩ := hx
    rw [map_mul, norm_mul, map_pow, norm_pow]
    exact mul_le_of_le_one_left (by positivity) (hle y)

private theorem conjBy_conjBy {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (h k : GL (Fin 3) R) :
    conjBy h (conjBy k r) = conjBy (h * k) r := by
  refine MonoidHom.ext fun g => ?_
  simp [conjBy, mul_assoc]

private theorem conjBy_mat {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (h : GL (Fin 3) R) (g : G)
    (hg : (r g).right = 1) : (conjBy h⁻¹ r g).mat =
      ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * (h : Matrix (Fin 3) (Fin 3) R) := by
  simp [conjBy, GG.mat, hg]

private theorem unit_diff {O : Type} [CommRing O] (x : Oˣ) (hx : IsUnit ((x : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((x ^ wt1 a : Oˣ) : O) - ((x ^ wt1 b : Oˣ) : O)) := by
  have h1 : IsUnit ((x : O) - 1) := by
    have e : (x : O) ^ 2 - 1 = ((x : O) - 1) * ((x : O) + 1) := by ring
    rw [e] at hx
    exact isUnit_of_mul_isUnit_left hx
  have hxy : ((x⁻¹ : Oˣ) : O) * (x : O) = 1 := Units.inv_mul x
  have h2 : IsUnit ((x : O) - ((x⁻¹ : Oˣ) : O)) := by
    have e : (x : O) - ((x⁻¹ : Oˣ) : O) = ((x⁻¹ : Oˣ) : O) * ((x : O) ^ 2 - 1) := by
      linear_combination (-(x : O)) * hxy
    rw [e]
    exact (Units.isUnit _).mul hx
  have h3 : IsUnit ((1 : O) - ((x⁻¹ : Oˣ) : O)) := by
    have e : (1 : O) - ((x⁻¹ : Oˣ) : O) = ((x⁻¹ : Oˣ) : O) * ((x : O) - 1) := by
      linear_combination (-1 : O) * hxy
    rw [e]
    exact (Units.isUnit _).mul h1
  have h1' := h1.neg
  have h2' := h2.neg
  have h3' := h3.neg
  rw [neg_sub] at h1' h2' h3'
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | simpa [wt1]

theorem UpperTheory.V.UnitaryThreeInertia.rig_eig :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {G' Γ ι : Type} [Group G'] [TopologicalSpace G'] [Group Γ] [TopologicalSpace Γ] (F : Frame c.O G' Γ ι) (g₁ : Γ) (r : Γ →* GG 3 (PadicAlgCl l)), F.IsCharZeroPt g₁ r → ∀ g : Γ, F.η g = 1 → IsUnit ((F.Ψ g : c.O) ^ 2 - 1) → ∀ P : GL (Fin 3) (PadicAlgCl l), (∀ i j, j < i → (conjBy P⁻¹ r g).mat i j = 0) → ∀ i j, i ≠ j → ∀ u : PadicAlgCl l, ‖u - 1‖ < 1 → (conjBy P⁻¹ r g).mat i i ≠ (conjBy P⁻¹ r g).mat j j * u := by
  intro l _ c G' Γ ι _ _ _ _ F g₁ r hr g hη hΨ P
  obtain ⟨A, hA, hfin, t, r', hpt, hp⟩ := hr
  have hle : ∀ x : A, ‖A.val x‖ ≤ 1 := fun x =>
    norm_le_one_of_int l _ (isIntegral_trans (A := c.O) _ ((Algebra.IsIntegral.isIntegral (R := c.O) x).map A.val))
  obtain ⟨hu, q, hq0, hq1, hq⟩ := dvr_norm (A.val : A →+* PadicAlgCl l) hle
  simp only [RingHom.coe_coe] at hu hq
  have hO : ∀ x : c.O, IsUnit x → ‖algebraMap c.O (PadicAlgCl l) x‖ = 1 := fun x hx => by
    rw [← hu _ (hx.map (algebraMap c.O A)), AlgHom.commutes]
  have e : conjBy P⁻¹ r = conjBy (tor _ t * P)⁻¹ (push A.val r') := by
    rw [hp, conjBy_conjBy, _root_.mul_inv_rev, inv_mul_cancel_right]
  have hright : (push A.val r' g).right = 1 := (hpt.mult g).trans hη
  rw [e, conjBy_mat _ _ _ hright]
  refine rig_sep _ (fun a => algebraMap c.O (PadicAlgCl l) ((F.Ψ g ^ wt1 a : (c.O)ˣ) : c.O)) _ ?_ ?_ ?_
  · intro a b
    have h := hq 1 _ (by rw [pow_one]; exact hpt.red g a b)
    rw [pow_one, Matrix.sub_apply, map_sub, Matrix.map_apply, AlgHom.commutes] at h
    refine lt_of_le_of_lt (le_of_eq_of_le ?_ h) hq1
    congr 2
    show _ = algebraMap c.O (PadicAlgCl l) (Matrix.diagonal (fun i => ((F.Ψ g ^ wt1 i : (c.O)ˣ) : c.O)) a b)
    rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
    split_ifs
    · rfl
    · rw [map_zero]
  · intro a
    exact hO _ (Units.isUnit _)
  · intro a b hab
    rw [← map_sub]
    exact hO _ (unit_diff _ hΨ a b hab)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RigLoc
section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

private theorem rigloc_adFun {m : ℕ} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : GG m R)
    (X : Matrix (Fin m) (Fin m) R) : (x.adFun X).map f = (GG.map f x).adFun (X.map f) := by
  have h1 : (((GG.map f x).left⁻¹ : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) =
      ((x.left⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R).map f := rfl
  unfold GG.adFun
  rw [h1, GG.map_mat, GG.map_right, Matrix.map_mul, Matrix.map_mul]
  congr 2
  split_ifs
  · rfl
  · unfold thetaLie
    rw [Matrix.map_neg _ (map_neg f), Matrix.map_mul, Matrix.map_mul, Jmat_map, Matrix.transpose_map]

private theorem rigloc_conj {m : ℕ} {G R S : Type} [Group G] [CommRing R] [CommRing S] (f : R →+* S)
    (h : GL (Fin m) R) (r : G →* GG m R) (g : G) :
    GG.map f (conjBy h r g) = conjBy (Matrix.GeneralLinearGroup.map f h) ((GG.map f).comp r) g := by
  have h1 : GG.map f (GG.ofGL h) = GG.ofGL (Matrix.GeneralLinearGroup.map f h) := rfl
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, h1]

private theorem rigloc_mul {m : ℕ} {R : Type} [CommRing R] (y a : Matrix (Fin m) (Fin m) R) (i j : Fin m) :
    (((1 + y.map (TrivSqZeroExt.inr : R → DualNumber R)) * a.map (algebraMap R (DualNumber R))) i j).fst = a i j ∧
    (((1 + y.map (TrivSqZeroExt.inr : R → DualNumber R)) * a.map (algebraMap R (DualNumber R))) i j).snd =
      (y * a) i j := by
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]
  simp [TrivSqZeroExt.fst_sum, TrivSqZeroExt.snd_sum, TrivSqZeroExt.algebraMap_eq_inl]

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.UnitaryThreeInertia.rig_loc :
    UpperTheory.V.Loc.LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (φ : Γ →* Formalism.BasicNotions.Loc.GQ l), Topology.IsOpenEmbedding φ → ∀ (η : Γ →* ℤˣ), IsLocallyConstant η → ∀ (r : Γ →* GG 3 (PadicAlgCl l)) (y : Γ → Matrix (Fin 3) (Fin 3) (PadicAlgCl l)) (r' : Γ →* GG 3 (DualNumber (PadicAlgCl l))) (h : GL (Fin 3) (DualNumber (PadicAlgCl l))), HasMult η r → Continuous (mats r) → Continuous y → IsCoc r y → IsDeform ((GG.map (algebraMap (PadicAlgCl l) (DualNumber (PadicAlgCl l)))).comp r) (fun g => (y g).map (TrivSqZeroExt.inr : (PadicAlgCl l) → DualNumber (PadicAlgCl l))) r' → ∀ (H : Subgroup Γ) [H.Normal], IsOpen (H : Set Γ) → H ≤ η.ker → Upper η (conjBy h⁻¹ r') → ∀ w : Fin 3 → ℤ, StrictAnti w → (∀ g ∈ H, φ g ∈ UpperTheory.V.Loc.Iq l → ∀ a, (conjBy h⁻¹ r' g).mat a a = ((UpperTheory.V.Loc.cycA l l (DualNumber (PadicAlgCl l)) (φ g) ^ w a : (DualNumber (PadicAlgCl l))ˣ) : DualNumber (PadicAlgCl l))) → (∀ i j : Fin 3, i < j → ∃ g ∈ H, ((conjBy h⁻¹ r' g).mat i i).fst ≠ ((conjBy h⁻¹ r' g).mat j j).fst * ((UpperTheory.V.Loc.cycA l l (PadicAlgCl l) (φ g) : (PadicAlgCl l)ˣ) : (PadicAlgCl l))) → y ∈ UpperTheory.V.Loc.finiteCocycles φ (adRep r) := by
  intro P l _ Γ _ _ _ φ hφ η hη r y r' h hm hr hy hcoc hdef H _ hH hHη hU w hw hκ hne
  have hc : IsClosed (φ.range : Set (Formalism.BasicNotions.Loc.GQ l)) := φ.range.isClosed_of_isOpen hφ.isOpen_range
  haveI : CompactSpace Γ := (Topology.IsClosedEmbedding.mk hφ.isEmbedding hc).compactSpace
  haveI : T2Space Γ := hφ.isEmbedding.t2Space
  have hfst : ∀ g a b, ((r' g).mat a b).fst = (r g).mat a b := fun g a b => by
    rw [(hdef g).2]; exact (rigloc_mul (y g) (r g).mat a b).1
  have hsnd : ∀ g a b, ((r' g).mat a b).snd = (y g * (r g).mat) a b := fun g a b => by
    rw [(hdef g).2]; exact (rigloc_mul (y g) (r g).mat a b).2
  obtain ⟨L, f, s', h₁, hf, hs', hh⟩ := rig_desc r' h
    (fun a b => by simp only [hfst]; exact hr.matrix_elem a b)
    (fun a b => by simp only [hsnd]; exact (hy.matrix_mul hr).matrix_elem a b)
  haveI := L.2
  haveI : IsModuleTopology ℚ_[l] ↥L.1 := isModuleTopologyOfFiniteDimensional
  let ι : ↥L.1 →+* PadicAlgCl l := L.1.val.toRingHom
  have hι : Function.Injective ι := Subtype.val_injective
  have hιm : Function.Injective fun X : Matrix (Fin 3) (Fin 3) ↥L.1 => X.map ι := Matrix.map_injective hι
  have hfi : Function.Injective f := fun a b hab => by
    ext
    · rw [← (hf a).1, ← (hf b).1, hab]
    · rw [← (hf a).2, ← (hf b).2, hab]
  have hcont : ∀ z : Γ → Matrix (Fin 3) (Fin 3) ↥L.1, Continuous (fun g => (z g).map ι) → Continuous z :=
    fun z hz => continuous_matrix fun a b => Topology.IsInducing.subtypeVal.continuous_iff.2 (hz.matrix_elem a b)
  have he : ∀ g, GG.map f (s' g) = r' g := fun g => by rw [← hs']; rfl
  have hem : ∀ g a b, f ((s' g).mat a b) = (r' g).mat a b := fun g a b => by rw [← he]; rfl
  let s : Γ →* GG 3 ↥L.1 := (GG.map (TrivSqZeroExt.fstHom ↥L.1 ↥L.1 ↥L.1).toRingHom).comp s'
  have hsr : ∀ g, (s g).right = (r g).right := fun g => by
    have := (hdef g).1
    rw [← he] at this
    exact this
  have hsm : ∀ g, (s g).mat.map ι = (r g).mat := fun g => by
    ext a b
    rw [← hfst, ← hem, (hf _).1]; rfl
  have hs : ∀ g, GG.map ι (s g) = r g := fun g =>
    SemidirectProduct.ext (Units.ext (hsm g)) (hsr g)
  let z : Γ → Matrix (Fin 3) (Fin 3) ↥L.1 := fun g =>
    (s' g).mat.map TrivSqZeroExt.snd * (((s g).left⁻¹ : GL (Fin 3) ↥L.1) : Matrix (Fin 3) (Fin 3) ↥L.1)
  have hzs : ∀ g, z g * (s g).mat = (s' g).mat.map TrivSqZeroExt.snd := fun g => by
    simp only [z, GG.mat, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  have hz : ∀ g, (z g).map ι = y g := fun g => by
    have h1 : (z g).map ι * (r g).mat = y g * (r g).mat := by
      rw [← hsm g, ← Matrix.map_mul, hzs, hsm]
      ext a b
      rw [← hsnd, ← hem, (hf _).2]; rfl
    exact (Units.mul_left_inj (r g).left).1 h1
  have had : ∀ g X, (adRep s g X).map ι = adRep r g (X.map ι) := fun g X => by
    have := rigloc_adFun ι (s g) X
    rw [hs] at this
    exact this
  have hcj : ∀ g a b, f ((conjBy h₁⁻¹ s' g).mat a b) = (conjBy h⁻¹ r' g).mat a b := fun g a b => by
    have := rigloc_conj f h₁⁻¹ s' g
    rw [map_inv, hh, hs'] at this
    rw [← this]; rfl
  have hcy : ∀ σ, Units.map f.toMonoidHom
      (UpperTheory.V.Loc.cycA l l (DualNumber ↥L.1) σ) = UpperTheory.V.Loc.cycA l l (DualNumber (PadicAlgCl l)) σ := fun σ => by
    apply Units.ext
    apply TrivSqZeroExt.ext
    · exact (hf _).1
    · exact (hf _).2
  have key : z ∈ UpperTheory.V.Loc.finiteCocycles φ (adRep s) := by
    refine rig_fin P φ hφ η hη s z s' h₁ (fun g => (hsr g).trans (hm g)) ?_ ?_ ?_ ?_ H hH hHη ?_ w hw ?_ ?_
    · exact hcont _ (by simp only [mats, hsm]; exact hr)
    · exact hcont _ (by simp only [hz]; exact hy)
    · intro g k
      apply hιm
      simp only []
      rw [Matrix.map_add _ (map_add ι), had, hz, hz, hz, hcoc g k]
    · intro g
      refine ⟨rfl, ?_⟩
      ext a b : 1
      apply TrivSqZeroExt.ext
      · exact (rigloc_mul (z g) (s g).mat a b).1.symm
      · refine Eq.trans ?_ (rigloc_mul (z g) (s g).mat a b).2.symm
        rw [hzs]; rfl
    · intro g hg a b hab
      apply hfi
      rw [hcj, hU g hg a b hab, map_zero]
    · intro g hg hI a
      apply hfi
      rw [hcj, hκ g hg hI a, ← hcy, ← map_zpow, Units.coe_map]; rfl
    · intro i j hij
      obtain ⟨g, hg, hne⟩ := hne i j hij
      refine ⟨g, hg, fun e => hne ?_⟩
      rw [← hcj, ← hcj, (hf _).1, (hf _).1]
      have e2 := congrArg ι e
      rw [map_mul] at e2
      have e3 : ι ((UpperTheory.V.Loc.cycA l l ↥L.1 (φ g) : (↥L.1)ˣ) : ↥L.1) =
          ((UpperTheory.V.Loc.cycA l l (PadicAlgCl l) (φ g) : (PadicAlgCl l)ˣ) : PadicAlgCl l) := rfl
      rw [e3] at e2
      exact e2
  have := UpperTheory.V.Loc.z1fCoef φ (adRep s) (adRep r) (L.1.val.toLinearMap.mapMatrix)
    (continuous_matrix fun a b => continuous_subtype_val.comp (continuous_id.matrix_elem a b)) had z key
  have e : y = fun g => (z g).map ι := funext fun g => (hz g).symm
  rw [e]
  exact this
end

