import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PointsFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0006

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsSpanEntMonApproxOfMemWtPart
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem one_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) : (1 : R) ∈ entMon r 0 :=
  ⟨[], rfl, rfl⟩

private theorem mul_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) {i j : ℤ} {a b : R}
    (ha : a ∈ entMon r i) (hb : b ∈ entMon r j) : a * b ∈ entMon r (i + j) := by
  obtain ⟨L, rfl, rfl⟩ := ha
  obtain ⟨M, rfl, rfl⟩ := hb
  exact ⟨L ++ M, by simp, by simp⟩

private theorem mat_mem_entMon {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (g : G) (a b : Fin 3) :
    (r g).mat a b ∈ entMon r (wt1 a - wt1 b) :=
  ⟨[(g, a, b)], by simp [wt], by simp⟩

private theorem theta_left {G R : Type} [Group G] [CommRing R] (r : G →* GG 3 R) (c : G)
    (h1 : (r c).right = -1) (h2 : (r c).mat = 1) (g : G) :
    (theta (r g).left : Matrix (Fin 3) (Fin 3) R) = (r (c * g)).mat := by
  have h : (r c).left = 1 := Units.ext h2
  rw [map_mul, GG.mat, SemidirectProduct.mul_left, h, h1, one_mul, sgnAct_neg_one]

private theorem emb_mem {O G R : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] (r : G →* GG 3 R) (c : G)
    (h1 : (r c).right = -1) (h2 : (r c).mat = 1) (g : G) (a b : Fin 3 ⊕ Fin 3) :
    emb (r g) a b ∈ Submodule.span O (entMon r (wt6 a - wt6 b)) := by
  rw [emb_apply, theta_left r c h1 h2]
  split_ifs <;> rcases a with a | a <;> rcases b with b | b <;>
    first
    | exact Submodule.zero_mem _
    | exact Submodule.subset_span (mat_mem_entMon r _ a b)

theorem UpperTheory.exists_span_entMon_approx_of_mem_wtPart :
    ∀ {O G R σ : Type} [CommRing O] [Group G] [CommRing R] [Algebra O R] [Finite σ] (η : G →* ℤˣ) (Ψ : G →* Oˣ) (r : G →* GG 3 R) (c : G),
          (r c).right = -1 → (r c).mat = 1 → ∀ (w : σ → ℤ) (Φ : MvPowerSeries σ O →ₐ[O] R) (m : Ideal R), (∀ s, Φ (MvPowerSeries.X s) ∈ m) →
          (∀ s, ∃ g a b, w s = wt6 a - wt6 b ∧ Φ (MvPowerSeries.X s) = emb (r g) a b - algebraMap O R (emb (r0 η Ψ g) a b)) →
          ∀ j, ∀ F ∈ wtPart O w j, ∀ n : ℕ, ∃ y ∈ Submodule.span O (entMon r j), Φ F - y ∈ m ^ n := by
  intro O G R σ _ _ _ _ _ η Ψ r c h1 h2 w Φ m hm hX j F hF n
  refine approx w Φ m (fun j => Submodule.span O (entMon r j))
    (Submodule.subset_span (one_mem_entMon r)) ?_ hm ?_ j F hF n
  · intro i j a ha b hb
    have h := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at h
    refine Submodule.span_mono ?_ h
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact mul_mem_entMon r hx hy
  · intro s
    obtain ⟨g, a, b, hw, he⟩ := hX s
    rw [hw, he]
    refine Submodule.sub_mem _ (emb_mem r c h1 h2 g a b) ?_
    by_cases h : wt6 a = wt6 b
    · rw [h, sub_self, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (one_mem_entMon r))
    · rw [unitaryEmbedding_residualRep_eq_zero_of_weight_ne η Ψ g a b h, map_zero]
      exact Submodule.zero_mem _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsSurjectionUnivNormCondKerSpanNEq
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

private theorem mat_symm {R : Type} [CommRing R] (x : GG 3 R) (h2 : x * x = 1) (hx : x.right = -1) :
    x.mat = Jmat R 3 * x.matᵀ * Jmat R 3 := by
  have h : x.left * theta x.left = 1 := by
    have := congrArg SemidirectProduct.left h2
    rwa [SemidirectProduct.mul_left, hx, sgnAct_neg_one] at this
  have h' : x.left = (theta x.left)⁻¹ := eq_inv_of_mul_eq_one_left h
  have := theta_inv_val x.left
  rw [← h'] at this
  exact this

private theorem norm_iff {G R : Type} [Group G] [CommRing R] (c g₁ : G) (r : G →* GG 3 R) (hc : c * c = 1)
    (hr : (r c).right = -1) : Normalised c g₁ r ↔ ∀ i, nEq c g₁ r i = 0 := by
  have hs := mat_symm (r c) (by rw [← map_mul, hc, map_one]) hr
  have hsym : ∀ i j, (r c).mat i j = (r c).mat j.rev i.rev := by
    intro i j
    conv_lhs => rw [hs]
    fin_cases j <;> simp [Matrix.mul_apply, Jmat, Fin.sum_univ_three]
  constructor
  · rintro ⟨h1, h2, h3⟩ i
    fin_cases i <;> simp [nEq, h1, h2, h3]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    have h6 := h 6
    have h7 := h 7
    simp [nEq, sub_eq_zero] at h0 h1 h2 h3 h4 h5 h6 h7
    have e12 : (r c).mat 1 2 = (r c).mat 0 1 := hsym 1 2
    have e21 : (r c).mat 2 1 = (r c).mat 1 0 := hsym 2 1
    have e22 : (r c).mat 2 2 = (r c).mat 0 0 := hsym 2 2
    refine ⟨?_, h6, h7⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, h3, h4, h5, e12, e21, e22]

private theorem nEq_map {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} (c g₁ : Γ) {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] (r : GLift O η Ψ R) (f : R →ₐ[O] R') (i : Fin 8) :
    nEq c g₁ (r.map f).hom i = f (nEq c g₁ r.hom i) := by
  have hm : ∀ g, ((r.map f).hom g).mat = (r.hom g).mat.map f := fun g => GG.map_mat (f : R →+* R') (r.hom g)
  fin_cases i <;> simp [nEq, zmat, hm, map_sub, map_one]

private theorem ext_lemma {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (a b : GLift O η Ψ R) (h : ∀ x, (a.hom x).mat = (b.hom x).mat) : a = b := by
  apply GLift.ext
  apply MonoidHom.ext
  intro x
  apply SemidirectProduct.ext
  · exact Units.ext (h x)
  · rw [a.hasMult x, b.hasMult x]

private theorem gLift_map_hom_mat_eq_map {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] (r : GLift O η Ψ R) (f : R →ₐ[O] R') (x : Γ) :
    ((r.map f).hom x).mat = (r.hom x).mat.map f :=
  GG.map_mat (f : R →+* R') (r.hom x)

private theorem comp_lemma_3 {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R R' R'' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R']
    [Algebra O R'] [IsCO O R'] [CommRing R''] [Algebra O R''] [IsCO O R''] (r : GLift O η Ψ R)
    (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') : r.map (g.comp f) = (r.map f).map g := by
  apply ext_lemma
  intro x
  rw [gLift_map_hom_mat_eq_map, gLift_map_hom_mat_eq_map, gLift_map_hom_mat_eq_map]
  ext i j
  simp

private theorem gLift_map_id {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (r : GLift O η Ψ R) : r.map (AlgHom.id O R) = r := by
  apply ext_lemma
  intro x
  rw [gLift_map_hom_mat_eq_map]
  ext i j
  simp

theorem UpperTheory.exists_surjection_univ_normCond_ker_span_nEq :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {P : GCond O η Ψ} (c g₁ : Γ)
          (B : Univ P) (S : Univ (NormCond c g₁ P)), c * c = 1 → η c = -1 →
          ∃ p : B.R →ₐ[O] S.R, Function.Surjective p ∧ B.r.map p = S.r ∧ RingHom.ker p = Ideal.span (Set.range (nEq c g₁ B.r.hom)) := by
  intro O _ _ Γ _ _ η Ψ P c g₁ B S hc hη
  have hr : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (r : GLift O η Ψ R),
      (r.hom c).right = -1 := fun R _ _ _ r => by rw [r.hasMult c, hη]
  have hNS : NormCond c g₁ P S.R S.r := by
    have h := (S.rep S.R).1 (AlgHom.id O S.R)
    rwa [gLift_map_id] at h
  obtain ⟨p, hp, -⟩ := (B.rep S.R).2 S.r hNS.2
  have hI : Ideal.span (Set.range (nEq c g₁ B.r.hom)) ≤ RingHom.ker p := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    show p (nEq c g₁ B.r.hom i) = 0
    rw [← nEq_map, hp]
    exact (norm_iff c g₁ S.r.hom hc (hr _ S.r)).1 hNS.1 i
  set I := Ideal.span (Set.range (nEq c g₁ B.r.hom)) with hIdef
  haveI : Nontrivial (B.R ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (RingHom.ker_ne_top _) hI)
  haveI : IsCO O (B.R ⧸ I) := co_quot O B.R (B.R ⧸ I) (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  have hNq : NormCond c g₁ P (B.R ⧸ I) (B.r.map (Ideal.Quotient.mkₐ O I)) := by
    refine ⟨(norm_iff c g₁ _ hc (hr _ _)).2 (fun i => ?_), (B.rep _).1 _⟩
    rw [nEq_map]
    show Ideal.Quotient.mk I _ = 0
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨i, rfl⟩)
  obtain ⟨s, hs, -⟩ := (S.rep (B.R ⧸ I)).2 _ hNq
  have hsp : s.comp p = Ideal.Quotient.mkₐ O I := by
    obtain ⟨u, -, hu⟩ := (B.rep (B.R ⧸ I)).2 _ hNq.2
    have e1 := hu (s.comp p) (by
      show GLift.map (s.comp p) B.r = _
      rw [comp_lemma_3, hp, hs])
    have e2 := hu (Ideal.Quotient.mkₐ O I) rfl
    rw [e1, e2]
  have hker : RingHom.ker p = I := by
    refine le_antisymm (fun x hx => ?_) hI
    have h0 : Ideal.Quotient.mkₐ O I x = 0 := by
      rw [← hsp, AlgHom.comp_apply, RingHom.mem_ker.1 hx, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 h0
  have hI' : ∀ a ∈ I, p a = 0 := fun a ha => RingHom.mem_ker.1 (hI ha)
  let p' := Ideal.Quotient.liftₐ I p hI'
  have hp'q : ∀ z, p' (Ideal.Quotient.mkₐ O I z) = p z := fun z => by
    show Ideal.Quotient.lift I (p : B.R →+* S.R) hI' (Ideal.Quotient.mk I z) = p z
    exact Ideal.Quotient.lift_mk I _ _
  have hpq : p'.comp (Ideal.Quotient.mkₐ O I) = p := AlgHom.ext hp'q
  have hid : p'.comp s = AlgHom.id O S.R := by
    obtain ⟨u, -, hu⟩ := (S.rep S.R).2 S.r hNS
    have e1 := hu (p'.comp s) (by
      show GLift.map (p'.comp s) S.r = S.r
      rw [comp_lemma_3, hs, ← comp_lemma_3, hpq, hp])
    have e2 := hu (AlgHom.id O S.R) (gLift_map_id _)
    rw [e1, e2]
  refine ⟨p, fun y => ?_, hp, hker⟩
  obtain ⟨z, hz⟩ := Ideal.Quotient.mkₐ_surjective O I (s y)
  refine ⟨z, ?_⟩
  rw [← hp'q, hz]
  exact congrArg (fun f => f y) hid
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsTorusTwistEqLocalPointOfWeightedPres
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.U3.Mop

open Polynomial in
private theorem pts_int {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have halg : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) x).isIntegral
  have hmon : (minpoly ℚ_[l] x).Monic := minpoly.monic halg
  have hn : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [hn, spectralValue_le_one_iff hmon]
  constructor
  · intro hx n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hx, Polynomial.coeff_map]
    exact PadicInt.norm_le_one ((minpoly ℤ_[l] x).coeff n)
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hmon
    refine ⟨q, hqm, ?_⟩
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l), ← Polynomial.eval₂_map, hq,
      ← Polynomial.aeval_def]
    exact minpoly.aeval ℚ_[l] x

private theorem pts_unit {B K : Type} [CommRing B] [Field K] [Algebra B K] (hi : Function.Injective (algebraMap B K))
    (b : B) (h0 : algebraMap B K b ≠ 0) (h : IsIntegral B (algebraMap B K b)⁻¹) : IsUnit b := by
  classical
  obtain ⟨p, hpm, hp⟩ := h
  set y := (algebraMap B K b)⁻¹ with hy
  have hy0 : y ≠ 0 := inv_ne_zero h0
  letI : Invertible y := invertibleOfNonzero hy0
  have hrev := Polynomial.eval₂_reverse_mul_pow (algebraMap B K) y p
  rw [hp, invOf_eq_inv, hy, inv_inv] at hrev
  have hq : Polynomial.eval₂ (algebraMap B K) (algebraMap B K b) p.reverse = 0 :=
    (mul_eq_zero.mp hrev).resolve_right (pow_ne_zero _ (inv_ne_zero h0))
  rw [Polynomial.eval₂_at_apply] at hq
  have hq' : Polynomial.eval b p.reverse = 0 := hi (by rw [hq, map_zero])
  obtain ⟨r, hr⟩ := Polynomial.X_dvd_sub_C (p := p.reverse)
  have he := congrArg (Polynomial.eval b) hr
  rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.coeff_zero_reverse, hpm.leadingCoeff, hq',
    Polynomial.eval_mul, Polynomial.eval_X] at he
  have h1 : b * -Polynomial.eval b r = 1 := by
    rw [mul_neg, ← he]
    ring
  exact ⟨⟨b, _, h1, (mul_comm _ _).trans h1⟩, rfl⟩

private theorem automorphic_points_exist {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R) (h : W.HasOrigin)
    (s : W.σ) : W.z s ∈ maximalIdeal R := mem_max_of_zero (W.origin h) (origin_presentation_var_eq_zero W h s)

private theorem pts_sur {O R K : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [Field K] [Algebra O K]
    (f : R →ₐ[O] K) (x : R) (h0 : f x ≠ 0) (h3 : IsIntegral O (f x)⁻¹) : IsUnit x := by
  classical
  have hu : IsUnit (⟨f x, AlgHom.mem_range_self f x⟩ : f.range) :=
    pts_unit (B := f.range) (K := K) (fun a b hab => Subtype.ext hab) _ h0 h3.tower_top
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨r, hr⟩ := (AlgHom.mem_range f).1 v.2
  have hfr : f x * f r = 1 := by
    rw [hr]
    exact congrArg Subtype.val hv
  by_contra hxu
  have hm : x * r ∈ maximalIdeal R := Ideal.mul_mem_right r _ hxu
  have hunit := (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (x * r) hm).map f
  rw [map_sub, map_one, map_mul, hfr, sub_self] at hunit
  exact not_isUnit_zero hunit

private theorem pts_loc {l : ℕ} [Fact l.Prime] {c : Coef l} {R : Type} [CommRing R] [Algebra c.O R] [IsLocalRing R]
    (f : R →ₐ[c.O] PadicAlgCl l) : IsLocPt f := by
  intro x hx
  by_contra hge
  push_neg at hge
  have h0 : f x ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hge
    linarith
  have hint : IsIntegral ℤ_[l] (f x)⁻¹ :=
    (pts_int _).mpr (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hge)
  exact hx (pts_sur f x h0 hint.tower_top)

private theorem fg_lemma {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {K : Type} [Field K]
    [Algebra O K] (P : Submodule O A) (I : Ideal A) (ξ : A →ₐ[O] K) (hξ : ∀ a ∈ I, ξ a = 0)
    (h : (Submodule.map (Ideal.Quotient.mkₐ O I).toLinearMap P).FG) :
    (Submodule.map ξ.toLinearMap P).FG := by
  have he : ξ.toLinearMap = (Ideal.Quotient.liftₐ I ξ hξ).toLinearMap ∘ₗ
      (Ideal.Quotient.mkₐ O I).toLinearMap := by
    ext a
    rfl
  rw [he, Submodule.map_comp]
  exact h.map _

set_option maxHeartbeats 1000000 in
theorem UpperTheory.exists_torus_twist_eq_localPoint_of_weightedPres :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {R S : Type} [CommRing R] [Algebra c.O R] [IsCO c.O R] [CommRing S] [Algebra c.O S] [IsCO c.O S]
          (W : WPres c.O ℤ R) (h : W.HasOrigin) (qh : R →ₐ[c.O] S), Function.Surjective qh → ∀ {κ : Type} (g : κ → W.A) (w : κ → ℤ), (∀ i, g i ∈ W.gr (w i)) →
          RingHom.ker qh = Ideal.span (Set.range fun i => (g i : R)) → M2 W.gr (Ideal.span (Set.range g)) →
          ∀ ξ : W.A →ₐ[c.O] PadicAlgCl l, OnS (Ideal.span (Set.range g)) ξ →
            ∃ (t : (PadicAlgCl l)ˣ) (f : S →ₐ[c.O] PadicAlgCl l), IsLocPt f ∧ act W.gr (tz t) ξ = f.comp (qh.comp W.A.val) := by
  intro l _ c R S _ _ _ _ _ _ W h qh hqh κ g w hg hk hM ξ hOn
  have hfg : (Submodule.map ξ.toLinearMap (W.gr 0)).FG := fg_lemma (W.gr 0) _ ξ hOn hM
  haveI : IsLocalRing c.O := IsDiscreteValuationRing.toIsLocalRing
  haveI : Module.Finite ℤ_[l] c.O := c.fin
  obtain ⟨hcomp, -, -, hinj, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI := hcomp
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) := Algebra.IsAlgebraic.mk fun x =>
    ((IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] (PadicAlgCl l)).mpr
      (Algebra.IsAlgebraic.isAlgebraic x)).extendScalars hinj
  obtain ⟨t, Ξ, hΞ, -⟩ := points_finite c.O ℤ R W (automorphic_points_exist W h) (PadicAlgCl l) ξ hfg
  have hker : ∀ a ∈ RingHom.ker qh, Ξ a = 0 := by
    intro a ha
    rw [hk] at ha
    have hle : Ideal.span (Set.range fun i => (g i : R)) ≤ RingHom.ker Ξ := by
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have h1 := congrArg (fun φ : W.A →ₐ[c.O] PadicAlgCl l => φ (g i)) hΞ
      simp only [AlgHom.comp_apply, Subalgebra.coe_val] at h1
      rw [h1, act_of_mem W.gr t ξ (hg i), hOn (g i) (Ideal.subset_span ⟨i, rfl⟩), mul_zero]
    exact RingHom.mem_ker.mp (hle ha)
  let f : S →ₐ[c.O] PadicAlgCl l := (Ideal.Quotient.liftₐ (RingHom.ker qh) Ξ hker).comp
    (Ideal.quotientKerAlgEquivOfSurjective hqh).symm.toAlgHom
  have hf : ∀ r, f (qh r) = Ξ r := by
    intro r
    have hmk : (Ideal.quotientKerAlgEquivOfSurjective hqh).symm (qh r) =
        Ideal.Quotient.mk (RingHom.ker qh) r := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    show Ideal.Quotient.liftₐ (RingHom.ker qh) Ξ hker
      ((Ideal.quotientKerAlgEquivOfSurjective hqh).symm (qh r)) = Ξ r
    rw [hmk]
    rfl
  refine ⟨(zpowersHom (PadicAlgCl l)ˣ).symm t, f, pts_loc f, ?_⟩
  rw [show tz ((zpowersHom (PadicAlgCl l)ˣ).symm t) = t from Equiv.apply_symm_apply _ _, ← hΞ]
  refine AlgHom.ext fun a => ?_
  simp only [AlgHom.comp_apply, hf]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.FinrankKerAdRepComplexConjSubOneEqBoxDef
section
open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg

namespace UpperTheory.V.U3.FixDim

variable {k : Type} [Field k]

private def sw (k : Type) [Field k] : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k := Matrix.fromBlocks 0 1 1 0

private def am (x y z : k) : Matrix (Fin 3) (Fin 3) k := !![x, y, 0; z, 0, -y; 0, -z, -x]

private def bm (x y z : k) : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k :=
  Matrix.fromBlocks (am x y z) 0 0 (am x y z)

private theorem emb_c {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* kˣ) (c : Γ) (h1 : η c = -1) (h2 : Ψ c = 1) :
    emb (r0 η Ψ c) = sw k := by
  rw [emb_apply, GG.mat, unitaryThreeReflection_left, theta_tor, unitaryThreeReflection_right, h1, h2, map_one, if_neg (by decide)]
  rfl

private theorem J3 : Jmat k 3 = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Jmat] <;> decide

private theorem sw_bm (x y z : k) : sw k * bm x y z * sw k = bm x y z := by
  simp [sw, bm, Matrix.fromBlocks_multiply]

private theorem bm_smul (t x y z : k) : t • bm x y z = bm (t * x) (t * y) (t * z) := by
  have : t • am x y z = am (t * x) (t * y) (t * z) := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [am]
  simp [bm, Matrix.fromBlocks_smul, this]

private theorem bm_mem (O : Type) [CommRing O] [Algebra O k] (j : ℤ) (x y z : k) (hx : j ≠ 0 → x = 0)
    (hy : j ≠ 1 → y = 0) (hz : j ≠ -1 → z = 0) : bm x y z ∈ (form6 O).gw k j := by
  have h0 : (am x y z)ᵀ * Jmat k 3 + Jmat k 3 * am x y z = 0 := by
    rw [J3]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [am, Matrix.mul_apply, Fin.sum_univ_three]
  have h1 : ∀ a b : Fin 3, wt1 a - wt1 b ≠ j → am x y z a b = 0 := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp [wt1] at h <;> simp [am] <;>
      first | exact hx (by omega) | exact hy (by omega) | exact hz (by omega)
  refine ⟨⟨?_, fun a b h => ?_⟩, fun a b h => ?_⟩
  · rw [blockPairingForm_JR]
    simp [bm, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add, h0]
  · rcases a with a | a <;> rcases b with b | b <;> first | rfl | exact absurd rfl h
  · rcases a with a | a <;> rcases b with b | b <;> first | rfl | exact h1 a b h

private theorem eq_bm (O : Type) [CommRing O] [Algebra O k] (h2 : (2 : k) ≠ 0) (j : ℤ)
    (Y : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) k) (hY : Y ∈ (form6 O).gw k j) (hs : sw k * Y * sw k = Y) :
    ∃ x y z : k, Y = bm x y z ∧ (j ≠ 0 → x = 0) ∧ (j ≠ 1 → y = 0) ∧ (j ≠ -1 → z = 0) := by
  obtain ⟨⟨y1, y2⟩, y3⟩ := hY
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, Y = Matrix.fromBlocks A B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks Y).symm⟩
  have hB : B = 0 := by
    ext a b
    exact y2 (.inl a) (.inr b) (by simp [form6])
  have hC : C = 0 := by
    ext a b
    exact y2 (.inr a) (.inl b) (by simp [form6])
  subst hB hC
  have hD : D = A := by
    simp [sw, Matrix.fromBlocks_multiply] at hs
    exact hs.1
  subst hD
  rw [blockPairingForm_JR] at y1
  have h0 : Dᵀ * Jmat k 3 + Jmat k 3 * D = 0 := by
    ext a b
    have := congrFun (congrFun y1 (.inl a)) (.inr b)
    simpa [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add] using this
  rw [J3] at h0
  have e := fun a b => congrFun (congrFun h0 a) b
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e11 := e 1 1
  have e12 := e 1 2
  have e22 := e 2 2
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three, ← two_mul, h2] at e00 e01 e02 e11 e12 e22
  refine ⟨D 0 0, D 0 1, D 1 0, ?_, fun h => y3 (.inl 0) (.inl 0) ?_, fun h => y3 (.inl 0) (.inl 1) ?_,
    fun h => y3 (.inl 1) (.inl 0) ?_⟩
  · have : D = am (D 0 0) (D 0 1) (D 1 0) := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [am] <;>
        first | assumption | linear_combination e01 | linear_combination e02 | linear_combination e12
    rw [bm, ← this]
  · simp [wt6, wt1]; omega
  · simp [wt6, wt1]; omega
  · simp [wt6, wt1]; omega

end UpperTheory.V.U3.FixDim

open UpperTheory.V.U3.FixDim in
theorem UpperTheory.finrank_ker_adRep_complexConj_sub_one_eq_boxDef :
    ∀ (O k : Type) [CommRing O] [Field k] [Algebra O k], (2 : k) ≠ 0 → ∀ {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* kˣ) (c : Γ), η c = -1 → Ψ c = 1 → ∀ j : ℤ,
          Module.finrank k (LinearMap.ker (FormData.adRep (blockPairingForm_normalises_baseLift O η Ψ) j c - 1)) = boxDef j := by
  intro O k _ _ _ h2 Γ _ η Ψ c h1 hΨ j
  have e1 := emb_c η Ψ c h1 hΨ
  have e2 := emb_c η Ψ c⁻¹ (by rw [map_inv, h1]; rfl) (by rw [map_inv, hΨ, inv_one])
  have hk : ∀ Y : (form6 O).gw k j, Y ∈ LinearMap.ker (FormData.adRep (blockPairingForm_normalises_baseLift O η Ψ) j c - 1) ↔
      sw k * Y.1 * sw k = Y.1 := by
    intro Y
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Subtype.ext_iff]
    show emb (r0 η Ψ c) * Y.1 * emb (r0 η Ψ c⁻¹) = Y.1 ↔ _
    rw [e1, e2]
  have one : ∀ x y z : k, (j ≠ 0 → x = 0) → (j ≠ 1 → y = 0) → (j ≠ -1 → z = 0) → bm x y z ≠ 0 →
      (∀ x' y' z' : k, (j ≠ 0 → x' = 0) → (j ≠ 1 → y' = 0) → (j ≠ -1 → z' = 0) →
        ∃ t : k, t * x = x' ∧ t * y = y' ∧ t * z = z') →
      Module.finrank k (LinearMap.ker (FormData.adRep (blockPairingForm_normalises_baseLift O η Ψ) j c - 1)) = 1 := by
    intro x y z hx hy hz hne hgen
    refine finrank_eq_one_iff'.2 ⟨⟨⟨bm x y z, bm_mem O j x y z hx hy hz⟩, (hk _).2 (sw_bm x y z)⟩, ?_, ?_⟩
    · intro h
      exact hne (congrArg (fun v => v.1.1) h)
    · rintro ⟨Y, hY⟩
      obtain ⟨x', y', z', e, h⟩ := eq_bm O h2 j Y.1 Y.2 ((hk Y).1 hY)
      obtain ⟨t, rfl, rfl, rfl⟩ := hgen x' y' z' h.1 h.2.1 h.2.2
      refine ⟨t, Subtype.ext (Subtype.ext ?_)⟩
      show t • bm x y z = Y.1
      rw [e, bm_smul]
  by_cases j0 : j = 0
  · subst j0
    refine one 1 0 0 (by simp) (by simp) (by simp) (fun h => ?_) (fun x y z _ hy hz => ⟨x, by simp, ?_, ?_⟩)
    · simpa [bm, am] using congrFun (congrFun h (.inl 0)) (.inl 0)
    · simp [hy (by decide)]
    · simp [hz (by decide)]
  by_cases j1 : j = 1
  · subst j1
    refine one 0 1 0 (by simp) (by simp) (by simp) (fun h => ?_) (fun x y z hx _ hz => ⟨y, ?_, by simp, ?_⟩)
    · simpa [bm, am] using congrFun (congrFun h (.inl 0)) (.inl 1)
    · simp [hx (by decide)]
    · simp [hz (by decide)]
  by_cases j2 : j = -1
  · subst j2
    refine one 0 0 1 (by simp) (by simp) (by simp) (fun h => ?_) (fun x y z hx hy _ => ⟨z, ?_, ?_, by simp⟩)
    · simpa [bm, am] using congrFun (congrFun h (.inl 1)) (.inl 0)
    · simp [hx (by decide)]
    · simp [hy (by decide)]
  rw [boxDef, if_neg (by rw [abs_le]; omega), Submodule.finrank_eq_zero, eq_bot_iff]
  intro Y hY
  obtain ⟨x, y, z, e, hx, hy, hz⟩ := eq_bm O h2 j Y.1 Y.2 ((hk Y).1 hY)
  rw [Submodule.mem_bot]
  refine Subtype.ext ?_
  rw [e, hx j0, hy j1, hz j2]
  simpa using (bm_smul (0 : k) 0 0 0).symm
end

