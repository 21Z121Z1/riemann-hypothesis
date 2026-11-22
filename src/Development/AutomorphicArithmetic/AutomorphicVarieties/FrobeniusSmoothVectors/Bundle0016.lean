import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EpresDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OfForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.NegOneZpowSg
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem neg_one_zpow_sg (K : Type) [CommRing K] (j : ℤ) :
    (((-1 : Kˣ) ^ j : Kˣ) : K) = sg K (j : ZMod 2) := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' j
  · rw [Even.neg_one_zpow (even_two_mul k)]
    push_cast
    rw [h2, zero_mul]
    simp [sg]
  · rw [Odd.neg_one_zpow (odd_two_mul_add_one k)]
    push_cast
    rw [h2, zero_mul, zero_add]
    show _ = (-1 : K) ^ 1
    simp

private theorem map_sg {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (j : ZMod 2) :
    f (sg K j) = sg K' j := by simp [sg]

private theorem sg_sq (K : Type) [CommRing K] (j : ZMod 2) : sg K j * sg K j = 1 := by
  rw [sg, ← mul_pow]; simp

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)}
  (S : Space O F 3)

private theorem ex_tau : ∃ τ : S.R →ₐ[O] S.R,
    (∀ g i j, τ (S.ρ.r g i j) = (((-1 : S.Rˣ) ^ (w 3 i - w 3 j) : S.Rˣ) : S.R) * S.ρ.r g i j) ∧
      ∀ v i g, τ (S.ρ.ψ v i g) = S.ρ.ψ v i g := by
  obtain ⟨ρ', h1, h2⟩ := alg_twist (-1 : S.Rˣ) S.ρ
  obtain ⟨⟨c1, c2⟩, ⟨b1, b2⟩, d⟩ := S.lift
  have hl : IsLift O ρ' := by
    refine ⟨⟨fun i j N => ?_, by rw [h2]; exact c2⟩, ⟨fun g i => ?_, fun v i g => ?_⟩, fun g i j hij => ?_⟩
    · simp only [h1, map_mul]
      exact (c1 i j N).comp (fun y => Ideal.Quotient.mk _ _ * y)
    · rw [NRep.map_r, h1, sub_self, zpow_zero, Units.val_one, one_mul]
      exact b1 g i
    · rw [NRep.map_ψ, h2]
      exact b2 v i g
    · rw [NRep.map_r, h1, map_mul]
      have := d g i j hij
      rw [NRep.map_r] at this
      rw [this, mul_zero]
  obtain ⟨τ, hτ, -⟩ := S.univ S.R ρ' hl
  refine ⟨τ, fun g i j => ?_, fun v i g => ?_⟩
  · rw [← h1, ← hτ]; rfl
  · conv_rhs => rw [← h2, ← hτ]
    rfl

private theorem tau_B (τ : S.R →ₐ[O] S.R)
    (h1 : ∀ g i j, τ (S.ρ.r g i j) = (((-1 : S.Rˣ) ^ (w 3 i - w 3 j) : S.Rˣ) : S.R) * S.ρ.r g i j)
    (h2 : ∀ v i g, τ (S.ρ.ψ v i g) = S.ρ.ψ v i g) : ∀ y ∈ S.B, τ y = y := by
  have hm : ∀ M : List (F.G0 × Fin 3 × Fin 3), τ (M.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod =
      (((-1 : S.Rˣ) ^ (M.map fun s => w 3 s.2.1 - w 3 s.2.2).sum : S.Rˣ) : S.R) *
        (M.map fun s => S.ρ.r s.1 s.2.1 s.2.2).prod := by
    intro M
    induction M with
    | nil => simp
    | cons a M ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul, h1, ih, _root_.zpow_add, Units.val_mul]
      ring
  have ha : ∀ y ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}), τ y = y := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨M, e, rfl⟩ | ⟨v, i, g, rfl⟩
      · rw [hm, e]; simp
      · exact h2 v i g
    | algebraMap r => exact τ.commutes r
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]
  have hloc : (maximalIdeal S.R).map τ ≤ maximalIdeal S.R := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, ← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  intro y hy
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := maximalIdeal S.R) inferInstance _ fun N => ?_
  obtain ⟨z, hz, hyz⟩ := hy N
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have e : τ y - y = τ (y - z) - (y - z) := by rw [map_sub, ha z hz]; ring
  rw [e]
  refine sub_mem ?_ hyz
  have := Ideal.mem_map_of_mem τ hyz
  rw [Ideal.map_pow] at this
  exact Ideal.pow_right_mono hloc N this

private theorem ex_tauA : ∃ τ : S.A →ₐ[O] S.A,
    (∀ g i j, τ (S.u.r g i j) = sg S.A (pw i j) * S.u.r g i j) ∧ (∀ y : S.B, τ (S.inc y) = S.inc y) ∧
      (∀ a, τ (τ a) = a) ∧ ∀ a, τ a - a ∈ S.u.ee := by
  obtain ⟨τ, h1, h2⟩ := ex_tau S
  have hB := tau_B S τ h1 h2
  have h1' : ∀ g i j, τ (S.ρ.r g i j) = sg S.R (pw i j) * S.ρ.r g i j := fun g i j => by
    rw [h1, neg_one_zpow_sg]; rfl
  have hA : ∀ y ∈ S.A, τ y ∈ S.A := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with hy | ⟨g, i, j, rfl⟩
      · rw [hB y hy]; exact S.B_le_A hy
      · rw [h1']
        exact mul_mem (pow_mem (neg_mem (one_mem _)) _) (S.r_mem g i j)
    | algebraMap r => rw [τ.commutes r]; exact S.A.algebraMap_mem r
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  let τA : S.A →ₐ[O] S.A := (τ.comp S.A.val).codRestrict S.A fun a => hA a a.2
  have e1 : ∀ g i j, τA (S.u.r g i j) = sg S.A (pw i j) * S.u.r g i j := fun g i j =>
    Subtype.ext ((h1' g i j).trans (by
      rw [← map_sg (S.A.val : S.A →+* S.R)]; rfl))
  have e2 : ∀ y : S.B, τA (S.inc y) = S.inc y := fun y => Subtype.ext (hB y y.2)
  have ind : ∀ P : S.A → Prop, (∀ y : S.B, P (S.inc y)) → (∀ g i j, P (S.u.r g i j)) →
      (∀ a b, P a → P b → P (a + b)) → (∀ a b, P a → P b → P (a * b)) → ∀ a, P a := by
    intro P p1 p2 p3 p4 ⟨y, hy⟩
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with hy | ⟨g, i, j, rfl⟩
      · exact p1 ⟨y, hy⟩
      · exact p2 g i j
    | algebraMap r => exact p1 (algebraMap O S.B r)
    | add a b ha hb qa qb => exact p3 ⟨a, ha⟩ ⟨b, hb⟩ qa qb
    | mul a b ha hb qa qb => exact p4 ⟨a, ha⟩ ⟨b, hb⟩ qa qb
  refine ⟨τA, e1, e2, ind _ (fun y => by rw [e2, e2]) (fun g i j => ?_) (fun a b qa qb => ?_) fun a b qa qb => ?_,
    ind _ (fun y => by rw [e2, sub_self]; exact zero_mem _) (fun g i j => ?_) (fun a b qa qb => ?_)
      fun a b qa qb => ?_⟩
  · rw [e1, map_mul, e1, ← mul_assoc]
    have := map_sg (τA : S.A →+* S.A) (pw i j)
    rw [RingHom.coe_coe] at this
    rw [this, sg_sq, one_mul]
  · rw [map_add, map_add, qa, qb]
  · rw [map_mul, map_mul, qa, qb]
  · rw [e1, pw, ← neg_one_zpow_sg]
    rcases Int.even_or_odd (w 3 i - w 3 j) with h | h
    · rw [h.neg_one_zpow]; simp
    · exact sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨g, i, j, h, rfl⟩))
        (Ideal.subset_span ⟨g, i, j, h, rfl⟩)
  · rw [map_add, add_sub_add_comm]; exact add_mem qa qb
  · have : τA (a * b) - a * b = (τA a - a) * τA b + a * (τA b - b) := by rw [map_mul]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ qa) (Ideal.mul_mem_left _ _ qb)

end

theorem UpperTheory.V.Fr.ep_inv :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ}, F.Ok C₀ → ∀ S : Space O F 3, ∀ (x : Ideal S.A) (L : S.Loc x), S.u.ee ≤ x → ∃ σ, L.IsInv σ := by
  intro l _ O _ _ _ _ F C₀ _ S x L hx
  obtain ⟨τ, h1, h2, h3, h4⟩ := ex_tauA S
  obtain ⟨σ, hσ, -⟩ := L.univ L.R (L.ι.comp τ) fun a => by
    rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff, AlgHom.comp_apply, ← map_sub]
    have := hx (h4 a)
    rw [← L.lies] at this
    exact this
  obtain ⟨g₀, -, hu⟩ := L.univ L.R L.ι fun _ => rfl
  have hsq : σ.comp σ = AlgHom.id _ _ :=
    (hu (σ.comp σ) fun a => by
      rw [AlgHom.comp_apply, hσ, AlgHom.comp_apply, hσ, AlgHom.comp_apply, h3]).trans
      (hu (AlgHom.id _ _) fun _ => rfl).symm
  refine ⟨σ, fun y => DFunLike.congr_fun hsq y, fun g a b => ?_, fun y => ?_⟩
  · show σ (L.ι (S.u.r g a b)) = sg _ _ * L.ι (S.u.r g a b)
    rw [hσ, AlgHom.comp_apply, h1, map_mul, ← map_sg (L.ι : S.A →+* L.R)]
    rfl
  · show σ (L.ι (S.inc y)) = sg _ _ * L.ι (S.inc y)
    rw [hσ, AlgHom.comp_apply, h2]
    simp [sg]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.NontrivTr
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem rank_tr {k K G V : Type} [Field k] [Field K] (f : k →+* K) [Group G] [TopologicalSpace G]
    [CompactSpace G] {Gv : V → Type} [∀ v, Group (Gv v)] [Finite V] (loc : ∀ v, Gv v →* G) (χ : G →* kˣ)
    (χ' : G →* Kˣ) (h : ∀ g, χ' g = Units.map f.toMonoidHom (χ g)) :
    Module.rank K (H1C loc (chRep χ') fun _ => ⊥) = Module.rank k (H1C loc (chRep χ) fun _ => ⊥) ∧
    Module.rank K (H1C loc (chRep χ') fun _ => ⊤) = Module.rank k (H1C loc (chRep χ) fun _ => ⊤) := by
  have hχ : χ' = (Units.map (f : k →* K)).comp χ := MonoidHom.ext fun g => h g
  subst hχ
  exact ⟨(n4ch f loc χ (fun _ => ⊥) (fun _ => ⊥) (fun _ => Or.inl ⟨rfl, rfl⟩)).2,
    (n4ch f loc χ (fun _ => ⊤) (fun _ => ⊤) (fun _ => Or.inr ⟨rfl, rfl⟩)).2⟩

private theorem nontriv_tr {k K M N : Type} [Field k] [Field K] [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module K N] (e : Module.rank K N = Module.rank k M) (h : Nontrivial M) : Nontrivial N := by
  rw [← rank_pos_iff_nontrivial (R := K), e]
  exact rank_pos_iff_nontrivial.2 h

theorem UpperTheory.V.Fr.ok_ext :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ} {k' : Type} [Field k'] [Finite k'] [CharP k' l] (f : k →+* k'), F.Ok C₀ → (F.ext f).Ok C₀ := by
  intro l _ k _ _ F C₀ k' _ _ _ f h
  have hinj : Function.Injective f := f.injective
  have hU : ∀ u v : kˣ, Units.map (f : k →* k') u = Units.map (f : k →* k') v → u = v := by
    intro u v huv
    ext
    apply hinj
    simpa using congrArg Units.val huv
  have hU1 : ∀ u : kˣ, Units.map (f : k →* k') u = 1 → u = 1 := by
    intro u hu
    apply hU
    rw [hu, map_one]
  have hΨ : ∀ g, (F.ext f).Ψ g = Units.map (f : k →* k') (F.Ψ g) := fun g => rfl
  have hz : ∀ x : ZMod l, f (ZMod.castHom (dvd_refl l) k x) = ZMod.castHom (dvd_refl l) k' x :=
    fun x => RingHom.congr_fun
      (Subsingleton.elim (f.comp (ZMod.castHom (dvd_refl l) k)) (ZMod.castHom (dvd_refl l) k')) x
  have hom : ∀ g, (F.ext f).om k' g = Units.map (f : k →* k') (F.om k g) := by
    intro g
    ext
    change ((ZMod.castHom (dvd_refl l) k').comp PadicInt.toZMod) ((F.eps g : ℤ_[l])) =
      f (((ZMod.castHom (dvd_refl l) k).comp PadicInt.toZMod) ((F.eps g : ℤ_[l])))
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact (hz _).symm
  have hdel : ∀ g, (F.ext f).delK k' g = Units.map (f : k →* k') (F.delK k g) := by
    intro g
    ext
    change (Int.castRingHom k') (F.del g : ℤ) = f ((Int.castRingHom k) (F.del g : ℤ))
    simp
  have hker : (F.ext f).Ψ.ker = F.Ψ.ker := by
    ext g
    simp only [MonoidHom.mem_ker]
    exact ⟨hU1 _, fun h1 => by rw [hΨ, h1, map_one]⟩
  haveI : CompactSpace F.G0 :=
    isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ h.del_open).isCompact
  have hχ1 : ∀ g : F.Γ, ((F.ext f).Ψ⁻¹ * (F.ext f).delK k') g =
      Units.map f.toMonoidHom ((F.Ψ⁻¹ * F.delK k) g) := by
    intro g
    change ((F.ext f).Ψ g)⁻¹ * (F.ext f).delK k' g = Units.map f.toMonoidHom ((F.Ψ g)⁻¹ * F.delK k g)
    erw [hdel, hΨ, map_mul, map_inv]
    rfl
  have hχ2 : ∀ g : F.Γ, ((F.ext f).Ψ⁻¹ ^ 2 * (F.ext f).delK k') g =
      Units.map f.toMonoidHom ((F.Ψ⁻¹ ^ 2 * F.delK k) g) := by
    intro g
    rw [pow_two, pow_two]
    change ((F.ext f).Ψ g)⁻¹ * ((F.ext f).Ψ g)⁻¹ * (F.ext f).delK k' g =
      Units.map f.toMonoidHom ((F.Ψ g)⁻¹ * (F.Ψ g)⁻¹ * F.delK k g)
    erw [hdel, hΨ, map_mul, map_mul, map_inv]
    rfl
  have hχ3 : ∀ g : F.G0, ((F.ext f).Ψ⁻¹.comp (F.ext f).del.ker.subtype) g =
      Units.map f.toMonoidHom ((F.Ψ⁻¹.comp F.del.ker.subtype) g) := by
    intro g
    change (Units.map (f : k →* k') (F.Ψ (g : F.Γ)))⁻¹ = Units.map f.toMonoidHom ((F.Ψ (g : F.Γ))⁻¹)
    rw [map_inv]
    rfl
  have hχ4 : ∀ g : F.Γ, (1 : F.Γ →* k'ˣ) g = Units.map f.toMonoidHom ((1 : F.Γ →* kˣ) g) := by
    intro g
    rw [MonoidHom.one_apply, MonoidHom.one_apply, map_one]
  exact
    { l_odd := h.l_odd
      fin := inferInstance
      del_open := h.del_open
      c_sq := h.c_sq
      del_c := h.del_c
      loc_cont := h.loc_cont
      eps_cont := h.eps_cont
      Ψ_open := by rw [hker]; exact h.Ψ_open
      Ψ_c := by
        show Units.map (f : k →* k') (F.Ψ F.c) = 1
        rw [h.Ψ_c, map_one]
      baseSubgroup_spec := fun he => h.baseSubgroup_spec (hU1 _ (by rw [map_pow]; exact he))
      phi := h.phi
      card_inf := h.card_inf
      cw_sq := h.cw_sq
      del_cw := h.del_cw
      f2a := by
        obtain ⟨g, hg⟩ := h.f2a
        refine ⟨g, fun he => hg (hU1 _ ?_)⟩
        rw [hom] at he
        exact he
      f2b := by
        intro j hj
        obtain ⟨g, hg⟩ := h.f2b j hj
        refine ⟨g, fun he => hg (hU1 _ ?_)⟩
        rw [hom, hΨ] at he
        rw [map_mul, map_zpow]
        exact he
      f2c := by
        intro j hj
        obtain ⟨g, hg⟩ := h.f2c j hj
        refine ⟨g, fun he => hg (hU1 _ ?_)⟩
        erw [hom, hdel] at he
        rw [map_mul, map_mul, map_zpow]
        exact he
      f3 := by
        intro v
        obtain ⟨g, hg⟩ := h.f3 v
        exact ⟨g, fun he => hg (hU1 _ (by rw [map_pow]; exact he))⟩
      f4 := nontriv_tr (rank_tr f F.loc _ _ hχ1).1 h.f4
      f4' := nontriv_tr (rank_tr f F.loc _ _ hχ2).1 h.f4'
      f5 := by
        rintro ⟨j, hj⟩
        refine h.f5 ⟨j, fun g => hU _ _ ?_⟩
        have hg := hj g
        rw [hom, hΨ] at hg
        rw [map_zpow]
        exact hg
      Ψ_N := fun v g hg => by
        show Units.map (f : k →* k') (F.Ψ (F.loc v g)) = 1
        rw [h.Ψ_N v g hg, map_one]
      gen := by
        intro v
        obtain ⟨u, a₀, h1, h2, h3⟩ := h.gen v
        refine ⟨u, a₀, fun a => ⟨(h1 a).1, ?_⟩, h2, h3⟩
        show Units.map (f : k →* k') (F.Ψ (F.loc v (u a))) = 1
        rw [(h1 a).2, map_one]
      cl := h.cl
      ec := h.ec
      b1p := (rank_tr f F.loc _ _ hχ2).1.trans_le h.b1p
      b1 := (rank_tr f F.loc2 _ _ hχ3).1.trans_le h.b1
      h1 := (rank_tr f F.loc _ _ hχ4).2.trans_le h.h1 }
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.OfTrace
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem zero_of_trace {G K : Type} [Monoid G] [Field K] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) K)
    (h : Submodule.span K (Set.range ρ) = ⊤) (X : Matrix (Fin n) (Fin n) K) (hX : ∀ g, (ρ g * X).trace = 0) :
    X = 0 := by
  have hall : ∀ M : Matrix (Fin n) (Fin n) K, (M * X).trace = 0 := by
    intro M
    have hM : M ∈ Submodule.span K (Set.range ρ) := by rw [h]; trivial
    induction hM using Submodule.span_induction with
    | mem x hx => obtain ⟨t, rfl⟩ := hx; exact hX t
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul a x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  ext i j
  simpa [Matrix.trace_single_mul] using hall (Matrix.single j i 1)

private theorem span_of_trace {G C K K' : Type} [Monoid G] [CommRing C] [Field K] [Field K'] {n : ℕ}
    (f : C →+* K) (hf : Function.Injective f) (φ : C →+* K') (t : G → C)
    (ρ : G →* Matrix (Fin n) (Fin n) K) (ρ' : G →* Matrix (Fin n) (Fin n) K')
    (h : ∀ g, f (t g) = (ρ g).trace) (h' : ∀ g, φ (t g) = (ρ' g).trace)
    (hs : Submodule.span K' (Set.range ρ') = ⊤) : Submodule.span K (Set.range ρ) = ⊤ := by
  obtain ⟨g, hg⟩ := (UpperTheory.V.AlgebraTools.Det.gramIff ρ').mp hs
  refine (UpperTheory.V.AlgebraTools.Det.gramIff ρ).mpr ⟨g, fun h0 => hg ?_⟩
  have e : (Matrix.of fun a b => (ρ (g a * g b)).trace) = f.mapMatrix (Matrix.of fun a b => t (g a * g b)) := by
    ext a b
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, h]
  have e' : (Matrix.of fun a b => (ρ' (g a * g b)).trace) = φ.mapMatrix (Matrix.of fun a b => t (g a * g b)) := by
    ext a b
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, h']
  rw [e, ← RingHom.map_det, map_eq_zero_iff f hf] at h0
  rw [e', ← RingHom.map_det, h0, map_zero]

private theorem lift_surj {G K : Type} [Group G] [Field K] {n : ℕ} (ρ : G →* Matrix (Fin n) (Fin n) K)
    (h : Submodule.span K (Set.range ρ) = ⊤) :
    Function.Surjective (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) G ρ) := by
  have : LinearMap.range (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) G ρ).toLinearMap = ⊤ := by
    rw [eq_top_iff, ← h, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨MonoidAlgebra.of K G g, by simp⟩
  exact LinearMap.range_eq_top.1 this

private theorem conj_of_trace {G K : Type} [Group G] [Field K] {n : ℕ} (ρ₁ ρ₂ : G →* Matrix (Fin n) (Fin n) K)
    (h₂ : Submodule.span K (Set.range ρ₂) = ⊤) (hf : ∀ g, (ρ₁ g).trace = (ρ₂ g).trace) :
    ∃ P : Matrix (Fin n) (Fin n) K, IsUnit P ∧ ∀ g, ρ₁ g * P = P * ρ₂ g := by
  have h₁ := span_of_trace (RingHom.id K) Function.injective_id (RingHom.id K) (fun g => (ρ₁ g).trace) ρ₁ ρ₂
    (fun _ => rfl) hf h₂
  set R₁ := MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) G ρ₁ with hR₁
  set R₂ := MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) G ρ₂ with hR₂
  have s₂ : Function.Surjective R₂ := lift_surj ρ₂ h₂
  have e1 : ∀ g, R₁ (MonoidAlgebra.of K G g) = ρ₁ g := fun g => by simp [hR₁]
  have e2 : ∀ g, R₂ (MonoidAlgebra.of K G g) = ρ₂ g := fun g => by simp [hR₂]
  have hf' : ∀ a, (R₁ a).trace = (R₂ a).trace := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g => rw [e1, e2, hf]
    | add a b ha hb => simp only [map_add, Matrix.trace_add, ha, hb]
    | smul c a ha => simp only [map_smul, Matrix.trace_smul, ha]
  have hker : ∀ a, R₂ a = 0 → R₁ a = 0 := by
    intro a ha
    refine zero_of_trace ρ₁ h₁ _ fun g => ?_
    rw [← e1, ← map_mul, hf', map_mul, ha, mul_zero, Matrix.trace_zero]
  let φ₀ := RingHom.liftOfSurjective R₂.toRingHom s₂ ⟨R₁.toRingHom, fun a ha => hker a ha⟩
  have hφ₀ : ∀ a, φ₀ (R₂ a) = R₁ a := fun a => RingHom.liftOfSurjective_comp_apply R₂.toRingHom s₂ _ a
  let φ : Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) K :=
    ⟨φ₀, fun c => by
      have := hφ₀ (algebraMap K _ c)
      rwa [AlgHom.commutes, AlgHom.commutes] at this⟩
  obtain ⟨J, hJ⟩ := KStar.Tree.exists_conj_of_algHom φ
  refine ⟨J, J.isUnit, fun g => ?_⟩
  have h1 := hJ (R₂ (MonoidAlgebra.of K G g))
  have e : φ (R₂ (MonoidAlgebra.of K G g)) = R₁ (MonoidAlgebra.of K G g) := hφ₀ _
  rwa [e, e1, e2] at h1

private theorem alt_two {K : Type} [Field K] (h2 : (2 : K) ≠ 0) (P A B : Matrix (Fin 2) (Fin 2) K) (hP : IsUnit P)
    (hs : Pᵀ = -P) (h : Bᵀ * P = P * A) : A + B = A.trace • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have d : ∀ i, P i i = 0 := fun i => by
    have := congrFun (congrFun hs i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    exact (mul_eq_zero.1 (by linear_combination this : 2 * P i i = 0)).resolve_left h2
  have o : P 1 0 = -P 0 1 := congrFun (congrFun hs 0) 1
  have u : P 0 1 ≠ 0 := by
    have := ((Matrix.isUnit_iff_isUnit_det _).1 hP).ne_zero
    rw [Matrix.det_fin_two, d, d, o] at this
    intro h0
    simp [h0] at this
  have k := fun i j => congrFun (congrFun h i) j
  have k00 := k 0 0
  have k01 := k 0 1
  have k10 := k 1 0
  have k11 := k 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, d, o] at k00 k01 k10 k11
  ext i j
  apply mul_left_cancel₀ u
  fin_cases i <;> fin_cases j <;> simp [Matrix.trace_fin_two, -mul_eq_mul_left_iff, -mul_eq_zero]
  · linear_combination k01
  · linear_combination k11
  · linear_combination -k00
  · linear_combination -k10

private theorem not_alt {G K : Type} [Group G] [Field K] (h2 : (2 : K) ≠ 0) (ρ : G →* Matrix (Fin 2) (Fin 2) K)
    (hs : Submodule.span K (Set.range ρ) = ⊤)
    (h : ∀ g x, (ρ x * ρ g).trace + (ρ x * (Jmat K 2 * (ρ g)ᵀ * Jmat K 2)).trace = (ρ g).trace * (ρ x).trace) :
    False := by
  have h1 : ∀ g, ρ g 0 1 = 0 := fun g => by
    have := zero_of_trace ρ hs (ρ g + Jmat K 2 * (ρ g)ᵀ * Jmat K 2 - (ρ g).trace • 1) fun x => by
      rw [Matrix.mul_sub, Matrix.mul_add, Matrix.trace_sub, Matrix.trace_add, h, Matrix.mul_smul, Matrix.mul_one,
        Matrix.trace_smul, smul_eq_mul, sub_self]
    have e := congrFun (congrFun this 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Jmat, Fin.rev] at e
    exact (mul_eq_zero.1 (by linear_combination e : 2 * ρ g 0 1 = 0)).resolve_left h2
  have := zero_of_trace ρ hs (Matrix.single 1 0 1) fun g => by simp [Matrix.trace_mul_single, h1]
  simpa using congrFun (congrFun this 1) 0

theorem UpperTheory.V.Fr.of_trace :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [Field K] [IsAlgClosed K] [Algebra C K], Function.Injective (algebraMap C K) → ∀ (r : F.G0 →* Matrix (Fin n) (Fin n) K) (t : F.G0 → C) (χ : ∀ v, Fin n → F.Gv v →* Cˣ), IsTr O F n t → (∀ g, algebraMap C K (t g) = (r g).trace) → (∀ g, t (F.star g) = t g) → IsPsi O F n (fun v i g => (χ v i g : C)) → (∀ v g h, (r h * ordProd (fun s => r (F.loc0 v s)) (fun i s => algebraMap C K (χ v i s)) g).trace = 0) → ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (φ : C →+* K') (ρ' : NRep F n K'), MatIrr ⊤ ρ'.r → (∀ g, φ (t g) = (ρ'.r g).trace) → ∃ (ρ : NRep F n K) (h : GL (Fin n) K), (∀ g, ρ.r g = h * r g * h⁻¹) ∧ (∀ v i g, (ρ.ψ v i g : K) = algebraMap C K (χ v i g)) ∧ Integral O C ρ ∧ MatIrr ⊤ ρ.r := by
  intro l _ O _ _ _ _ F C₀ n hF hn C _ _ _ K _ _ _ hinj r t χ ht htr hst hχ hord K' _ _ φ ρ' hirr hφ
  obtain ⟨ss, sm, -, -, -⟩ := UpperTheory.V.Fr.star hF
  have h2C : IsUnit (2 : C) := by
    by_contra hn2
    have h0 := (res_eq_zero_iff O C 2).2 hn2
    rw [map_ofNat] at h0
    have := (CharP.cast_eq_zero_iff (ResidueField O) l 2).1 (by exact_mod_cast h0)
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have h2K : (2 : K) ≠ 0 := by simpa [map_ofNat] using (h2C.map (algebraMap C K)).ne_zero
  have h2K' : (2 : K') ≠ 0 := by simpa [map_ofNat] using (h2C.map φ).ne_zero
  have hs' : Submodule.span K' (Set.range ρ'.r) = ⊤ :=
    (UpperTheory.V.AlgebraTools.Det.irrIffSpan ρ'.r).1 fun N hN => hirr N fun g _ => hN g
  have hs := span_of_trace (algebraMap C K) hinj φ t r ρ'.r htr hφ hs'
  have s1 : F.star 1 = 1 := by simp [Frame.star]
  let r' : F.G0 →* Matrix (Fin n) (Fin n) K :=
    { toFun := fun g => (r (F.star g))ᵀ
      map_one' := by rw [s1, map_one, Matrix.transpose_one]
      map_mul' := fun g h => by rw [sm, map_mul, Matrix.transpose_mul] }
  obtain ⟨P, hP, hPr⟩ := conj_of_trace r' r hs fun g => by
    show (r (F.star g))ᵀ.trace = _
    rw [Matrix.trace_transpose, ← htr, ← htr, hst]
  replace hPr : ∀ g, (r (F.star g))ᵀ * P = P * r g := hPr
  have sc : ∀ g, F.star g * F.conj g = 1 := fun g => by rw [Frame.star, ← map_mul, inv_mul_cancel, map_one]
  have hform : ∀ g, (r g)ᵀ * P * r (F.conj g) = P := fun g => by
    have := hPr (F.star g)
    rw [ss] at this
    rw [this, Matrix.mul_assoc, ← map_mul, sc, map_one, Matrix.mul_one]
  have cc : ∀ g, F.conj (F.conj g) = g := fun g => by
    have := ss g
    simpa only [Frame.star, map_inv, inv_inv] using this
  have hsym : Pᵀ = P := by
    refine (UpperTheory.V.AlgebraTools.Det.signLemma r F.conj (fun _ => 1) P hs cc (fun _ => rfl) hP
      fun g => by rw [hform, one_smul]).resolve_right fun ha => ?_
    rcases hn with rfl | rfl
    · refine not_alt h2K' ρ'.r hs' fun g x => ?_
      rw [← ρ'.pol, ← map_mul, ← map_mul, ← hφ, ← hφ, ← hφ, ← hφ, ← map_add, ← map_mul]
      congr 1
      apply hinj
      rw [map_add, map_mul, htr, htr, htr, htr, map_mul, map_mul, ← Matrix.trace_add, ← Matrix.mul_add,
        alt_two h2K P _ _ hP ha (hPr g), Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
    · have hd := congrArg Matrix.det ha
      rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at hd
      exact mul_ne_zero h2K ((Matrix.isUnit_iff_isUnit_det _).1 hP).ne_zero (by linear_combination hd)
  obtain ⟨ρ, h, h1, h2, h3⟩ := UpperTheory.V.Fr.of_form hF hn C K hinj r P t χ hP hsym hform ht htr hχ
    fun v g => zero_of_trace r hs _ (hord v g)
  refine ⟨ρ, h, h1, h2, h3, fun N hN => ?_⟩
  refine (UpperTheory.V.AlgebraTools.Det.irrIffSpan ρ.r).2 ?_ N fun g => hN g trivial
  refine span_of_trace (algebraMap C K) hinj φ t ρ.r ρ'.r (fun g => ?_) hφ hs'
  rw [h1, htr, Matrix.trace_mul_cycle, Units.inv_mul, Matrix.one_mul]
end

