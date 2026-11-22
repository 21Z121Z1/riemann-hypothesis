import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BurnsideEnd
section
theorem UpperTheory.Reformulated.B.Qj3.burnside_end.{u_3, u_4} :
    ∀ {K : Type u_3} {V : Type u_4} [inst : Field K] [IsAlgClosed K] [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [FiniteDimensional K V] (S : Subalgebra K (Module.End K V)),
    (∀ (N : Submodule K V), (∀ f ∈ S, ∀ v ∈ N, (f : V → V) v ∈ N) → N = ⊥ ∨ N = ⊤) → ∀ (f : Module.End K V), f ∈ S := by
  intro K V _ _ _ _ _ S h f
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : f = 0 := by ext v; exact Subsingleton.elim _ _
    rw [this]; exact S.zero_mem
  haveI : IsSimpleModule S V := by
    refine { eq_bot_or_eq_top := fun N => ?_ }
    rcases h (N.restrictScalars K) (fun g hg v hv => N.smul_mem (⟨g, hg⟩ : S) hv) with h1 | h1
    · left
      exact (Submodule.restrictScalars_eq_bot_iff _ _ _).1 h1
    · right
      exact (Submodule.restrictScalars_eq_top_iff _ _ _).1 h1
  have hs := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K (A := S) (V := V)).2
  let F : Module.End (Module.End S V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, rfl⟩ := hs φ
        simp [Module.End.smul_def, Module.algebraMap_end_apply] }
  classical
  let b := Module.finBasis K V
  obtain ⟨r, hr⟩ := jacobson_density (R := S) F (Finset.univ.image b)
  have : f = (r : Module.End K V) := by
    refine b.ext fun i => ?_
    exact hr (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]; exact r.2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardCount
section
namespace ListOfFnPermExistsEquivPerm

open Finset in
private theorem card_count {α : Type} [DecidableEq α] :
    ∀ {n : ℕ} (v : Fin n → α) (a : α), #{i | v i = a} = (List.ofFn v).count a
  | 0, v, a => by simp
  | n + 1, v, a => by
    have ih := card_count (fun i : Fin n => v i.succ) a
    rw [Fin.card_filter_univ_succ', List.ofFn_succ, List.count_cons, ih]
    by_cases h : v 0 = a <;> simp [h, add_comm]

end ListOfFnPermExistsEquivPerm

theorem UpperTheory.Reformulated.B.Yde7.main :
    ∀ {α : Type} {n : ℕ} (v w : Fin n → α),
      (List.ofFn v).Perm (List.ofFn w) → ∃ (s : Equiv.Perm (Fin n)), v = w ∘ (⇑s : Fin n → Fin n) := by
  intro α n v w h
  classical
  have hc : ∀ c, Fintype.card {i // v i = c} = Fintype.card {i // w i = c} := by
    intro c
    rw [Fintype.card_subtype, Fintype.card_subtype]
    convert (ListOfFnPermExistsEquivPerm.card_count v c).trans ((h.count_eq c).trans (ListOfFnPermExistsEquivPerm.card_count w c).symm)
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map _ i).symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardEmbeddingsRestrict
section
theorem UpperTheory.Reformulated.B.CardEmbeddingsRestrict.card_embeddings_restrict.{u_1, u_2} :
    ∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [NumberField K] [inst_2 : Field L] [inst_3 : NumberField L]
    [inst_4 : Algebra K L] (τ : K →+* ℂ),
    (open Classical in Finset.filter (fun σ : L →+* ℂ => σ.comp (Algebra.algebraMap K L) = τ) Finset.univ).card = Module.finrank K L := by
  intro K L _ _ _ _ _ τ
  classical
  letI : Algebra K ℂ := τ.toAlgebra
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  rw [← AlgHom.card K L ℂ, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun (f : L →ₐ[K] ℂ) _ => (f : L →+* ℂ)) ?_ ?_ ?_
  · intro f _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, RingHom.ext fun x => f.commutes x⟩
  · intro f _ g _ h
    exact AlgHom.ext fun x => RingHom.congr_fun h x
  · intro σ hσ
    rw [Finset.mem_filter] at hσ
    exact ⟨{ σ with commutes' := fun x => RingHom.congr_fun hσ.2 x }, Finset.mem_univ _, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardFiber
section
namespace MultisetMapEqExistsEquivPerm

private lemma card_fiber {α : Type*} [DecidableEq α] {l : ℕ} (x : Fin l → α) (v : α) :
    Fintype.card {a : Fin l // x a = v} =
      (Multiset.map x Finset.univ.val).countP (fun b => b = v) := by
  rw [Multiset.countP_map, Fintype.card_subtype]
  rfl

end MultisetMapEqExistsEquivPerm

theorem UpperTheory.Reformulated.B.Yhb6.main.{u_1} :
    ∀ {α : Type u_1} {l : ℕ} {x y : Fin l → α},
      Multiset.map y Finset.univ.val = Multiset.map x Finset.univ.val →
        ∃ (e : Equiv.Perm (Fin l)), ∀ (a : Fin l), y a = x ((e : Fin l → Fin l) a) := by
  intro α l x y h
  classical
  have hc : ∀ v : α, Fintype.card {a : Fin l // y a = v} = Fintype.card {a : Fin l // x a = v} := by
    intro v
    convert (MultisetMapEqExistsEquivPerm.card_fiber y v).trans
      ((congrArg (fun m => Multiset.countP (fun b => b = v) m) h).trans (MultisetMapEqExistsEquivPerm.card_fiber x v).symm)
  let E : ∀ v : α, {a : Fin l // y a = v} ≃ {a : Fin l // x a = v} :=
    fun v => Fintype.equivOfCardEq (hc v)
  refine ⟨Equiv.ofFiberEquiv E, fun a => ?_⟩
  exact (Equiv.ofFiberEquiv_map E a).symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardLe
section
namespace AddCharEqMulShift

private lemma card_le (F K : Type) [Field F] [Fintype F] [Field K] :
    Finite (AddChar F K) ∧ Nat.card (AddChar F K) ≤ Nat.card F := by
  have hli : LinearIndependent K
      (fun ψ : AddChar F K => ((AddChar.toMonoidHomEquiv ψ : Multiplicative F →* K) :
        Multiplicative F → K)) :=
    (linearIndependent_monoidHom (Multiplicative F) K).comp _
      AddChar.toMonoidHomEquiv.injective
  have hfin : Finite (AddChar F K) := hli.finite
  refine ⟨hfin, ?_⟩
  haveI : Fintype (AddChar F K) := Fintype.ofFinite _
  have h := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h
  simpa [Nat.card_eq_fintype_card] using h

end AddCharEqMulShift

theorem UpperTheory.Reformulated.B.Yde4.main :
    ∀ {F K : Type} [inst : Field F] [Fintype F] [inst_2 : Field K] (ψ₀ ψ : AddChar F K),
      ψ₀ ≠ (1 : AddChar F K) → ∃ (c : F), ψ = ψ₀.mulShift c := by
  intro F K _ _ _ ψ₀ ψ h
  obtain ⟨hfin, hle⟩ := AddCharEqMulShift.card_le F K
  have hinj : Function.Injective ψ₀.mulShift :=
    AddChar.to_mulShift_inj_of_isPrimitive (AddChar.IsPrimitive.of_ne_one h)
  obtain ⟨c, hc⟩ := (hinj.bijective_of_nat_card_le hle).2 ψ
  exact ⟨c, hc.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardPow
section
theorem UpperTheory.Reformulated.B.Qi54.card_pow :
    ∀ {E : Type} [inst : Field E] [NumberField E]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (q : ℕ),
    Nat.Prime q →
      (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal →
        ∃ (f : ℕ), Nat.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) = q ^ f := by
  intro E _ _ w q hq hmem
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  letI : Field (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Fintype (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Fintype.ofFinite _
  have h0 : (q : NumberField.RingOfIntegers E ⧸ w.asIdeal) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rwa [map_natCast] at this
  haveI : CharP (NumberField.RingOfIntegers E ⧸ w.asIdeal) q :=
    (CharP.charP_iff_prime_eq_zero (p := q) (hp := hq)).mpr h0
  obtain ⟨n, -, hn⟩ := FiniteField.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) q
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardQuotPow
section
theorem UpperTheory.Reformulated.B.Yzb5.aux1 :
    ∀ {F : Type} [inst : Field F], SubsemiringClass (Subring F) F := by
  intro F _
  infer_instance

noncomputable def UpperTheory.Reformulated.B.Yzb5.resQ :
    {F : Type} → [inst : Field F] → [inst_1 : ValuativeRel F] → ↥(ValuativeRel.valuation F).integer → ℕ :=
    fun {F : Type} [Field F] [ValuativeRel F] (ϖ : ↥(ValuativeRel.valuation F).integer) ↦
      Nat.card (↥(ValuativeRel.valuation F).integer ⧸ Ideal.span {ϖ})

private lemma UpperTheory.Reformulated.B.Yzb5.card_quot_pow {R : Type*} [CommRing R] [IsDomain R] (p : R) (hp : p ≠ 0)
    (n : ℕ) :
    Nat.card (R ⧸ Ideal.span {p ^ n}) = Nat.card (R ⧸ Ideal.span {p}) ^ n := by
  have hidx : ∀ x : R, Nat.card (R ⧸ Ideal.span {x}) = (Ideal.span {x}).toAddSubgroup.index :=
    fun x => rfl
  induction n with
  | zero =>
    have : (Ideal.span {(1 : R)}) = ⊤ := Ideal.span_singleton_one
    simp [this]
  | succ n ih =>
    have hinj : Function.Injective (AddMonoidHom.mulLeft (p ^ n)) :=
      mul_right_injective₀ (pow_ne_zero n hp)
    have h1 : AddSubgroup.map (AddMonoidHom.mulLeft (p ^ n)) (Ideal.span {p}).toAddSubgroup
        = (Ideal.span {p ^ (n + 1)}).toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton,
        AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨y, ⟨c, rfl⟩, rfl⟩
        exact ⟨c, by ring⟩
      · rintro ⟨c, rfl⟩
        exact ⟨p * c, ⟨c, rfl⟩, by ring⟩
    have h2 : AddSubgroup.map (AddMonoidHom.mulLeft (p ^ n)) (⊤ : AddSubgroup R)
        = (Ideal.span {p ^ n}).toAddSubgroup := by
      ext x
      simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton,
        AddMonoidHom.coe_mulLeft, AddSubgroup.mem_top, true_and]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨y, rfl⟩
      · rintro ⟨c, rfl⟩
        exact ⟨c, rfl⟩
    have h3 : (Ideal.span {p ^ (n + 1)}).toAddSubgroup.relIndex (Ideal.span {p ^ n}).toAddSubgroup
        = (Ideal.span {p}).toAddSubgroup.index := by
      rw [← h1, ← h2, AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
        AddSubgroup.relIndex_top_right]
    have hle : (Ideal.span {p ^ (n + 1)}).toAddSubgroup ≤ (Ideal.span {p ^ n}).toAddSubgroup := by
      rw [← h1, ← h2]
      exact AddSubgroup.map_mono le_top
    rw [hidx, ← AddSubgroup.relIndex_top_right,
      ← AddSubgroup.relIndex_mul_relIndex _ _ _ hle le_top, h3,
      AddSubgroup.relIndex_top_right, ← hidx p, ← hidx (p ^ n), ih, pow_succ, mul_comm]

private lemma UpperTheory.Reformulated.B.Yzb5.card_coker {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {p : R} (hp : Irreducible p) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (M : Matrix ι ι R) (hM : M.det ≠ 0) :
    ∃ (m : ℕ) (v : Rˣ), M.det = (v : R) * p ^ m ∧
      Nat.card ((ι → R) ⧸ LinearMap.range M.mulVecLin) = Nat.card (R ⧸ Ideal.span {p}) ^ m := by
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Matrix.eq_zero_of_mulVec_eq_zero hM hx
  have hrank : Module.finrank R (LinearMap.range M.mulVecLin) = Module.finrank R (ι → R) :=
    LinearMap.finrank_range_of_inj hinj
  let b0 := Pi.basisFun R ι
  let b' := Submodule.smithNormalFormTopBasis b0 hrank
  let a := Submodule.smithNormalFormCoeffs b0 hrank
  let ab := Submodule.smithNormalFormBotBasis b0 hrank
  have hab : ∀ i, (ab i : ι → R) = a i • b' i := Submodule.smithNormalFormBotBasis_def b0 hrank
  have ha0 : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b0 hrank
  let e := LinearEquiv.ofInjective M.mulVecLin hinj
  let c : Module.Basis ι R (ι → R) := ab.map e.symm
  have hc : ∀ i, M.mulVecLin (c i) = a i • b' i := by
    intro i
    rw [← hab i]
    have h := LinearEquiv.ofInjective_apply (f := M.mulVecLin) (h := hinj) (c i)
    rw [← h]
    simp [c, e]
  have hdet : b'.det (M.mulVecLin ∘ c) = ∏ i, a i := by
    rw [Module.Basis.det_apply]
    have : b'.toMatrix (M.mulVecLin ∘ c) = Matrix.diagonal a := by
      ext i j
      simp [Module.Basis.toMatrix_apply, hc, Matrix.diagonal_apply, Finsupp.single_apply, eq_comm]
      split_ifs with h
      · rw [h]
      · rfl
    rw [this, Matrix.det_diagonal]
  have hcomp := b'.det_comp M.mulVecLin c
  rw [hdet, ← Matrix.toLin'_apply', LinearMap.det_toLin'] at hcomp
  choose k hk using fun i => IsDiscreteValuationRing.associated_pow_irreducible (ha0 i) hp
  have hprod : Associated (∏ i, a i) (p ^ ∑ i, k i) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Associated.prod _ _ _ (fun i _ => hk i)
  obtain ⟨w, hw⟩ := b'.isUnit_det c
  have hassoc : Associated M.det (p ^ ∑ i, k i) :=
    Associated.trans ⟨w, by rw [hw, hcomp]⟩ hprod
  obtain ⟨v, hv⟩ := hassoc.symm
  refine ⟨∑ i, k i, v, by rw [← hv, mul_comm], ?_⟩
  rw [Nat.card_congr (Submodule.quotientEquivPiSpan _ b0 hrank).toEquiv, Nat.card_pi,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hs : Ideal.span {Submodule.smithNormalFormCoeffs b0 hrank i} = Ideal.span {p ^ k i} :=
    Ideal.span_singleton_eq_span_singleton.mpr (hk i)
  rw [hs, UpperTheory.Reformulated.B.Yzb5.card_quot_pow p hp.ne_zero]

theorem UpperTheory.Reformulated.B.Yzb5.relIndex_map :
    ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F] [IsNonarchimedeanLocalField F]
      {ϖ : ↥(ValuativeRel.valuation F).integer},
      Irreducible ϖ →
        ∀ {W : Type} [inst_4 : AddCommGroup W] [inst_5 : _root_.Module F W] {ι : Type} [Fintype ι] (b : Module.Basis ι F W)
          (ψ : W →ₗ[F] W) (a : ℤ) (u : (↥(ValuativeRel.valuation F).integer)ˣ),
          (LinearMap.det : (W →ₗ[F] W) → F) ψ = (↑ϖ : F) ^ a * (↑(↑u : ↥(ValuativeRel.valuation F).integer) : F) →
            ∀ (W0 : AddSubgroup W),
              (∀ (x : W), x ∈ W0 ↔ ∀ (i : ι), ((b.repr : W → ι →₀ F) x : ι → F) i ∈ (ValuativeRel.valuation F).integer) →
                (∀ (i j : ι),
                    ((b.repr : W → ι →₀ F) ((ψ : W → W) ((b : ι → W) j)) : ι → F) i ∈ (ValuativeRel.valuation F).integer) →
                  ∃ (m : ℕ), a = (↑m : ℤ) ∧ (AddSubgroup.map ψ.toAddMonoidHom W0).relIndex W0 = UpperTheory.Reformulated.B.Yzb5.resQ ϖ ^ m := by
  intro F _ _ _ _ ϖ hϖ W _ _ ι _ b ψ a u hdet W0 hW0 hint
  classical
  let f := (ValuativeRel.valuation F).integer.subtype
  let M : Matrix ι ι (ValuativeRel.valuation F).integer := fun i j => ⟨b.repr (ψ (b j)) i, hint i j⟩
  have hMdet : f M.det = LinearMap.det ψ := by
    rw [RingHom.map_det, ← LinearMap.det_toMatrix b ψ]
    congr 1
    ext i j
    simp [f, M, LinearMap.toMatrix_apply]
    rfl
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hu0 : ((u : (ValuativeRel.valuation F).integer) : F) ≠ 0 :=
    fun h => u.ne_zero (Subtype.ext h)
  have hM0 : M.det ≠ 0 := by
    intro h
    rw [h, map_zero, hdet] at hMdet
    exact mul_ne_zero (zpow_ne_zero a hϖ0) hu0 hMdet.symm
  obtain ⟨m, v, hv, hcard⟩ := UpperTheory.Reformulated.B.Yzb5.card_coker hϖ M hM0
  have hint' := Valuation.integer.integers (ValuativeRel.valuation F)
  have hlt : ValuativeRel.valuation F (ϖ : F) < 1 :=
    Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hϖ.not_isUnit
  have hpos : 0 < ValuativeRel.valuation F (ϖ : F) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff _).mpr hϖ0
  have ham : a = (m : ℤ) := by
    have h1 : (ϖ : F) ^ a * ((u : (ValuativeRel.valuation F).integer) : F)
        = ((v : (ValuativeRel.valuation F).integer) : F) * (ϖ : F) ^ (m : ℤ) := by
      rw [← hdet, ← hMdet, hv]
      simp [f]
    have h2 := congrArg (ValuativeRel.valuation F) h1
    have hu1 : ValuativeRel.valuation F ((u : (ValuativeRel.valuation F).integer) : F) = 1 :=
      hint'.isUnit_iff_valuation_eq_one.mp u.isUnit
    have hv1 : ValuativeRel.valuation F ((v : (ValuativeRel.valuation F).integer) : F) = 1 :=
      hint'.isUnit_iff_valuation_eq_one.mp v.isUnit
    rw [map_mul, map_mul, map_zpow₀, map_zpow₀, hu1, hv1, mul_one, one_mul] at h2
    exact (zpow_right_strictAnti₀ hpos hlt).injective h2
  refine ⟨m, ham, ?_⟩
  let e : (ι → (ValuativeRel.valuation F).integer) →+ W :=
    (b.equivFun.symm.toLinearMap.toAddMonoidHom).comp (AddMonoidHom.compLeft f.toAddMonoidHom ι)
  have he : ∀ x i, b.repr (e x) i = (x i : F) := by
    intro x i
    have h : b.equivFun (e x) i = (x i : F) := by
      change b.equivFun (b.equivFun.symm fun i => (x i : F)) i = _
      rw [LinearEquiv.apply_symm_apply]
    exact h
  have hinj : Function.Injective e := by
    intro x y hxy
    ext i
    rw [← he x i, ← he y i, hxy]
  have hrange : AddSubgroup.map e ⊤ = W0 := by
    ext w
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, hW0]
    constructor
    · rintro ⟨x, rfl⟩ i
      rw [he]
      exact (x i).2
    · intro h
      refine ⟨fun i => ⟨b.repr w i, h i⟩, ?_⟩
      apply b.repr.injective
      ext i
      rw [he]
  have hcomm : ∀ x, e (M.mulVecLin x) = ψ (e x) := by
    intro x
    apply b.repr.injective
    ext i
    rw [he]
    have hx := b.sum_repr (e x)
    simp only [he] at hx
    have hmv : ((M.mulVecLin x) i : F) = f (∑ j, M i j * x j) := rfl
    rw [hmv, map_sum, ← hx, map_sum, map_sum, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
    rfl
  have hmap : AddSubgroup.map ψ.toAddMonoidHom W0
      = AddSubgroup.map e (LinearMap.range M.mulVecLin).toAddSubgroup := by
    ext w
    rw [← hrange]
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_top, true_and, Submodule.mem_toAddSubgroup,
      LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, hcomm x⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, (hcomm x).symm⟩
  rw [hmap, ← hrange, AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
    AddSubgroup.relIndex_top_right]
  exact hcard
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardinalityOfBand
section
noncomputable def UpperTheory.Reformulated.B.CardinalityOfBand.band :
    (m : Nat) → Nat → Nat → Fin m → Bool :=
    fun (m a b : Nat) (i : Fin m) ↦
      @Decidable.decide (And (@LE.le Nat instLENat a (@Fin.val m i)) (@LT.lt Nat instLTNat (@Fin.val m i) b))
        (@instDecidableAnd (@LE.le Nat instLENat a (@Fin.val m i)) (@LT.lt Nat instLTNat (@Fin.val m i) b)
          (a.decLe (@Fin.val m i)) ((@Fin.val m i).decLt b))

theorem UpperTheory.Reformulated.B.CardinalityOfBand.card_band :
    ∀ (m a b : Nat),
      @LE.le Nat instLENat b m →
        @Eq Nat (@Finset.card (Fin m) {i : Fin m | @Eq Bool (UpperTheory.Reformulated.B.CardinalityOfBand.band m a b i) Bool.true})
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) b a) := by
  intro m a b hb
  rw [← Nat.card_Ico a b, ← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_Ico, UpperTheory.Reformulated.B.CardinalityOfBand.band, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact hi
  · intro hx
    exact ⟨⟨x, lt_of_lt_of_le hx.2 hb⟩, hx, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CasimirElement
section
noncomputable def UpperTheory.Reformulated.B.CasimirElement.casC :
    {n : ℕ} → (Fin n → ℂ) → ℂ :=
    fun {n : ℕ} (τ : Fin n → ℂ) ↦
      ∑ a : Fin n, τ a ^ (2 : ℕ) + ∑ a : Fin n, ∑ b : Fin n, if a < b then τ a - τ b else (0 : ℂ)

namespace YgaHelp

private lemma inner_left {n : ℕ} (σ : Fin n → ℂ) (a : Fin n) :
    (∑ b : Fin n, if a < b then σ a else (0 : ℂ)) = σ a * (((n : ℂ) - 1) - ((a : ℕ) : ℂ)) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul]
  have h : (a : ℕ) ≤ n - 1 := by omega
  have h1 : 1 ≤ n := by omega
  rw [Nat.cast_sub h, Nat.cast_sub h1]
  push_cast; ring

private lemma inner_right {n : ℕ} (σ : Fin n → ℂ) (b : Fin n) :
    (∑ a : Fin n, if a < b then σ b else (0 : ℂ)) = σ b * ((b : ℕ) : ℂ) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul]
  ring

end YgaHelp

theorem UpperTheory.Reformulated.B.CasimirElement.main :
    ∀ {n : ℕ} (σ : Fin n → ℂ),
      UpperTheory.Reformulated.B.CasimirElement.casC σ =
        ∑ a : Fin n, σ a ^ (2 : ℕ) + ∑ a : Fin n, σ a * ((↑n : ℂ) - (1 : ℂ) - (2 : ℂ) * (↑(↑a : ℕ) : ℂ)) := by
  intro n σ
  unfold UpperTheory.Reformulated.B.CasimirElement.casC
  congr 1
  have hsplit : ∀ a b : Fin n, (if a < b then σ a - σ b else (0 : ℂ)) =
      (if a < b then σ a else 0) - (if a < b then σ b else 0) := by
    intro a b; split_ifs <;> simp
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => if a < b then σ b else (0 : ℂ))]
  simp_rw [YgaHelp.inner_left, YgaHelp.inner_right]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro a _
  ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CayleyForm
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj14.Mat :
    ℕ → ℕ → Type :=
    fun (k r : ℕ) ↦ Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ

noncomputable def UpperTheory.Reformulated.B.Qj14.Hpk :
    (k r : ℕ) → Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ :=
    fun (k r : ℕ) (i j : Fin ((2 : ℕ) * r + k + (1 : ℕ))) ↦
      if (↑i : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
      else
        if (↑j : ℕ) < r ∧ (↑i : ℕ) + (↑j : ℕ) = (2 : ℕ) * r + k then (1 : ℂ)
        else if r ≤ (↑i : ℕ) ∧ (↑i : ℕ) ≤ r + k ∧ i = j then if (↑i : ℕ) = r + k then (-1 : ℂ) else (1 : ℂ) else (0 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qj14.inLie :
    (k r : ℕ) → UpperTheory.Reformulated.B.Qj14.Mat k r → Prop :=
    fun (k r : ℕ) (X : UpperTheory.Reformulated.B.Qj14.Mat k r) ↦
      Matrix.conjTranspose X * UpperTheory.Reformulated.B.Qj14.Hpk k r + UpperTheory.Reformulated.B.Qj14.Hpk k r * X =
        (0 : Matrix (Fin ((2 : ℕ) * r + k + (1 : ℕ))) (Fin ((2 : ℕ) * r + k + (1 : ℕ))) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qj14.UH.{u_1} :
    {ι : Type u_1} → [Fintype ι] → [DecidableEq ι] → Matrix ι ι ℂ → Set (Matrix ι ι ℂ) :=
    fun {ι : Type u_1} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) ↦ {g : Matrix ι ι ℂ | g.conjTranspose * H * g = H}

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj14.GV :
    (k r : ℕ) → Set (UpperTheory.Reformulated.B.Qj14.Mat k r) :=
    fun (k r : ℕ) ↦ UpperTheory.Reformulated.B.Qj14.UH (UpperTheory.Reformulated.B.Qj14.Hpk k r)

noncomputable def UpperTheory.Reformulated.B.Qj14.kap :
    {k r : ℕ} → UpperTheory.Reformulated.B.Qj14.Mat k r → UpperTheory.Reformulated.B.Qj14.Mat k r :=
    fun {k r : ℕ} (Y : UpperTheory.Reformulated.B.Qj14.Mat k r) ↦
      ((1 : UpperTheory.Reformulated.B.Qj14.Mat k r) + Y) * ((1 : UpperTheory.Reformulated.B.Qj14.Mat k r) - Y)⁻¹

private theorem UpperTheory.Reformulated.B.Qj14.cayley_form {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H Y : Matrix ι ι ℂ) (h : Y.conjTranspose * H + H * Y = 0) (hu : IsUnit (1 - Y).det) :
    ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹) = H := by
  have h' : Y.conjTranspose * H = -(H * Y) := eq_neg_of_add_eq_zero_left h
  have key : (1 + Y).conjTranspose * H * (1 + Y) = (1 - Y).conjTranspose * H * (1 - Y) := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      add_mul, sub_mul, h']
    noncomm_ring
  have hinv : (1 - Y) * (1 - Y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  calc ((1 + Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 + Y) * (1 - Y)⁻¹)
      = ((1 - Y)⁻¹).conjTranspose * ((1 + Y).conjTranspose * H * (1 + Y)) * (1 - Y)⁻¹ := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = ((1 - Y) * (1 - Y)⁻¹).conjTranspose * H * ((1 - Y) * (1 - Y)⁻¹) := by
        rw [key, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = H := by
        rw [hinv, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

theorem UpperTheory.Reformulated.B.Qj14.kap_mem :
    ∀ {k r : ℕ} {Y : UpperTheory.Reformulated.B.Qj14.Mat k r},
      UpperTheory.Reformulated.B.Qj14.inLie k r Y →
        IsUnit (Matrix.det ((1 : UpperTheory.Reformulated.B.Qj14.Mat k r) - Y)) → UpperTheory.Reformulated.B.Qj14.kap Y ∈ UpperTheory.Reformulated.B.Qj14.GV k r := by
  intro k r Y h hu
  exact UpperTheory.Reformulated.B.Qj14.cayley_form (UpperTheory.Reformulated.B.Qj14.Hpk k r) Y h hu
end

