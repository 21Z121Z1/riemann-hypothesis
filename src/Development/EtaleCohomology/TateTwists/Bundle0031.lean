import Development.EtaleCohomology.TateTwists.Bundle0030
import Development.EtaleCohomology.TateTwists.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008

-- bundled from Development.EtaleCohomology.TateTwists.AlgPowPfR
section
noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AlgPowPf

theorem root_dom {K : Type} [CommRing K] [IsDomain K] (q : ℕ) [NeZero q] (hq : (q : K) ≠ 0) (z : K)
    (hz : aeval z (cyclotomic q ℤ) = 0) : IsPrimitiveRoot z q := by
  have : NeZero (q : K) := ⟨hq⟩
  have h : (cyclotomic q K).IsRoot z := by
    rw [IsRoot, ← map_cyclotomic_int, eval_map]
    simpa [aeval_def] using hz
  exact (isRoot_cyclotomic_iff).1 h

theorem eq_pow_dom {K : Type} [CommRing K] [IsDomain K] (q : ℕ) [NeZero q] (z x : K)
    (hz : IsPrimitiveRoot z q) (hx : IsPrimitiveRoot x q) : ∃ b : (ZMod q)ˣ, x = z ^ (b : ZMod q).val := by
  obtain ⟨i, hi, hzi⟩ := hz.eq_pow_of_pow_eq_one hx.pow_eq_one
  have hc : i.Coprime q := (hz.pow_iff_coprime (Nat.pos_of_ne_zero (NeZero.ne q)) i).1 (hzi ▸ hx)
  refine ⟨ZMod.unitOfCoprime i hc, ?_⟩
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi, hzi]

theorem pow_ne_dom {K : Type} [CommRing K] (q : ℕ) [NeZero q] (z : K)
    (hz : IsPrimitiveRoot z q) (a b : (ZMod q)ˣ) (h : a ≠ b) :
    z ^ (a : ZMod q).val ≠ z ^ (b : ZMod q).val := by
  intro e
  apply h
  exact Units.ext (ZMod.val_injective q (hz.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e))

theorem pow_q {A : Type} [CommRing A] (q : ℕ) (z : A) (hz : aeval z (cyclotomic q ℤ) = 0) : z ^ q = 1 := by
  obtain ⟨p, hp⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have := congrArg (aeval z) hp
  simp [hz] at this
  exact sub_eq_zero.1 this

theorem self_sq {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (x y : A)
    (hx : x ^ q = 1) (hy : y ^ q = 1) : ∃ w : A, x - y = (x - y) ^ 2 * w := by
  set d := x - y
  set u := ∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)
  have hdu : u * d = 0 := by
    have := geom_sum₂_mul x y q
    rw [hx, hy, sub_self] at this
    exact this
  have hyu : IsUnit y := isUnit_iff_exists_inv.2 ⟨y ^ (q - 1), by rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne q)), hy]⟩
  set c : A := (q : A) * y ^ (q - 1)
  have hc : IsUnit c := hq.mul (hyu.pow _)
  have hmem : u - c ∈ Ideal.span {d} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hxy : Ideal.Quotient.mk (Ideal.span {d}) x = Ideal.Quotient.mk (Ideal.span {d}) y := by
      rw [Ideal.Quotient.eq]; exact Ideal.subset_span rfl
    simp only [u, c, map_sub, map_sum, map_mul, map_pow, map_natCast, hxy]
    rw [geom_sum₂_self, sub_self]
  obtain ⟨w0, hw0⟩ := Ideal.mem_span_singleton'.1 hmem
  obtain ⟨cu, hcu⟩ := hc
  refine ⟨-(w0 * ↑cu⁻¹), ?_⟩
  have hdc : d * c = -(d ^ 2 * w0) := by
    have : c = u - w0 * d := by rw [hw0]; ring
    rw [this]; linear_combination hdu
  calc d = d * c * ↑cu⁻¹ := by rw [← hcu, mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [hdc]; ring

theorem self_pow {A : Type} [CommRing A] (d w : A) (h : d = d ^ 2 * w) (k : ℕ) : d = d ^ (k + 1) * w ^ k := by
  induction k with
  | zero => simp
  | succ k ih => calc d = d ^ (k + 1) * w ^ k := ih
      _ = d ^ k * d * w ^ k := by ring
      _ = d ^ k * (d ^ 2 * w) * w ^ k := by rw [← h]
      _ = _ := by ring

theorem AlgPow_of : LateralTheory.EtaleFoundations.TwSecLocPf.AlgPow := by
  classical
  intro q _ A _ ζ ξ
  obtain ⟨hqA, hζ⟩ := ζ.2
  obtain ⟨-, hξ⟩ := ξ.2
  let f : (ZMod q)ˣ → A := fun a => ∏ b ∈ Finset.univ.erase a, (ξ.1 - ζ.1 ^ (b : ZMod q).val)

  have hdom : ∀ p : Ideal A, p.IsPrime → IsPrimitiveRoot (Ideal.Quotient.mk p ζ.1) q ∧
      IsPrimitiveRoot (Ideal.Quotient.mk p ξ.1) q := by
    intro p hp
    have hq : ((q : ℕ) : A ⧸ p) ≠ 0 := by
      have := hqA.map (Ideal.Quotient.mk p)
      rw [map_natCast] at this
      exact this.ne_zero
    have hm : ∀ z : A, aeval z (cyclotomic q ℤ) = 0 → aeval (Ideal.Quotient.mk p z) (cyclotomic q ℤ) = 0 := by
      intro z hz
      have := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℤ p) z (cyclotomic q ℤ)
      rw [hz, map_zero] at this
      simpa using this
    exact ⟨root_dom q hq _ (hm _ hζ), root_dom q hq _ (hm _ hξ)⟩
  refine ⟨Set.range f, ?_, ?_⟩
  · by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨h1, h2⟩ := hdom m hm.isPrime
    obtain ⟨b0, hb0⟩ := eq_pow_dom q _ _ h1 h2
    have hin : f b0 ∈ m := hsm (Ideal.subset_span ⟨b0, rfl⟩)
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hin
    simp only [f, map_prod, map_sub, map_pow, hb0] at hin
    rw [Finset.prod_eq_zero_iff] at hin
    obtain ⟨b, hb, e⟩ := hin
    exact pow_ne_dom q _ h1 b0 b (Finset.ne_of_mem_erase hb).symm (sub_eq_zero.1 e)
  · rintro _ ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    have hnil : IsNilpotent (f a * (ξ.1 - ζ.1 ^ (a : ZMod q).val)) := by
      rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
      intro p hp
      have hp : p.IsPrime := hp
      obtain ⟨h1, h2⟩ := hdom p hp
      obtain ⟨b0, hb0⟩ := eq_pow_dom q _ _ h1 h2
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [f, map_mul, map_prod, map_sub, map_pow, hb0]
      by_cases hab : b0 = a
      · subst hab; simp
      · apply mul_eq_zero_of_left
        exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hab, Finset.mem_univ _⟩) (sub_self _)
    obtain ⟨n, hn⟩ := hnil
    obtain ⟨w, hw⟩ := self_sq q hqA ξ.1 (ζ.1 ^ (a : ZMod q).val) (pow_q q _ hξ)
      (by rw [← pow_mul, mul_comm, pow_mul, pow_q q _ hζ, one_pow])
    refine ⟨n, ?_⟩
    rw [self_pow _ w hw n, pow_succ, mul_pow] at *
    calc f a ^ n * ((ξ.1 - ζ.1 ^ (a : ZMod q).val) ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) * w ^ n)
        = (f a ^ n * (ξ.1 - ζ.1 ^ (a : ZMod q).val) ^ n) * ((ξ.1 - ζ.1 ^ (a : ZMod q).val) * w ^ n) := by ring
      _ = 0 := by rw [hn, zero_mul]

end LateralTheory.EtaleFoundations.AlgPowPf
end
end

-- bundled from Development.EtaleCohomology.TateTwists.ColumnOf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleFoundations.columnPf

theorem vanish_fg {S : Type*} [CommRing S] {N G Pv : Type*} [AddCommGroup N] [Module S N] [AddCommGroup G] [Module S G]
    [AddCommGroup Pv] [Module S Pv] (φ : Pv →ₗ[S] N) {k : ℕ} (b : Fin k → G) (q : Fin k → Pv)
    (h : ∑ j, φ (q j) ⊗ₜ[S] b j = 0) :
    ∃ (gs : Finset N) (l : ℕ) (a : Fin k → Fin l → S) (c : gs → Fin l → S) (y : Fin l → G),
      (∀ j, b j = ∑ κ, a j κ • y κ) ∧ (∀ g, 0 = ∑ κ, c g κ • y κ) ∧
      ∀ κ, ∑ j, a j κ • φ (q j) + ∑ g, c g κ • (g : N) = 0 := by
  classical
  set Q0 : Submodule S N := Submodule.span S (Set.range fun j => φ (q j))
  have hQ0 : Q0.FG := Submodule.fg_span (Set.finite_range _)
  let t : Q0 ⊗[S] G := ∑ j, (⟨φ (q j), Submodule.subset_span ⟨j, rfl⟩⟩ : Q0) ⊗ₜ b j
  have ht : LinearMap.rTensor G Q0.subtype t = 0 := by simpa [t, map_sum] using h
  obtain ⟨Q, hQ0Q, hQ, ht'⟩ := TensorProduct.eq_zero_of_fg_of_subtype_eq_zero hQ0 ht
  obtain ⟨gs, hgs⟩ := hQ
  have memg : ∀ g : gs, (g : N) ∈ Q := fun g => hgs ▸ Submodule.subset_span g.2
  let m' : Fin k ⊕ gs → Q := Sum.elim (fun j => Submodule.inclusion hQ0Q ⟨φ (q j), Submodule.subset_span ⟨j, rfl⟩⟩)
    fun g => ⟨g, memg g⟩
  let n' : Fin k ⊕ gs → G := Sum.elim b fun _ => 0
  have hspan : Submodule.span S (Set.range m') = ⊤ := by
    apply Submodule.map_injective_of_injective Q.injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
    refine le_antisymm (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact (m' i).2
    · intro z hz
      rw [← hgs] at hz
      refine (Submodule.span_le.2 fun g hg => Submodule.subset_span ?_) hz
      exact ⟨m' (Sum.inr ⟨g, hg⟩), ⟨Sum.inr ⟨g, hg⟩, rfl⟩, rfl⟩
  have hsum : ∑ i, m' i ⊗ₜ[S] n' i = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [m', n', Sum.elim_inl, Sum.elim_inr, TensorProduct.tmul_zero, Finset.sum_const_zero, add_zero]
    simpa [t, map_sum] using ht'
  obtain ⟨l, a, y, hn, hm⟩ := TensorProduct.vanishesTrivially_of_sum_tmul_eq_zero S hspan hsum
  refine ⟨gs, l, fun j => a (Sum.inl j), fun g => a (Sum.inr g), y, fun j => hn (Sum.inl j), fun g => hn (Sum.inr g),
    fun κ => ?_⟩
  have := congrArg Subtype.val (hm κ)
  rw [Fintype.sum_sum_type] at this
  simpa [m'] using this

end LateralTheory.EtaleFoundations.columnPf

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.columnPf.kerLoc_of : kerLoc := by
  classical
  intro R _ M P φ hsurj hker G V u hu
  obtain ⟨k, b, q, rfl⟩ := TensorProduct.exists_sum_tmul_eq u
  have h : ∑ j, (φ.app (op V)).hom (q j) ⊗ₜ[ULift.{1} R] b j = 0 := by
    have := congrArg (TensorProduct.comm _ _ _) hu
    simpa [map_sum] using this
  obtain ⟨gs, l, a, c, y, hb, hc, hrel⟩ := vanish_fg (φ.app (op V)).hom b q h
  refine loc_bind (loc_finset (Finset.univ : Finset gs) fun i _ => hsurj V (i : Sec M V)) ?_
  intro W hW hl
  choose pt hpt using hl
  have nφ : ∀ x, (φ.app (op W)).hom ((P.map hW.op).hom x) = (M.obj.map hW.op).hom ((φ.app (op V)).hom x) := fun x => by
    rw [← ModuleCat.comp_apply, φ.naturality, ModuleCat.comp_apply]
  let e : Fin l → P.obj (op W) := fun κ =>
    ∑ j, a j κ • (P.map hW.op).hom (q j) + ∑ g, c g κ • pt g (Finset.mem_univ g)
  have he : ∀ κ, (φ.app (op W)).hom (e κ) = 0 := fun κ => by
    have := congrArg (M.obj.map hW.op).hom (hrel κ)
    simp only [map_add, map_sum, map_smul, map_zero] at this
    simp only [e, map_add, map_sum, map_smul, nφ]
    rw [← this]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hpt g (Finset.mem_univ g)]
  have hu' : TensorProduct.map (G.obj.map hW.op).hom (P.map hW.op).hom (∑ j, b j ⊗ₜ[ULift.{1} R] q j) =
      ∑ κ, (G.obj.map hW.op).hom (y κ) ⊗ₜ e κ := by
    have hz : ∀ g : gs, ∑ κ, (G.obj.map hW.op).hom (y κ) ⊗ₜ[ULift.{1} R] (c g κ • pt g (Finset.mem_univ g)) = 0 :=
      fun g => by
        have := congrArg (fun z => (G.obj.map hW.op).hom z ⊗ₜ[ULift.{1} R] pt g (Finset.mem_univ g)) (hc g)
        simp only [map_zero, TensorProduct.zero_tmul, map_sum, map_smul, TensorProduct.sum_tmul] at this
        rw [this]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp only [e, TensorProduct.tmul_add, TensorProduct.tmul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := Finset.univ) (t := (Finset.univ : Finset gs)), Finset.sum_congr rfl fun g _ => hz g,
      Finset.sum_const_zero, add_zero, map_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.map_tmul, hb j, map_sum, TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  refine loc_mono (loc_finset (Finset.univ : Finset (Fin l)) fun κ _ => hker W (e κ) (he κ)) ?_
  intro W' k' hk'
  have hcomp : TensorProduct.map (G.obj.map (k' ≫ hW).op).hom (P.map (k' ≫ hW).op).hom
      (∑ j, b j ⊗ₜ[ULift.{1} R] q j) = TensorProduct.map (G.obj.map k'.op).hom (P.map k'.op).hom
      (TensorProduct.map (G.obj.map hW.op).hom (P.map hW.op).hom (∑ j, b j ⊗ₜ[ULift.{1} R] q j)) := by
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
    simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp]
  rw [hcomp, hu', map_sum]
  refine Finset.sum_eq_zero fun κ _ => ?_
  rw [TensorProduct.map_tmul, hk' κ (Finset.mem_univ κ), TensorProduct.tmul_zero]

open LateralTheory.EtaleFoundations.columnPf in
theorem LateralTheory.EtaleFoundations.acyc.column_of : LateralTheory.EtaleFoundations.acyc.column := column_of' kerLoc_of
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizOfSucc
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem awleib_ext_pf : EtaleSimplicialCochainEqOfEvaluationsAgree := by
  intro R _ E K k γ γ' H
  apply Cochain.ext
  intro p q hpq
  by_cases hp : ∃ N : ℕ, -(N : ℤ) = p
  · obtain ⟨N, rfl⟩ := hp
    rw [← cancel_epi (chainsXIso R E N).inv]
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ (Sheaf.cond _)
    ext U : 2
    apply ModuleCat.free_hom_ext
    intro x
    exact H N q hpq U.unop x.down
  · have hz : IsZero (((chains R).obj E).X p) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => hp ⟨i, by
        have e : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
        omega⟩)
    exact hz.eq_of_src _ _

theorem etale_cup_alexanderWhitney_leibniz_of_succ (hs : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree) : EtaleAlexanderWhitneyCupLeibnizRule :=
  etale_cup_alexanderWhitney_leibniz_of_ext_and_succ awleib_ext_pf hs

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistGeneratorRestrictionAndRootChangeH
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace LateralTheory.EtaleFoundations.GenIsoSurjRootPf

theorem ofRings_sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
    {V U : Scheme.{0}} (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op
  have h2 := congrArg (fun f => f.hom x) h
  simp only [ModuleCat.hom_comp] at h2
  exact h2.symm

theorem res_twGen (q : ℕ) (j : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen j ζ) = twGen j (ζ.map g.appTop.hom) := by
  refine (ofRings_sec_res (twF q j) g _).trans ?_
  congr 1
  change Submodule.mapQ _ _ _ (twRel_le q j (Scheme.Hom.appTop g).hom) (Submodule.Quotient.mk _) = _
  rw [Submodule.mapQ_apply]
  simp [Finsupp.mapDomain_single]

theorem twGen_pow (q : ℕ) [NeZero q] (j : ℤ) {V : Scheme.{0}} (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen j ξ = ((a ^ j : (ZMod q)ˣ) : ZMod q).val • twGen j ζ := by
  have hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q j).obj Γ(V, ⊤)) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ j : (ZMod q)ˣ) : ZMod q))) := by
    rw [Submodule.Quotient.eq]
    exact Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩
  have hs : (Finsupp.single ζ (ULift.up ((a ^ j : (ZMod q)ˣ) : ZMod q)) : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) =
      ((a ^ j : (ZMod q)ˣ) : ZMod q).val • Finsupp.single ζ 1 := by
    rw [Finsupp.smul_single]
    congr 1
    apply ULift.ext
    simp only [nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_zmod_val _).symm
  have key : ∀ (n : ℕ) (x y : (twF q j).obj Γ(V, ⊤)), x = n • y →
      ofRings.sec (twF q j) V x = n • ofRings.sec (twF q j) V y := by
    rintro n x y rfl
    exact map_nsmul _ _ _
  refine key _ _ _ ?_
  show (Submodule.Quotient.mk (Finsupp.single ξ 1) : (_ ⧸ twRel q j Γ(V, ⊤))) =
    _ • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (_ ⧸ twRel q j Γ(V, ⊤)))
  rw [hrel, hs]
  exact map_nsmul (Submodule.mkQ _) _ _

end LateralTheory.EtaleFoundations.GenIsoSurjRootPf

def LateralTheory.EtaleFoundations.EtalePrimitiveRootsLocallyPowersOfEachOther : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)),
    Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val

open LateralTheory.EtaleFoundations.GenIsoSurjRootPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_root_change_of_local_primitive_root_powers
    (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsLocallyPowersOfEachOther) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange := by
  intro q _ j
  refine ⟨fun V U g ζ => res_twGen q j g ζ, fun U ζ ξ => ?_⟩
  obtain ⟨S, hS, h⟩ := hp q U ζ ξ
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨a, ha⟩ := h V g hg
  exact ⟨_, (res_twGen q j g ξ).trans (twGen_pow q j (ζ.map g.appTop.hom) (ξ.map g.appTop.hom) a ha)⟩

namespace LateralTheory.EtaleFoundations.GenIsoSurjRootPf

theorem alg_prim_pow {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (ζ ξ : A)
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic q ℤ) = 0)
    {K : Type} [Field K] (f : A →+* K) : ∃ (a : (ZMod q)ˣ) (s : A), f s ≠ 0 ∧ s * (ξ - ζ ^ (a : ZMod q).val) = 0 := by
  have hqK : (q : K) ≠ 0 := by
    have := hq.map f; simpa using this.ne_zero
  have : NeZero (q : K) := ⟨hqK⟩
  have root : ∀ x : A, Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0 → IsPrimitiveRoot (f x) q := by
    intro x hx
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def,
      Polynomial.eval_map]
    have h1 := congrArg f hx
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, map_zero] at h1
    rwa [show f.comp (algebraMap ℤ A) = Int.castRingHom K from RingHom.ext_int _ _] at h1
  have pq : ∀ x : A, Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0 → x ^ q = 1 := by
    intro x hx
    obtain ⟨r, hr⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
    have := congrArg (Polynomial.aeval x) hr
    rw [map_mul, hx, zero_mul] at this
    simpa [sub_eq_zero] using this
  obtain ⟨i, hi, he⟩ := (root ζ hζ).eq_pow_of_pow_eq_one (root ξ hξ).pow_eq_one
  have hcop : i.Coprime q := by
    have h2 := root ξ hξ
    rw [← he] at h2
    exact ((root ζ hζ).pow_iff_coprime (NeZero.pos q) i).1 h2
  refine ⟨ZMod.unitOfCoprime i hcop, ∑ m ∈ Finset.range q, ξ ^ m * (ζ ^ i) ^ (q - 1 - m), ?_, ?_⟩
  · have hv : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    intro h0
    rw [map_sum] at h0
    have : ∀ m ∈ Finset.range q, f (ξ ^ m * (ζ ^ i) ^ (q - 1 - m)) = (f ζ ^ i) ^ (q - 1) := by
      intro m hm
      rw [map_mul, map_pow, map_pow, map_pow, ← he, ← pow_add]
      congr 1
      have := Finset.mem_range.1 hm; omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact hqK h
    · exact (root ζ hζ).ne_zero (NeZero.ne q) (eq_zero_of_pow_eq_zero (eq_zero_of_pow_eq_zero h))
  · have hv : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    rw [hv, geom_sum₂_mul]
    rw [pq ξ hξ, ← pow_mul, mul_comm i q, pow_mul, pq ζ hζ, one_pow, sub_self]

theorem unit_res {U : Scheme.{0}} (s : Γ(U, ⊤)) : ∀ (O : U.Opens) (h : O ≤ ⊤), O = U.basicOpen s →
    IsUnit (U.presheaf.map (homOfLE h).op s) := by
  rintro O h rfl
  exact RingedSpace.isUnit_res_basicOpen U.toRingedSpace s

theorem loc_of_points {U : Scheme.{0}} (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g))
    (h : ∀ x : U, ∃ s : Γ(U, ⊤), x ∈ U.basicOpen s ∧ P _ (U.basicOpen s).ι) : Loc U P := by
  choose s hs hPs using h
  let S : Sieve U := { arrows := fun V g => P V g, downward_closed := fun hg k => hP _ _ _ k hg }
  refine ⟨S, Scheme.zariskiTopology_le_etaleTopology _ ?_, fun V g hg => hg⟩
  rw [Scheme.mem_grothendieckTopology_iff]
  refine ⟨U.openCoverOfIsOpenCover (fun x => U.basicOpen (s x)) ?_, ?_⟩
  · exact eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hs x⟩
  · rintro V g ⟨x⟩
    exact hPs x

theorem prim_root_loc : LateralTheory.EtaleFoundations.EtalePrimitiveRootsLocallyPowersOfEachOther := by
  intro q _ U ζ ξ
  have hq : IsUnit (q : Γ(U, ⊤)) := ζ.2.1
  refine loc_of_points _ ?_ fun x => ?_
  · rintro V W g k ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, ha, map_pow]
  · obtain ⟨a, s, hs, hd⟩ := alg_prim_pow q hq ζ.1 ξ.1 ζ.2.2 ξ.2.2 (U.Γevaluation x).hom
    refine ⟨s, (U.evaluation_ne_zero_iff_mem_basicOpen x (show x ∈ (⊤ : U.Opens) from trivial) s).1 hs, a, ?_⟩
    have hu : IsUnit ((U.basicOpen s).ι.appTop.hom s) := unit_res s _ _ (by simp)
    have h0 := congrArg (U.basicOpen s).ι.appTop.hom hd
    rw [map_mul, map_zero, map_sub, map_pow] at h0
    exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)

end LateralTheory.EtaleFoundations.GenIsoSurjRootPf

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_restriction_and_root_change_holds : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange :=
  LateralTheory.EtaleFoundations.etale_tate_twist_generator_root_change_of_local_primitive_root_powers LateralTheory.EtaleFoundations.GenIsoSurjRootPf.prim_root_loc
end
end

-- bundled from Development.EtaleCohomology.TateTwists.StepPf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section
namespace LateralTheory.EtaleFoundations.StepPf
open LateralTheory.EtaleFoundations.stairPf
variable {R : Type} [CommRing R] {C J T : Cx R}

theorem tens_res_comp {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (w : ℤ) (x : Tens C J U w) :
    Tens.res (k ≫ g) w x = Tens.res k w (Tens.res g w x) := by
  ext p
  rw [res_apply, res_apply, res_apply]
  generalize x p = v
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b => simp [TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ix_eq {w : ℤ} (p : Ix w) (a b : ℤ) (h : p.1.2 = b) (ha : a + b = w) : p = ⟨(a, b), ha⟩ :=
  Subtype.ext (Prod.ext (show p.1.1 = a by have := p.2; omega) h)

theorem lof_back {U : Scheme.{0}} {w : ℤ} (i j : Ix w) (h : i = j) (v : Cmp C J U w i) :
    DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) j ((DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) i v) j) =
      DirectSum.lof (ULift.{1} R) (Ix w) (Cmp C J U w) i v := by
  subst h; rw [lof_same]

theorem ev_zsmul {U : Scheme.{0}} {w : ℤ} (c : ℤ) (f : Tens C J U w) (q : Ix w) : (c • f) q = c • f q := rfl

theorem Dm_comp (U : Scheme.{0}) (n t0 : ℤ) (y : Tens C J U n) :
    (Dm U n (n + 1) rfl y) ⟨(n - t0 + 1, t0), by omega⟩ =
      TensorProduct.map ((C.d (n - t0) (n - t0 + 1)).hom.app (op U)).hom LinearMap.id (y ⟨(n - t0, t0), by omega⟩) +
      (Dm U n (n + 1) rfl (DirectSum.lof (ULift.{1} R) (Ix n) (Cmp C J U n) ⟨(n - t0 + 1, t0 - 1), by omega⟩
        (y ⟨(n - t0 + 1, t0 - 1), by omega⟩))) ⟨(n - t0 + 1, t0), by omega⟩ := by
  classical
  induction y using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb =>
    simp only [map_add, DirectSum.add_apply] at ha hb ⊢
    rw [ha, hb]; abel
  | of p v =>
    rw [← DirectSum.lof_eq_of (ULift.{1} R)]
    by_cases h0 : p.1.2 = t0
    · obtain ⟨⟨a, b⟩, hab⟩ := p
      simp only at h0; subst h0
      obtain rfl : a = n - b := by omega
      rw [Dm_lof, DirectSum.add_apply, ev_zsmul]
      dsimp only
      rw [lof_same, lof_ne _ _ _ _ (by simp), smul_zero, add_zero,
        lof_same, lof_ne _ _ _ _ (by simp; omega), map_zero, map_zero, DirectSum.zero_apply, add_zero]
    by_cases h1 : p.1.2 = t0 - 1
    · rw [lof_back p _ (ix_eq p (n - t0 + 1) (t0 - 1) h1 (by omega)), lof_ne _ _ _ _ h0, map_zero, zero_add]
    · rw [Dm_lof, DirectSum.add_apply, ev_zsmul, lof_ne _ _ _ _ h0, lof_ne _ _ _ _ (by simp; omega),
        smul_zero, add_zero, lof_ne _ _ _ _ h0, lof_ne _ _ _ _ h1, map_zero, map_zero, map_zero,
        DirectSum.zero_apply, add_zero]

theorem Step_of : LateralTheory.EtaleFoundations.stairPf.Step := by
  intro R _ C J T τ hτ hc n t0 V x hx hd
  have hD : τ.lift V (n + 1) (Dm V n (n + 1) rfl x) = 0 := by rw [lift_Dm, hd]
  refine loc_bind (hτ.2 V (n + 1) _ hD) fun W g hW => ?_
  have hc0 : TensorProduct.map ((C.d (n - t0) (n - t0 + 1)).hom.app (op W)).hom LinearMap.id
      (Tens.res g n x ⟨(n - t0, t0), by omega⟩) = 0 := by
    rw [res_apply, nat_tens]
    have h1 := congrArg (fun z => z ⟨(n - t0 + 1, t0), by omega⟩) hW
    simp only at h1
    rw [res_apply, Dm_comp, hx ⟨(n - t0 + 1, t0 - 1), by omega⟩ (by simp)] at h1
    simp only [map_zero, DirectSum.zero_apply, add_zero] at h1
    exact h1
  refine loc_mono (hc W (n - t0) t0 _ hc0) fun W' k hk => ?_
  obtain ⟨y0, hy0⟩ := hk
  refine ⟨Tens.res (k ≫ g) n x - Dm W' (n - 1) n (by ring)
      (DirectSum.lof (ULift.{1} R) (Ix (n - 1)) (Cmp C J W' (n - 1)) ⟨(n - t0 - 1, t0), by omega⟩ y0),
    DirectSum.lof (ULift.{1} R) (Ix (n - 1)) (Cmp C J W' (n - 1)) ⟨(n - t0 - 1, t0), by omega⟩ y0, ?_,
    (sub_add_cancel _ _).symm⟩
  intro p hp
  rw [DirectSum.sub_apply, Dm_lof, DirectSum.add_apply, ev_zsmul]
  rcases lt_or_eq_of_le (show p.1.2 ≤ t0 by omega) with h | h
  · rw [res_apply, hx p h, map_zero, lof_ne _ _ _ _ (by simp; omega), lof_ne _ _ _ _ (by simp; omega),
      smul_zero, add_zero, sub_zero]
  · obtain ⟨⟨a, b⟩, hab⟩ := p
    simp only at h; subst h
    obtain rfl : a = n - b := by omega
    dsimp only
    rw [lof_shift W' n (n - b - 1) (n - b) b (by ring) (by omega) (by omega), lof_same,
      lof_ne _ _ _ _ (by simp), smul_zero, add_zero, hy0, tens_res_comp, res_apply k, sub_self]

end LateralTheory.EtaleFoundations.StepPf
end
end

