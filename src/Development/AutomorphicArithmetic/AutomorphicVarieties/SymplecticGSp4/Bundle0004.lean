import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0003

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PrimeTo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem pt_modEq_one (l d : ℕ) (hd : d ≠ 0) (h : l.Coprime d) :
    ∀ᶠ n : ℕ in Filter.atTop, l ^ n.factorial ≡ 1 [MOD d] := by
  filter_upwards [Filter.eventually_ge_atTop d.totient] with n hn
  obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.totient_pos.2 (Nat.pos_of_ne_zero hd)) hn
  rw [hk, pow_mul]
  simpa using (Nat.ModEq.pow_totient h).pow k

private theorem pt_dvd (l a : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, l ^ a ∣ l ^ n.factorial := by
  filter_upwards [Filter.eventually_ge_atTop a] with n hn
  exact pow_dvd_pow _ (hn.trans (Nat.self_le_factorial n))

private theorem pt_const (l : ℕ) (hl : l.Prime) {H : Type} [Group H] [Finite H] (x : H) :
    ∃ y, ∀ᶠ n : ℕ in Filter.atTop, x ^ l ^ n.factorial = y := by
  have h0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, d, hnd, hod⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.one_lt.ne'
  have hcop : l.Coprime d := (Nat.Prime.coprime_iff_not_dvd hl).2 hnd
  have hd : d ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using hod)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((pt_modEq_one l d hd hcop).and (pt_dvd l a))
  refine ⟨x ^ l ^ N.factorial, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [pow_eq_pow_iff_modEq, hod, ← Nat.modEq_and_modEq_iff_modEq_mul (Nat.Coprime.pow_left a hcop)]
  obtain ⟨h1, h2⟩ := hN n hn
  obtain ⟨h1', h2'⟩ := hN N le_rfl
  exact ⟨(Nat.modEq_zero_iff_dvd.2 h2).trans (Nat.modEq_zero_iff_dvd.2 h2').symm, h1.trans h1'.symm⟩

private theorem pt_exists (l : ℕ) (hl : l.Prime) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (g : Γ) :
    ∃ g', Filter.Tendsto (fun n : ℕ => g ^ l ^ n.factorial) Filter.atTop (nhds g') := by
  obtain ⟨g', -, hg'⟩ : ∃ g' ∈ Set.univ, ClusterPt g' (Filter.map (fun n : ℕ => g ^ l ^ n.factorial) Filter.atTop) :=
    isCompact_univ.exists_clusterPt (Filter.le_principal_iff.2 Filter.univ_mem)
  refine ⟨g', ?_⟩
  rw [(nhds_basis_opens g').tendsto_right_iff]
  rintro V ⟨hgV, hVo⟩
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (hVo.preimage (continuous_mul_left g')) (by simpa using hgV)
  haveI : H.toSubgroup.Normal := H.isNormal'
  haveI : Finite (Γ ⧸ H.toSubgroup) := H.toSubgroup.quotient_finite_of_isOpen H.isOpen'
  obtain ⟨y, hy⟩ := pt_const l hl (QuotientGroup.mk (s := H.toSubgroup) g)
  have hnh : ∀ᶠ z in nhds g', g'⁻¹ * z ∈ H.toSubgroup := by
    have hc : Continuous (fun z : Γ => g'⁻¹ * z) := continuous_const.mul continuous_id
    refine hc.continuousAt.preimage_mem_nhds (H.isOpen'.mem_nhds ?_)
    show g'⁻¹ * g' ∈ H.toSubgroup
    rw [inv_mul_cancel]
    exact H.toSubgroup.one_mem
  have hfr := hg'.frequently hnh
  rw [Filter.frequently_map] at hfr
  obtain ⟨n, hn1, hn2⟩ := (hfr.and_eventually hy).exists
  have hy' : y = QuotientGroup.mk g' := by
    rw [← hn2, ← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq]
    exact hn1
  filter_upwards [hy] with m hm
  rw [hy', ← QuotientGroup.mk_pow, QuotientGroup.eq] at hm
  have := hH (H.toSubgroup.inv_mem hm)
  simpa using this

private theorem pt_step {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (I J : Ideal R) (hJ : J ≤ I) (l : ℕ)
    (hl : (l : R) ∈ I) (X : Matrix ι ι R) (hX : ∀ a b, (X - 1) a b ∈ J) : ∀ a b, (X ^ l - 1) a b ∈ I * J := by
  classical
  have hXi : ∀ i : ℕ, ∀ a b, (X ^ i - 1 : Matrix ι ι R) a b ∈ J := by
    intro i
    have h0 : (Ideal.Quotient.mk J).mapMatrix (X - 1) = 0 := by
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hX a b
    have h1 : (Ideal.Quotient.mk J).mapMatrix X = 1 := by
      rw [map_sub, map_one, sub_eq_zero] at h0
      exact h0
    have h2 : (Ideal.Quotient.mk J).mapMatrix (X ^ i - 1) = 0 := by
      rw [map_sub, map_pow, h1, one_pow, map_one, sub_self]
    intro a b
    have := congrFun (congrFun h2 a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  have hgeom : X ^ l - 1 = (X - 1) * ((l : Matrix ι ι R) + ∑ i ∈ Finset.range l, (X ^ i - 1)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_one, add_sub_cancel, mul_geom_sum]
  intro a b
  rw [hgeom, Matrix.mul_apply]
  refine Ideal.sum_mem _ (fun c _ => ?_)
  have hW : ((l : Matrix ι ι R) + ∑ i ∈ Finset.range l, (X ^ i - 1)) c b ∈ I := by
    rw [Matrix.add_apply, Matrix.sum_apply]
    refine I.add_mem ?_ (I.sum_mem fun i _ => hJ (hXi i c b))
    by_cases hcb : c = b <;> simp [hcb, hl, Matrix.natCast_apply]
  rw [mul_comm ((X - 1) a c)]
  exact Ideal.mul_mem_mul hW (hX a c)

private theorem pt_pow {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (I : Ideal R) (l : ℕ)
    (hl : (l : R) ∈ I) (X : Matrix ι ι R) (hX : ∀ a b, (X - 1) a b ∈ I) (k : ℕ) :
    ∀ a b, (X ^ l ^ k - 1) a b ∈ I ^ (k + 1) := by
  induction k with
  | zero => simpa using hX
  | succ k ih =>
    intro a b
    have h := pt_step I (I ^ (k + 1)) (Ideal.pow_le_self (Nat.succ_ne_zero k)) l hl (X ^ l ^ k) ih a b
    rw [← pow_mul, ← pow_succ] at h
    rw [pow_succ' I (k + 1)]
    exact h

theorem UpperTheory.V.GradeZeroInterpolatingElement.primeTo :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ] (g : Γ), (∃ g', Filter.Tendsto (fun n : ℕ => g ^ l ^ n.factorial) Filter.atTop (nhds g')) ∧ ∀ g', Filter.Tendsto (fun n : ℕ => g ^ l ^ n.factorial) Filter.atTop (nhds g') → ∀ (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (ι : Type) [Fintype ι] [DecidableEq ι] (rbar : Γ →* Matrix ι ι (ResidueField O)) (m : ℕ), l.Coprime m → rbar g ^ m = 1 → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R), rbar g' = rbar g ∧ ρ.hom g' ^ m = 1 := by
  intro l _ Γ _ _ _ _ _ _ g
  have hl : l.Prime := Fact.out
  refine ⟨pt_exists l hl Γ g, ?_⟩
  intro g' hlim O _ _ _ _ ι _ _ rbar m hcop hgm R _ _ _ ρ
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' (Nat.coprime_zero_right l |>.1 hcop)
  have key : ∀ {M : Type} [Monoid M] (x : M) (k : ℕ), x ^ m = 1 → k ≡ 1 [MOD m] → x ^ k = x := by
    intro M _ x k hx hk
    have hk' : k % orderOf x = 1 % orderOf x := Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hx) hk
    rw [← pow_mod_orderOf, hk', pow_mod_orderOf, pow_one]
  have hcong := pt_modEq_one l m hm0 hcop
  have hloc : ∀ N : ℕ, ∀ᶠ n : ℕ in Filter.atTop,
      (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix (ρ.hom (g ^ l ^ n.factorial)) =
      (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix (ρ.hom g') := by
    intro N
    have h1 : ∀ᶠ y in nhds g', ∀ a b, Ideal.Quotient.mk (maximalIdeal R ^ N) (ρ.hom y a b) =
        Ideal.Quotient.mk (maximalIdeal R ^ N) (ρ.hom g' a b) := by
      simp only [Filter.eventually_all]
      intro a b
      exact (ρ.cont a b N).eventually_eq g'
    filter_upwards [hlim.eventually h1] with n hn
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    exact hn a b
  have hres : ∀ x y : R, Ideal.Quotient.mk (maximalIdeal R ^ 1) x = Ideal.Quotient.mk (maximalIdeal R ^ 1) y →
      res O R x = res O R y := by
    intro x y h
    rw [Ideal.Quotient.eq, pow_one] at h
    rw [← sub_eq_zero, ← map_sub]
    exact (res_eq_zero_iff O R _).2 h
  have hA : rbar g' = rbar g := by
    obtain ⟨n, hn1, hn2⟩ := ((hloc 1).and hcong).exists
    ext a b
    rw [← ρ.red g' a b]
    have e1 := congrFun (congrFun hn1 a) b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at e1
    rw [← hres _ _ e1, ρ.red, map_pow, key (rbar g) _ hgm hn2]
  have hlM : ((l : ℕ) : R) ∈ maximalIdeal R := by
    rw [← res_eq_zero_iff O R, map_natCast]
    exact CharP.cast_eq_zero _ l
  have hX : ∀ a b, ((ρ.hom g) ^ m - 1) a b ∈ maximalIdeal R := by
    intro a b
    rw [← res_eq_zero_iff O R, Matrix.sub_apply, map_sub, ← map_pow, ρ.red, map_pow, hgm]
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply]
  have hB : ∀ N : ℕ, ∀ a b, ((ρ.hom g') ^ m - 1) a b ∈ maximalIdeal R ^ N := by
    intro N
    have hfin : ∀ᶠ n : ℕ in Filter.atTop, N ≤ n.factorial + 1 := by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      exact hn.trans ((Nat.self_le_factorial n).trans (Nat.le_succ _))
    obtain ⟨n, hn1, hn2⟩ := ((hloc N).and hfin).exists
    have hp := pt_pow (maximalIdeal R) l hlM _ hX n.factorial
    have hq : (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix (((ρ.hom g) ^ m) ^ l ^ n.factorial) = 1 := by
      rw [← sub_eq_zero, ← map_one ((Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix), ← map_sub]
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_le_pow_right hn2 (hp a b)
    have e : (ρ.hom (g ^ l ^ n.factorial)) ^ m = ((ρ.hom g) ^ m) ^ l ^ n.factorial := by
      rw [map_pow, ← pow_mul, ← pow_mul, mul_comm]
    have hr : (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix ((ρ.hom g') ^ m) = 1 := by
      rw [map_pow, ← hn1, ← map_pow, e]
      exact hq
    intro a b
    have h2 : (Ideal.Quotient.mk (maximalIdeal R ^ N)).mapMatrix ((ρ.hom g') ^ m - 1) = 0 := by
      rw [map_sub, hr, map_one, sub_self]
    have := congrFun (congrFun h2 a) b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  refine ⟨hA, ?_⟩
  have hbot : ⨅ i : ℕ, maximalIdeal R ^ i = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  rw [← sub_eq_zero]
  ext a b
  have hmem : ((ρ.hom g') ^ m - 1) a b ∈ ⨅ i : ℕ, maximalIdeal R ^ i := Ideal.mem_iInf.2 (fun N => hB N a b)
  rw [hbot, Ideal.mem_bot] at hmem
  rw [Matrix.zero_apply]
  exact hmem
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SInternal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem part_indep {O X R : Type} [CommRing O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R]
    (W : WPres O X R) : iSupIndep W.part := by
  have h := (W.A.val.toLinearMap.iSupIndep_map Subtype.val_injective
    (gr_internal O X R W).submodule_iSupIndep)
  convert h using 1
  funext j
  rw [WPres.gr, Submodule.map_comap_eq, eq_comm, inf_eq_right]
  intro x hx
  exact ⟨⟨x, W.part_le_A hx⟩, rfl⟩

private theorem part_gen {O X R : Type} [CommRing O] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [CommRing R] [Algebra O R] (W : WPres O X R) :
    Algebra.adjoin O ((W.part 0 : Set R) ∪ Set.range W.z) = W.A := by
  have h := congrArg (Subalgebra.map W.A.val) (gr_gen O R X W)
  rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val] at h
  rw [← h]
  congr 1
  rw [Set.image_union]
  congr 1
  · ext x
    constructor
    · intro hx
      exact ⟨⟨x, W.part_le_A hx⟩, hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy
  · ext x
    simp [WPres.zA, WPres.z]

private theorem quot_pres {O X R S : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing S] [Algebra O S] [IsCO O S] (W : WPres O X R) (org : W.HasOrigin) (π : R →ₐ[O] S)
    (surj : Function.Surjective π) {κ : Type} [Finite κ] (g : κ → R) (c : κ → X) (hg : ∀ i, g i ∈ W.part (c i))
    (ker : RingHom.ker π = Ideal.span (Set.range g)) :
    ∃ WS : WPres O X S, (∀ w, WS.part w = (W.part w).map π.toLinearMap) ∧ ∀ i, WS.z i ∈ maximalIdeal S := by
  have hz : ∀ i, W.z i ∈ maximalIdeal R := by
    intro i
    let ψ : R →+* ResidueField O := (IsLocalRing.residue O).comp (W.origin org).toRingHom
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      exact ⟨algebraMap O R a, by simp [ψ]⟩
    have heq : RingHom.ker ψ = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ψ hψ)
    rw [← heq, RingHom.mem_ker]
    simp [ψ, WPres.z, WPres.origin_π]
  have hhom : IsHomog O W.wt (RingHom.ker (π.comp W.π)) := by
    have h := (homog_span O R X W κ (fun i => ⟨g i, W.part_le_A (hg i)⟩) c
      (fun i => Submodule.mem_comap.mpr (hg i))).1
    convert h using 1
    ext f
    rw [RingHom.mem_ker, Ideal.mem_comap]
    show π (W.π f) = 0 ↔ W.π f ∈ Ideal.span (Set.range g)
    rw [← ker, RingHom.mem_ker]
  refine ⟨W.quot π surj hhom, ?_, ?_⟩
  · intro w
    exact Submodule.map_comp W.π.toLinearMap π.toLinearMap (wtPart O W.wt w)
  · intro i
    show π (W.z i) ∈ maximalIdeal S
    rw [← res_eq_zero_iff O S, res_map, res_eq_zero_iff]
    exact hz i

theorem UpperTheory.V.GradeZeroInterpolatingElement.sInternal :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, iSupIndep M.sPart ∧ (∃ s : Finset M.S, (∀ x ∈ s, ∃ w, x ∈ M.sPart w) ∧ Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ s) = M.SS) ∧ ∃ WS : WPres c.O (ℤ × ℤ) M.S, (∀ w, WS.part w = M.sPart w) ∧ ∀ i, WS.z i ∈ maximalIdeal M.S := by
  intro Ω _ _ _ l _ c D _ M
  classical
  let g : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → M.R := Sum.elim M.F (Sum.elim M.E M.Z)
  let cw : Fin (M.r + 1) ⊕ Fin M.r' ⊕ Fin M.m → ℤ × ℤ :=
    Sum.elim (fun _ => -wPs) (Sum.elim (fun _ => wPs) (fun _ => 0))
  have hg : ∀ i, g i ∈ M.W.part (cw i) := by
    rintro (i | i | i)
    · exact M.hF i
    · exact M.hE i
    · exact (M.hZ i).1
  have hker : RingHom.ker M.π = Ideal.span (Set.range g) := by
    rw [M.ker]
    simp only [g, Set.Sum.elim_range, Set.union_assoc]
  obtain ⟨WS, hpart, hzm⟩ := quot_pres M.W M.org M.π M.surj g cw hg hker
  have hp : WS.part = M.sPart := funext hpart
  have hA : WS.A = M.SS := by
    unfold WPres.A Model.SS
    congr
  haveI := WS.fin
  refine ⟨by rw [← hp]; exact part_indep WS, ⟨Finset.univ.image WS.z, ?_, ?_⟩, WS, hpart, hzm⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨WS.wt i, by rw [← hp]; exact WS.z_mem i⟩
  · rw [← hA, ← part_gen WS, ← hp]
    congr 2
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

private theorem wt_add' (i k j : Fin 4) : wt i j = wt i k + wt k j := by
  simp only [wt, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> ring

private theorem wt_self' (i : Fin 4) : wt i i = 0 := by
  simp [wt]

variable {R : Type} [CommRing R]

private theorem wv_add' (t : Rˣ × Rˣ) (a b : ℤ × ℤ) : wv t (a + b) = wv t a * wv t b := by
  simp only [wv, Prod.fst_add, Prod.snd_add, zpow_add]
  rw [mul_mul_mul_comm]

private theorem wv_zero' (t : Rˣ × Rˣ) : wv t 0 = 1 := by simp [wv]

private theorem adj_mul' (X Y : M4 R) : adj (X * Y) = adj Y * adj X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, sgn] <;> ring

private theorem adj_adj' (X : M4 R) : adj (adj X) = X := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn]

private theorem adj_smul' (a : R) (X : M4 R) : adj (a • X) = a • adj X := by
  ext i j
  simp only [adj_apply, Matrix.smul_apply, smul_eq_mul]
  rw [mul_smul_comm]

private theorem adj_one' : adj (1 : M4 R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Matrix.one_apply]

private theorem tconj_apply' (t : Rˣ × Rˣ) (X : M4 R) (i j : Fin 4) : tconj t X i j = (wv t (wt i j) : R) * X i j := rfl

private theorem tconj_unit' (t : Rˣ × Rˣ) : ∃ u : (M4 R)ˣ, ∀ X, tconj t X = u * X * (u⁻¹ : (M4 R)ˣ) := by
  let d : Fin 4 → Rˣ := fun i => wv t (lamW i, muW i)
  have key : ∀ i j, wv t (wt i j) = d i * (d j)⁻¹ := by
    intro i j
    rw [eq_mul_inv_iff_mul_eq, ← wv_add']
    congr 1
    simp [wt]
  let u : (M4 R)ˣ := ⟨Matrix.diagonal fun i => (d i : R), Matrix.diagonal fun i => ((d i)⁻¹ : Rˣ),
    by simp [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one], by simp [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]⟩
  refine ⟨u, fun X => ?_⟩
  ext i j
  simp only [u, Units.inv_mk, tconj_apply', key, Units.val_mul, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.grp :
    ∀ (R : Type) [CommRing R], (∀ X Y : M4 R, adj (X * Y) = adj Y * adj X) ∧ (∀ X : M4 R, adj (adj X) = X) ∧ (∀ X Y : M4 R, adj (X + Y) = adj X + adj Y) ∧ (∀ (a : R) (X : M4 R), adj (a • X) = a • adj X) ∧ adj (1 : M4 R) = 1 ∧ (∀ (R' : Type) [CommRing R'] (f : R →+* R') (X : M4 R), adj (X.map f) = (adj X).map f) ∧ (∀ (ν : R) (g g' : M4 R), IsGSp ν g → g * g' = 1 → adj g = ν • g') ∧ (∀ (ν ν' : R) (g g' : M4 R), IsGSp ν g → IsGSp ν' g' → IsGSp (ν * ν') (g * g')) ∧ (∀ (t : Rˣ × Rˣ) (X Y : M4 R), tconj t (X * Y) = tconj t X * tconj t Y) ∧ (∀ t : Rˣ × Rˣ, tconj t (1 : M4 R) = 1) ∧ (∀ (t : Rˣ × Rˣ) (X : M4 R), adj (tconj t X) = tconj t (adj X)) ∧ (∀ (t : Rˣ × Rˣ) (X : M4 R), (tconj t X).trace = X.trace) ∧ (∀ t : Rˣ × Rˣ, ∃ u : (M4 R)ˣ, ∀ X, tconj t X = u * X * (u⁻¹ : (M4 R)ˣ)) := by
  intro R _
  refine ⟨adj_mul', adj_adj', ?_, adj_smul', adj_one', ?_, ?_, ?_, ?_, ?_, ?_, ?_, tconj_unit'⟩
  · intro X Y
    ext i j
    simp [adj_apply]
  · intro R' _ f X
    ext i j
    simp [adj_apply, Matrix.map_apply]
  · intro ν g g' hg h
    have hg' : adj g * g = ν • 1 := hg
    calc adj g = adj g * (g * g') := by rw [h, mul_one]
      _ = adj g * g * g' := (mul_assoc _ _ _).symm
      _ = ν • g' := by rw [hg', smul_mul_assoc, one_mul]
  · intro ν ν' g g' hg hg'
    have h1 : adj g * g = ν • 1 := hg
    have h2 : adj g' * g' = ν' • 1 := hg'
    show adj (g * g') * (g * g') = (ν * ν') • 1
    rw [adj_mul', mul_assoc, ← mul_assoc (adj g), h1, smul_mul_assoc, one_mul, mul_smul_comm, h2,
      smul_smul]
  · intro t X Y
    ext i j
    simp only [tconj_apply', Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [wt_add' i k j, wv_add', Units.val_mul]
    ring
  · intro t
    ext i j
    rw [tconj_apply', Matrix.one_apply]
    split_ifs with h
    · subst h
      simp [wt_self', wv_zero']
    · simp
  · intro t X
    ext i j
    simp only [adj_apply, tconj_apply']
    rw [wt_rev, mul_smul_comm]
  · intro t X
    simp [Matrix.trace, tconj_apply', wt_self', wv_zero']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.XvanExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem cob_of_coord {H k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k] (a : H → k₀) (z : H → k)
    (h : ∀ φ : k →ₗ[k₀] k₀, ∃ m, ∀ g, φ (z g) = a g * m - m) :
    ∃ m, ∀ g, z g = algebraMap k₀ k (a g) * m - m := by
  by_cases ha : ∀ g, a g = 1
  · refine ⟨0, fun g => ?_⟩
    rw [mul_zero, sub_zero]
    refine (Module.forall_dual_apply_eq_zero_iff k₀ (z g)).1 fun φ => ?_
    obtain ⟨m, hm⟩ := h φ
    rw [hm g, ha g, one_mul, sub_self]
  · push_neg at ha
    obtain ⟨g₀, hg₀⟩ := ha
    have hne : a g₀ - 1 ≠ 0 := sub_ne_zero.2 hg₀
    refine ⟨(a g₀ - 1)⁻¹ • z g₀, fun g => ?_⟩
    rw [← Algebra.smul_def, ← sub_eq_zero]
    refine (Module.forall_dual_apply_eq_zero_iff k₀ _).1 fun φ => ?_
    obtain ⟨m, hm⟩ := h φ
    have key : φ ((a g₀ - 1)⁻¹ • z g₀) = m := by
      rw [map_smul, hm g₀, smul_eq_mul, ← sub_one_mul, inv_mul_cancel_left₀ hne]
    rw [map_sub, map_sub, map_smul, key, hm g, smul_eq_mul, sub_self]

theorem UpperTheory.V.GradeZeroInterpolatingElement.xvanExt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (k : Type) [Field k] (red : c.O →+* k), (∀ a ∈ maximalIdeal c.O, red a = 0) → ∀ γ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹], ∀ z : G ℚ Ω → k, IsLocallyConstant z → (∀ g h, z (g * h) = z g + red (γ g : c.O) * z h) → D.UnrT z 0 → (∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, z g = red (γ g : c.O) * m - m) → ∃ m, ∀ g, z g = red (γ g : c.O) * m - m := by
  intro Ω _ _ _ l _ c D hD k _ red hred γ hγ z hz hcoc hunr hloc
  have hlh : IsLocalHom red := ⟨fun a ha => by
    by_contra hn
    have h0 := hred a ((mem_maximalIdeal a).2 hn)
    rw [h0] at ha
    exact not_isUnit_zero ha⟩
  letI : Algebra (ResidueField c.O) k := (ResidueField.lift red).toAlgebra
  have hι : ∀ a : c.O, red a = algebraMap (ResidueField c.O) k (residue c.O a) := fun a =>
    (ResidueField.lift_residue_apply red a).symm
  have hX : D.XVan γ := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hD.xvan D.al (by simp)).1
    · exact (hD.xvan D.be (by simp)).1
    · exact (hD.xvan D.th (by simp)).1
    · exact (hD.xvan D.al (by simp)).2
    · exact (hD.xvan D.be (by simp)).2
    · exact (hD.xvan D.th (by simp)).2
  simp only [hι]
  apply cob_of_coord (fun g => Raw.bar γ g) z
  intro φ
  have h1 : ∀ g h, φ (z (g * h)) = φ (z g) + Raw.bar γ g * φ (z h) := by
    intro g h
    rw [hcoc g h, map_add, hι, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have h2 : D.UnrT (fun g => φ (z g)) 0 := by
    intro A hA g hg hb
    simp only [hunr A hA g hg hb, map_zero]
  have h3 : ∀ v ∈ D.T, ∃ m, ∀ g ∈ D.Gp v, φ (z g) = Raw.bar γ g * m - m := by
    intro v hv
    obtain ⟨m, hm⟩ := hloc v hv
    refine ⟨φ m, fun g hg => ?_⟩
    rw [hm g hg, hι, ← Algebra.smul_def, map_sub, map_smul, smul_eq_mul]
  exact hX (fun g => φ (z g)) (hz.comp fun x => φ x) h1 h2 h3
end

