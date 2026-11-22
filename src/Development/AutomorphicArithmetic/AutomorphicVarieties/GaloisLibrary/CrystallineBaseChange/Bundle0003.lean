import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0954
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RootSum
section
open UpperTheory.V.Af

namespace UpperTheory.V.Br

private theorem roots_finset (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) (B : Multiset ℂ) :
    ∃ T : Finset (Multiset ℂ), T.card ≤ 2 ^ B.card ∧ ∀ C : Multiset ℂ, C.map (· ^ f) = B → C ∈ T := by
  classical
  induction B using Multiset.induction_on with
  | empty =>
    refine ⟨{0}, by simp, fun C hC => ?_⟩
    simpa using hC
  | cons b B ih =>
    obtain ⟨T, hT, hm⟩ := ih
    refine ⟨((Polynomial.nthRoots f b).toFinset ×ˢ T).image fun x => x.1 ::ₘ x.2, ?_, fun C hC => ?_⟩
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_product, Multiset.card_cons, pow_succ']
      exact Nat.mul_le_mul (((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots f b)).trans h2) hT
    · obtain ⟨a, ha, hab, hr⟩ := (Multiset.map_eq_cons _ _ _ _).2 hC
      refine Finset.mem_image.2 ⟨(a, C.erase a), Finset.mem_product.2 ⟨?_, hm _ hr⟩, Multiset.cons_erase ha⟩
      exact Multiset.mem_toFinset.2 ((Polynomial.mem_nthRoots h1).2 hab)

private theorem roots_card (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) (B : Multiset ℂ) :
    Finite {C : Multiset ℂ // C.map (· ^ f) = B} ∧ Nat.card {C : Multiset ℂ // C.map (· ^ f) = B} ≤ 2 ^ B.card := by
  obtain ⟨T, hT, hm⟩ := roots_finset f h1 h2 B
  let g : {C : Multiset ℂ // C.map (· ^ f) = B} → T := fun C => ⟨C.1, hm _ C.2⟩
  have hg : Function.Injective g := fun x y h => Subtype.ext (congrArg Subtype.val h :)
  refine ⟨Finite.of_injective g hg, (Nat.card_le_card_of_injective g hg).trans ?_⟩
  simpa using hT

private theorem pairs_card {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) :
    Finite {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ∧
      Nat.card {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ≤ 2 ^ n * Nat.card D.S := by
  haveI := D.fin
  haveI := Fintype.ofFinite D.S
  haveI : ∀ s, Finite {C : Multiset ℂ // C.map (· ^ f) = D.β s} := fun s => (roots_card f h1 h2 _).1
  let e := Equiv.subtypeProdEquivSigmaSubtype fun (s : D.S) (C : Multiset ℂ) => C.map (· ^ f) = D.β s
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_sigma]
  refine (Finset.sum_le_card_nsmul _ _ (2 ^ n) fun s _ => ?_).trans ?_
  · have := (roots_card f h1 h2 (D.β s)).2
    rwa [D.card] at this
  · simp [mul_comm]

private theorem pairs_conj {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt) (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2)
    (σ : ℂ ≃+* ℂ) :
    ∃ e : {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ≃ {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1},
      ∀ x, (e x).1.2 = x.1.2.map σ := by
  haveI := (pairs_card D f h1 h2).1
  obtain ⟨e, he⟩ := D.conj σ
  let g : {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} → {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} :=
    fun x => ⟨(e x.1.1, x.1.2.map σ), by
      show (x.1.2.map σ).map (· ^ f) = D.β (e x.1.1)
      rw [he, ← x.2, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun b _ => by simp⟩
  have hg : Function.Injective g := fun x y h => by
    have h' := congrArg Subtype.val h
    simp only [g, Prod.mk.injEq] at h'
    exact Subtype.ext (Prod.ext (e.injective h'.1) (Multiset.map_injective σ.injective h'.2))
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hg), fun _ => rfl⟩

private theorem int_root (p f : ℕ) (h1 : 1 ≤ f) (a : ℤ) (b : ℂ) (h : IsIntegral ℤ (((p ^ f : ℕ) : ℂ) ^ a * b ^ f)) :
    IsIntegral ℤ ((p : ℂ) ^ a * b) := by
  refine IsIntegral.of_pow (n := f) h1 ?_
  convert h using 1
  rw [mul_pow, Nat.cast_pow, ← zpow_natCast, ← zpow_natCast (p : ℂ), ← zpow_mul, ← zpow_mul, mul_comm a]

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.rootSum :
    UpperTheory.V.Br.RootSum := by
  intro n p hp m wt I _ q f hf D
  haveI : ∀ i, Finite {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} :=
    fun i => (pairs_card (D i) (f i) (hf i).1 (hf i).2.1).1
  have hmem : ∀ i (x : {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1}), ∀ b ∈ x.1.2,
      b ^ f i ∈ (D i).β x.1.1 := fun i x b hb => by
    rw [← x.2]
    exact Multiset.mem_map_of_mem _ hb
  refine ⟨⟨Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool, inferInstance,
    fun x => x.2.1.1.2, ?_, ?_, ?_, ?_, ?_⟩, ?_, id, Function.injective_id, fun _ => rfl⟩
  · rintro ⟨i, x, t⟩
    have := (D i).card x.1.1
    rw [← x.2, Multiset.card_map] at this
    exact this
  · intro σ
    choose e he using fun i => pairs_conj (D i) (f i) (hf i).1 (hf i).2.1 σ
    exact ⟨Equiv.sigmaCongrRight fun i => (e i).prodCongr (Equiv.refl _), fun x => he x.1 x.2.1⟩
  · rintro ⟨i, x, t⟩ b hb
    have h := (D i).pure _ _ (hmem i x b hb)
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hq : ((q i : ℕ) : ℝ) = (p : ℝ) ^ f i := by rw [(hf i).2.2, Nat.cast_pow]
    rw [norm_pow, hq, ← Real.rpow_natCast (p : ℝ), ← Real.rpow_mul hp0, mul_comm, Real.rpow_mul hp0, Real.rpow_natCast] at h
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hp0 _) (by have := (hf i).1; omega)).1 h
  · rintro a ha ⟨i, x, t⟩ b hb
    have h := (D i).int a ha _ _ (hmem i x b hb)
    refine int_root p (f i) (hf i).1 a b ?_
    rw [← (hf i).2.2]
    exact h
  · rintro a ha ⟨i, x, t⟩ b hb
    have h := (D i).intInv a ha _ _ (hmem i x b hb)
    refine int_root p (f i) (hf i).1 a b⁻¹ ?_
    rw [← (hf i).2.2, inv_pow]
    exact h
  · show Nat.card (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) ≤ _
    rw [Nat.card_sigma, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    have := (pairs_card (D i) (f i) (hf i).1 (hf i).2.1).2
    calc _ ≤ 2 ^ n * Nat.card (D i).S * 2 := Nat.mul_le_mul_right _ this
      _ = _ := by ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SatOfPol
section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open scoped Matrix

section General

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ G V} {ρ : Representation ℂ G W} {K : Subgroup G} {h : G → ℂ} {x : V} {y : W}

private theorem pair_heckeVec (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed σ K)
    (hy : y ∈ fixed ρ K) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (θ : G ≃* G) (hθ : ∀ k, k ∈ K ↔ θ k ∈ K)
    (hi : ∀ g v w, β (σ (θ g) v) (ρ g w) = β v w)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t⁻¹ = t ∧ g = a * t * b) :
    β (heckeVec σ K h x) y = β x (heckeVec ρ K h y) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have hg := GlobalTheory.LGrp.mem_fixed.1 hy
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (σ (a * t * b) x) y = β (σ t x) y := fun a ha b hb t => by
    obtain ⟨a, rfl⟩ := θ.surjective a
    rw [map_mul σ, map_mul σ, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hg a ((hθ a).2 ha)).symm).trans (hi a _ _)
  have bi' : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β x (ρ (a * t * b) y) = β x (ρ t y) := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg b hb]
    exact (congrArg (fun u => β u _) (hf _ ((hθ a).1 ha)).symm).trans (hi a _ _)
  have inv : ∀ t, β (σ (θ t⁻¹) x) y = β x (ρ t y) := fun t => by
    rw [← hi t⁻¹ x (ρ t y)]; simp
  have e1 := (β.flip y).toAddMonoidHom.map_finsum (finite_heckeVec hK hh σ x)
  have e2 := (β x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh ρ y)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change β (h c.out • σ c.out x) y = β x (h c.out • ρ c.out y)
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e⟩ := ht _ h0
  congr 1
  rw [e, bi _ ha _ hb, bi' _ ha _ hb, ← inv, htt]

private theorem exists_fixed_pair [TopologicalSpace G] [IsTopologicalGroup G] (hρ : IsSmooth ρ)
    (hK : IsCompact (K : Set G)) (l : W →ₗ[ℂ] ℂ) (hl : ∀ k ∈ K, ∀ v, l (ρ k v) = l v) (y : W) :
    ∃ y' ∈ fixed ρ K, l y' = l y := by
  classical
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hfi : (GlobalTheory.OrbitAvg.stab ρ K y).FiniteIndex := by
    have ho : IsOpen (GlobalTheory.OrbitAvg.stab ρ K y : Set K) := (hρ y).preimage continuous_subtype_val
    haveI := (GlobalTheory.OrbitAvg.stab ρ K y).quotient_finite_of_isOpen ho
    exact Subgroup.finiteIndex_of_finite_quotient
  refine ⟨GlobalTheory.OrbitAvg.avg ρ K y,
    GlobalTheory.LGrp.mem_fixed.2 fun u hu => GlobalTheory.OrbitAvg.avg_invariant ρ K hfi ⟨u, hu⟩, ?_⟩
  haveI := Fintype.ofFinite (K ⧸ GlobalTheory.OrbitAvg.stab ρ K y)
  have hc : ((GlobalTheory.OrbitAvg.stab ρ K y).index : ℂ) ≠ 0 := by exact_mod_cast hfi.index_ne_zero
  have h1 : ∀ q : K ⧸ GlobalTheory.OrbitAvg.stab ρ K y, l (ρ (q.out : K) y) = l y := fun q => hl _ q.out.2 y
  simp only [GlobalTheory.OrbitAvg.avg, GlobalTheory.OrbitAvg.avgH, GlobalTheory.OrbitAvg.cv, finsum_eq_sum_of_fintype, map_smul, map_sum]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    ← Subgroup.index, nsmul_eq_mul, smul_eq_mul, inv_mul_cancel_left₀ hc]

end General

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.ConjPlace in
private theorem sat_eq_of_pair {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (hρ : IsSmooth ρ) (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hβ : ∀ x, (∀ y, β x y = 0) → x = 0)
    (hi : ∀ g x y, β (σ (GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) n g) x) (ρ g y) = β x y)
    {x : V} {B C : Multiset ℂˣ} (hx : IsSatVecGL w σ x B) (hC : HasSatGL w ρ C) : B = C := by
  classical
  have hKc : IsCompact (KGL w n : Set (GL (Fin n) (w.adicCompletion E))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers E w)
  obtain ⟨y₀, hy₀⟩ : ∃ y, β x y ≠ 0 := by
    by_contra hn
    exact hx.1 (hβ x fun y => by_contra fun h => hn ⟨y, h⟩)
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  obtain ⟨y, hyK, hy⟩ := exists_fixed_pair hρ hKc (β x) (fun k hk v => by
    have := hi k x v
    rwa [GlobalTheory.LGrp.mem_fixed.1 hx.2.1 _ ((hK k).1 hk)] at this) y₀
  have hne : β x y ≠ 0 := hy ▸ hy₀
  have hy' := hC.2 y hyK fun h0 => hne (by rw [h0, map_zero])
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  refine eq_of_satEig_eq (qV_ne_zero w) hx.2.2.1 hy'.2.2.1 fun j hj => ?_
  have key := pair_heckeVec (Final.GLintComm E w n) (Tj_mem_hecke hp j) hx.2.1 hyK β
    (GlobalTheory.LFun.ConjPlace.invT c n) hK hi
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      exact ⟨a, ha, b, hb, _, invT_dGL c ϖ j, e⟩)
  rw [hx.2.2.2 _ hp j hj, hy'.2.2.2 _ hp j hj, map_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul] at key
  exact mul_right_cancel₀ hne key

open Neutral.B1 ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published

private theorem conj_locGL {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : GL (Fin a) ((cPl w).adicCompletion E)) :
    Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g) =
      locGL E a w (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) := by
  have key : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v)
      (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      Matrix.GeneralLinearGroup.map (conjLoc _ v)
        (Matrix.GeneralLinearGroup.map (pLoc E (cPl v)) (locGL E a (cPl w) g)) := fun v => rfl
  have key2 : ∀ v, Matrix.GeneralLinearGroup.map (pLoc E v)
      (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E a (cPl w) g)) =
      Matrix.GeneralLinearGroup.map (pLoc E v) (locGL E a w (Matrix.GeneralLinearGroup.map (conjLoc _ w) g)) := fun v => by
    rw [key]
    by_cases h : v = w
    · subst h
      rw [pLoc_locGL, pLoc_locGL]
    · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (conjSrc_injective _ e)), map_one]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_)
  exact congrArg (fun u : GL (Fin a) (v.adicCompletion E) => u.val i j) (key2 v)

private theorem conjLoc_surjective {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    Function.Surjective (conjLoc (IsCMField.complexConj E).toRingEquiv w) := fun y => by
  classical
  refine ⟨pLoc E _ (GlobalTheory.ThetaPull.cFin E (sLoc E w y)), ?_⟩
  rw [← pLoc_conjFin]
  exact (congrArg (pLoc E w) (GlobalTheory.ThetaPull.cFin_cFin _)).trans
    (Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w y)

theorem UpperTheory.V.Br.satOfPol :
    UpperTheory.V.Br.SatOfPol := by
  intro E _ _ _ n P ψ hd w hu B B' hB hB'
  have hu' : (ψ⁻¹).UnrAt w := fun x hx => by
    have h3 : ψ.loc w x = 1 := hu x hx
    exact (congrArg Inv.inv h3).trans inv_one
  have hC := GlobalTheory.SphGal.hasSatGL_twist E n P ψ⁻¹ w B hu' hB
  rw [CG.hasSat_mk] at hB'
  let c : (cPl w).adicCompletion E ≃+* w.adicCompletion E :=
    RingEquiv.ofBijective (conjLoc _ w) ⟨(conjLoc _ w).injective, conjLoc_surjective w⟩
  have hq : Formalism.UG.qV E w = Formalism.UG.qV E (cPl w) := by
    change Ideal.absNorm w.asIdeal = Ideal.absNorm (conjSrc (IsCMField.complexConj E).toRingEquiv w).asIdeal
    rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
    exact (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv _)
      (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv).symm
  obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB'
  have hx' := GlobalTheory.LFun.ConjPlace.isSatVecGL_invT c (conjLoc_spec _ w).2.2 hq hx
  obtain ⟨β, -, hr, hf, -⟩ := hd
  refine sat_eq_of_pair ((P.twist ψ⁻¹).isSmooth_locRep w) β.flip hr (fun g u v => ?_) hx' hC
  obtain ⟨g, rfl⟩ : ∃ g', Matrix.GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g' = g :=
    ⟨Matrix.GeneralLinearGroup.map c.symm.toRingHom g, Units.ext (Matrix.ext fun i j => c.apply_symm_apply _)⟩
  have e1 : GlobalTheory.LFun.ConjPlace.invT (RingEquiv.refl _) n (Matrix.GeneralLinearGroup.map (conjLoc _ w) g) =
      GlobalTheory.LFun.ConjPlace.invT c n g := Units.ext (Matrix.ext fun i j => by
    rw [GlobalTheory.LFun.ConjPlace.invT_val, GlobalTheory.LFun.ConjPlace.invT_val, ← map_inv]; rfl)
  rw [e1]
  change β ((P.twist ψ⁻¹).locRep w _ v) (P.locRep (cPl w) ((GlobalTheory.LFun.ConjPlace.invT c n).symm (GlobalTheory.LFun.ConjPlace.invT c n g)) u) = β v u
  rw [MulEquiv.symm_apply_apply, CuspSub.locRep_eq, CuspSub.locRep_eq, ← conj_locGL, ← hf (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E n (cPl w) g)) v u]
  have e2 : Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (Matrix.GeneralLinearGroup.map (GlobalTheory.ThetaPull.cFin E) (locGL E n (cPl w) g)) = locGL E n (cPl w) g :=
    Units.ext (Matrix.ext fun i j => GlobalTheory.ThetaPull.cFin_cFin _)
  exact congrArg (fun k => β _ (P.op (.fin k) u)) e2.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.SignNe
section
open NumberField UpperTheory.V.Af.Bc

private theorem range_res_eq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Field K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] :
    (res F Ω K).range = (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨τ, rfl⟩ y hy
    obtain ⟨k, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    exact τ.commutes k
  · intro h
    refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) fun k => h _ (AlgHom.mem_fieldRange.mpr ⟨k, rfl⟩), ?_⟩
    ext y
    rfl

private theorem equiv_of_range {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω] (K K' : Type) [Field K] [Algebra F K]
    [Algebra K Ω] [IsScalarTower F K Ω] [Field K'] [Algebra F K'] [Algebra K' Ω] [IsScalarTower F K' Ω]
    (h : (res F Ω K).range = (res F Ω K').range) : Nonempty (K ≃ₐ[F] K') := by
  have hK := InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K Ω).fieldRange
  have hK' := InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K' Ω).fieldRange
  rw [range_res_eq, range_res_eq] at h
  have he : (IsScalarTower.toAlgHom F K Ω).fieldRange = (IsScalarTower.toAlgHom F K' Ω).fieldRange := by
    rw [← hK, ← hK', h]
  have he' : (IsScalarTower.toAlgHom F K Ω).range = (IsScalarTower.toAlgHom F K' Ω).range := by
    rw [← AlgHom.fieldRange_toSubalgebra, ← AlgHom.fieldRange_toSubalgebra, he]
  exact ⟨(AlgEquiv.ofInjectiveField _).trans
    ((Subalgebra.equivOfEq _ _ he').trans (AlgEquiv.ofInjectiveField _).symm)⟩

theorem UpperTheory.V.Br.signNe :
    UpperTheory.V.Br.SignNe := by
  intro K K' Ω _ _ _ _ _ _ _ _ _ _ _ hK hcop heq
  obtain ⟨e⟩ := equiv_of_range K K' heq
  rw [← NumberField.discr_eq_discr_of_algEquiv (K := K) e, isCoprime_self, Int.isUnit_iff] at hcop
  have := NumberField.abs_discr_gt_two (K := K) (by omega)
  rcases hcop with h | h <;> rw [h] at this <;> norm_num at this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.TwCard
section
open UpperTheory.V.Af

theorem UpperTheory.V.Br.twCard :
    UpperTheory.V.Br.TwCard := by
  intro Γ k _ _ n r hirr S hS
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Submodule.eq_bot_of_subsingleton) hirr.1
    · exact h
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  choose! g hg using hS
  have key : ∀ δ ∈ S, ∀ s, ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k)
      = ((δ s : kˣ) : k) • ((r s : Matrix (Fin n) (Fin n) k) * (g δ : Matrix (Fin n) (Fin n) k)) := by
    intro δ hδ s
    have h1 := congrArg (fun A : GL (Fin n) k => (A : Matrix (Fin n) (Fin n) k) * (g δ : Matrix (Fin n) (Fin n) k))
      (hg δ hδ s)
    simp only [tw_val, Units.val_mul, mul_assoc, Units.inv_mul, mul_one] at h1
    rw [← h1, smul_mul_assoc]
  have hli : LinearIndependent k (fun δ : S => ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc δ0
    have hsum : ∀ s, ∑ δ : S, (c δ * ((δ.1 s : kˣ) : k)) • ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
      intro s
      have h2 : (r s : Matrix (Fin n) (Fin n) k) *
          ∑ δ : S, (c δ * ((δ.1 s : kˣ) : k)) • ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
        rw [Finset.mul_sum]
        have e : ∑ δ : S, (r s : Matrix (Fin n) (Fin n) k) *
            ((c δ * ((δ.1 s : kˣ) : k)) • ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
            (∑ δ : S, c δ • ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) * (r s : Matrix (Fin n) (Fin n) k) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun δ _ => ?_
          rw [smul_mul_assoc, key δ.1 δ.2 s, mul_smul_comm, mul_smul]
        rw [e, hc, zero_mul]
      have h3 := congrArg (fun A => (((r s)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * A) h2
      simpa [← mul_assoc] using h3
    have hD := (linearIndependent_monoidHom Γ k).comp (fun δ : S => (Units.coeHom k).comp δ.1)
      (fun a b hab => Subtype.ext (MonoidHom.ext fun s => Units.ext (DFunLike.congr_fun hab s)))
    rw [Fintype.linearIndependent_iff] at hD
    have hz : ∀ i j, ∀ δ : S, c δ * ((g δ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0 := by
      intro i j
      apply hD
      funext s
      have e := congrFun (congrFun (hsum s) i) j
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, MonoidHom.coe_comp,
        Units.coeHom_apply, Pi.zero_apply]
      rw [← e]
      exact Finset.sum_congr rfl fun δ _ => by ring
    by_contra hc0
    have h0 : ((g δ0 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
      ext i j
      exact (mul_eq_zero.mp (hz i j δ0)).resolve_left hc0
    exact (g δ0).ne_zero h0
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, Fintype.card_coe] at hcard
  rw [sq]
  exact hcard
end

