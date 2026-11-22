import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0036
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0018
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0201
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0035
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0018

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.FreeSummand
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def fsSub {Λ R M P : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [AddCommGroup M] [Module Λ M]
    [AddCommGroup P] [Module R P] (θ : R →ₐ[Λ] Module.End Λ M) (E : P ≃+ M) (hE : ∀ (r : R) x, E (r • x) = θ r (E x))
    (N : Submodule Λ M) (hN : ∀ r, ∀ m ∈ N, θ r m ∈ N) : Submodule R P where
  carrier := {x | E x ∈ N}
  add_mem' := fun {x y} hx hy => by
    change E (x + y) ∈ N
    rw [map_add]; exact N.add_mem hx hy
  zero_mem' := by
    change E 0 ∈ N
    rw [map_zero]; exact N.zero_mem
  smul_mem' := fun r x hx => by
    change E (r • x) ∈ N
    rw [hE]; exact hN r _ hx

private theorem fs_abs {Λ R M P : Type} [CommRing Λ] [CommRing R] [IsLocalRing R] [Algebra Λ R] [AddCommGroup M] [Module Λ M]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    (θ : R →ₐ[Λ] Module.End Λ M) (E : P ≃+ M) (hE : ∀ (r : R) x, E (r • x) = θ r (E x))
    (N C : Submodule Λ M) (hN : ∀ r, ∀ m ∈ N, θ r m ∈ N) (hC : ∀ r, ∀ m ∈ C, θ r m ∈ C) (h : _root_.IsCompl N C) :
    ∃ (rk : ℕ) (e : N ≃+ (Fin rk → R)), ∀ (r : R) (m m' : N), (m' : M) = θ r m → e m' = r • e m := by
  set P' := fsSub θ E hE N hN with hP'
  set Q' := fsSub θ E hE C hC with hQ'
  have hc : _root_.IsCompl P' Q' := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx1 hx2
      have h0 : E x = 0 := (Submodule.disjoint_def.mp h.disjoint) _ hx1 hx2
      exact E.injective (h0.trans (map_zero E).symm)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hx : E x ∈ N ⊔ C := by rw [h.sup_eq_top]; trivial
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hx
      rw [Submodule.mem_sup]
      refine ⟨E.symm y, (show E (E.symm y) ∈ N by simpa using hy), E.symm z,
        (show E (E.symm z) ∈ C by simpa using hz), ?_⟩
      apply E.injective
      rw [map_add, E.apply_symm_apply, E.apply_symm_apply, hyz]
  haveI : Module.Projective R P' :=
    Module.Projective.of_split P'.subtype (Submodule.linearProjOfIsCompl P' Q' hc)
      (Submodule.linearProjOfIsCompl_comp_subtype hc)
  haveI : Module.Finite R P' :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl P' Q' hc)
      (Submodule.linearProjOfIsCompl_surjective hc)
  haveI : Module.Free R P' := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasis R P'
  let f : N ≃+ P' :=
    { toFun := fun m => ⟨E.symm m, (show E (E.symm m) ∈ N by simp)⟩
      invFun := fun p => ⟨E p, p.2⟩
      left_inv := fun m => by ext; simp
      right_inv := fun p => by ext; simp
      map_add' := fun m m' => by ext; simp }
  refine ⟨Module.finrank R P', f.trans b.equivFun.toAddEquiv, fun r m m' hm => ?_⟩
  have hf : f m' = r • f m := by
    ext
    apply E.injective
    simp only [f, AddEquiv.coe_mk, Equiv.coe_fn_mk, Submodule.coe_smul, hE, E.apply_symm_apply]
    exact hm
  show b.equivFun (f m') = r • b.equivFun (f m)
  rw [hf, LinearEquiv.map_smul]

private theorem fs_gen {σ : Type} [Fintype σ] [DecidableEq σ] (n : σ → ℕ) [∀ s, NeZero (n s)]
    (S : Submonoid (∀ s, Multiplicative (ZMod (n s))))
    (h : ∀ s : σ, (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (n s))) : ∀ s, Multiplicative (ZMod (n s))) ∈ S)
    (g : ∀ s, Multiplicative (ZMod (n s))) : g ∈ S := by
  have key : ∀ s, Pi.mulSingle s (g s) ∈ S := by
    intro s
    have : Pi.mulSingle s (g s) = (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (n s))) : ∀ s, Multiplicative (ZMod (n s))) ^ (Multiplicative.toAdd (g s)).val := by
      rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
    rw [this]
    exact S.pow_mem (h s) _
  rw [← Finset.univ_prod_mulSingle g]
  exact S.prod_mem fun s _ => key s

private def fsAgree {Λ S M : Type} [CommRing Λ] [CommRing S] [Algebra Λ S] [AddCommGroup M] [Module Λ M]
    (N : Submodule Λ M) (act : S →ₐ[Λ] Module.End Λ N) (θ : S →ₐ[Λ] Module.End Λ M) : Subalgebra Λ S where
  carrier := {z | ∀ m : N, (act z m : M) = θ z m}
  mul_mem' := fun {x y} hx hy m => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx, hy]
  add_mem' := fun {x y} hx hy m => by
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hx, hy]
  algebraMap_mem' := fun r m => by
    simp

theorem UpperTheory.V.Pa.Lev.freeSummand :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (l : ℕ) (q n : ℕ) (a : Fin q → ℕ) (M : Type) [AddCommGroup M] [Module Λ M] [Module.Finite Λ M] (ρ : Representation Λ (Del l n a) M) (N C : Submodule Λ M), l.Prime → (l : Λ) ∈ maximalIdeal Λ → Module.Projective (MonoidAlgebra Λ (Del l n a)) ρ.asModule → _root_.IsCompl N C → (∀ g, ∀ m ∈ N, ρ g m ∈ N) → (∀ g, ∀ m ∈ C, ρ g m ∈ C) → ∀ act : MvPowerSeries (Fin q × Fin n) Λ →ₐ[Λ] Module.End Λ N, (∀ (p : Fin q × Fin n) (m : N), (act (1 + MvPowerSeries.X p) m : M) = ρ (Pi.mulSingle p (Multiplicative.ofAdd 1)) m) → ∃ (rk : ℕ) (e : N ≃+ (Fin rk → MvPowerSeries (Fin q × Fin n) Λ ⧸ delIdeal l Λ n a)), ∀ z m, e (act z m) = z • e m := by
  intro Λ _ _ _ _ l q n a M _ _ _ ρ N C hl hlm hproj hNC hN hC act hact
  obtain ⟨φ, hφX, hφs, hloc, -⟩ := exists_groupRing_surj Λ l hl hlm (Fin q × Fin n) (fun p => a p.1)
  have hker : RingHom.ker φ = delIdeal l Λ n a := groupRing_ker Λ l hl hlm (Fin q × Fin n) (fun p => a p.1) φ hφX hφs
  haveI := hloc
  have hθN : ∀ r, ∀ m ∈ N, ρ.asAlgebraHom r m ∈ N := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of g => intro m hm; rw [Representation.asAlgebraHom_of]; exact hN g m hm
    | add x y hx hy => intro m hm; rw [map_add, LinearMap.add_apply]; exact N.add_mem (hx m hm) (hy m hm)
    | smul c x hx => intro m hm; rw [map_smul, LinearMap.smul_apply]; exact N.smul_mem c (hx m hm)
  have hθC : ∀ r, ∀ m ∈ C, ρ.asAlgebraHom r m ∈ C := by
    intro r
    induction r using MonoidAlgebra.induction_on with
    | of g => intro m hm; rw [Representation.asAlgebraHom_of]; exact hC g m hm
    | add x y hx hy => intro m hm; rw [map_add, LinearMap.add_apply]; exact C.add_mem (hx m hm) (hy m hm)
    | smul c x hx => intro m hm; rw [map_smul, LinearMap.smul_apply]; exact C.smul_mem c (hx m hm)
  haveI : Module.Finite Λ ρ.asModule := Module.Finite.equiv ρ.asModuleEquiv.symm
  haveI : Module.Finite (MonoidAlgebra Λ (Del l n a)) ρ.asModule :=
    Module.Finite.of_restrictScalars_finite Λ _ _
  obtain ⟨rk, e0, he0⟩ := fs_abs ρ.asAlgebraHom ρ.asModuleEquiv.toAddEquiv
    (fun r x => ρ.asModuleEquiv_map_smul r x) N C hθN hθC hNC
  let A := fsAgree N act (ρ.asAlgebraHom.comp φ)
  have hgen : ∀ p, (1 + MvPowerSeries.X p : MvPowerSeries (Fin q × Fin n) Λ) ∈ A := by
    intro p m
    show (act (1 + MvPowerSeries.X p) m : M) = ρ.asAlgebraHom (φ (1 + MvPowerSeries.X p)) m
    rw [hφX p, Representation.asAlgebraHom_of]
    exact hact p m
  have hgrp : ∀ g : Del l n a, ∃ w ∈ A, φ w = MonoidAlgebra.of Λ (Del l n a) g := by
    haveI : ∀ p : Fin q × Fin n, NeZero (l ^ a p.1) := fun p => ⟨pow_ne_zero _ hl.ne_zero⟩
    let T : Submonoid (Del l n a) :=
      { carrier := {g | ∃ w ∈ A, φ w = MonoidAlgebra.of Λ (Del l n a) g}
        mul_mem' := fun {x y} hx hy => by
          obtain ⟨w, hw, hwx⟩ := hx
          obtain ⟨w', hw', hwy⟩ := hy
          exact ⟨w * w', A.mul_mem hw hw', by rw [map_mul, hwx, hwy, map_mul]⟩
        one_mem' := ⟨1, A.one_mem, by rw [map_one, map_one]⟩ }
    intro g
    exact fs_gen (fun p : Fin q × Fin n => l ^ a p.1) T (fun p => ⟨_, hgen p, hφX p⟩) g
  have hsurjA : ∀ y, ∃ w ∈ A, φ w = y := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of g => exact hgrp g
    | add x y hx hy =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨w', hw', rfl⟩ := hy
      exact ⟨w + w', A.add_mem hw hw', map_add _ _ _⟩
    | smul c x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨c • w, A.smul_mem hw c, map_smul _ _ _⟩
  have hkill : delIdeal l Λ n a ≤ RingHom.ker act := by
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨p, rfl⟩
    have hw0 : ((1 + MvPowerSeries.X p) ^ l ^ a p.1 - 1 : MvPowerSeries (Fin q × Fin n) Λ) ∈ A :=
      A.sub_mem (A.pow_mem (hgen p) _) A.one_mem
    have hφ0 : φ ((1 + MvPowerSeries.X p) ^ l ^ a p.1 - 1) = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact Ideal.subset_span ⟨p, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    ext m
    rw [hw0 m]
    simp [hφ0]
  have hagree : ∀ z (m : N), (act z m : M) = ρ.asAlgebraHom (φ z) m := by
    intro z m
    obtain ⟨w, hwA, hw⟩ := hsurjA (φ z)
    have hzw : z - w ∈ RingHom.ker act := hkill (by rw [← hker, RingHom.mem_ker, map_sub, hw, sub_self])
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hzw
    rw [hzw, ← hw]
    exact hwA m
  let ψ : MonoidAlgebra Λ (Del l n a) ≃ₐ[Λ] MvPowerSeries (Fin q × Fin n) Λ ⧸ delIdeal l Λ n a :=
    (Ideal.quotientKerAlgEquivOfSurjective hφs).symm.trans (Ideal.quotientEquivAlgOfEq Λ hker)
  have hψ : ∀ z, ψ (φ z) = Ideal.Quotient.mk (delIdeal l Λ n a) z := by
    intro z
    apply ψ.symm.injective
    rw [AlgEquiv.symm_apply_apply]
    simp [ψ, Ideal.quotientKerAlgEquivOfSurjective_apply]
  refine ⟨rk, e0.trans (AddEquiv.piCongrRight fun _ => ψ.toRingEquiv.toAddEquiv), fun z m => ?_⟩
  have h1 := he0 (φ z) m (act z m) (hagree z m)
  funext i
  show ψ (e0 (act z m) i) = z • ψ (e0 m i)
  rw [h1, Pi.smul_apply, smul_eq_mul, map_mul, hψ, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.MultiPhi
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private noncomputable def uP (q n : ℕ) (j : Fin q) : Polynomial (MvPolynomial (Fin q × Fin n) ℤ) :=
  Polynomial.X ^ n + ∑ k : Fin n, Polynomial.C (MvPolynomial.X (j, k)) * Polynomial.X ^ (k : ℕ)

private theorem prod_coeff (R : Type) [CommRing R] (q n : ℕ) (j : Fin q) (k : ℕ) (hk : k ≤ n) :
    (∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i) : PU R q n))).coeff k =
      (-1) ^ (n - k) * emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ (n - k)) := by
  have hh : (emb ℤ R j : MvPolynomial (Fin n) ℤ →+* PU R q n) =
      (MvPolynomial.aeval (fun i : Fin n => (MvPolynomial.X (j, i) : PU R q n))).toRingHom :=
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) (fun i => by simp [emb])
  rw [show emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ (n - k)) = _ from RingHom.congr_fun hh _]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_esymm_eq_multiset_esymm]
  have key := Multiset.prod_X_sub_C_coeff
    (Finset.univ.val.map (fun i : Fin n => (MvPolynomial.X (j, i) : PU R q n))) (k := k) (by simpa using hk)
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, Multiset.map_map] at key
  rw [← key]
  rfl

private theorem exists_mvPolynomial_action_extending_inc (R B M V : Type) [CommRing R] [CommRing B] [AddCommGroup M] [Module B M]
    [AddCommGroup V] [Module R V] (σ : Type) (β : R →+* B) (act : MvPolynomial σ R →ₐ[R] Module.End R V)
    (inc : M →+ V) (hinc : ∀ (t : R) m, inc (β t • m) = t • inc m) :
    ∃ G : MvPolynomial σ B →+ M →+ V, (∀ m, G 1 m = inc m) ∧
      (∀ u h m, G (MvPolynomial.map β u * h) m = act u (G h m)) ∧
      (∀ b h m, G (MvPolynomial.C b * h) m = G h (b • m)) := by
  let X : (σ →₀ ℕ) → B →+ M →+ V := fun e =>
    { toFun := fun b =>
        { toFun := fun m => act (MvPolynomial.monomial e 1) (inc (b • m))
          map_zero' := by simp
          map_add' := fun x y => by simp [smul_add] }
      map_zero' := by ext m; simp
      map_add' := fun x y => by ext m; simp [add_smul] }
  let G : MvPolynomial σ B →+ M →+ V :=
    (Finsupp.liftAddHom X).comp (AddMonoidAlgebra.coeffAddEquiv (R := B) (M := σ →₀ ℕ)).toAddMonoidHom
  have hG : ∀ e b m, G (MvPolynomial.monomial e b) m = act (MvPolynomial.monomial e 1) (inc (b • m)) := by
    intro e b m
    show (Finsupp.liftAddHom X (Finsupp.single e b)) m = _
    rw [Finsupp.liftAddHom_apply_single]
    rfl
  refine ⟨G, ?_, ?_, ?_⟩
  · intro m
    rw [← MvPolynomial.C_1, MvPolynomial.C_apply, hG, one_smul, ← MvPolynomial.C_apply, MvPolynomial.C_1, map_one]
    rfl
  · intro u h m
    induction u using MvPolynomial.induction_on' with
    | monomial e r =>
      induction h using MvPolynomial.induction_on' with
      | monomial e' c =>
        have h1 : MvPolynomial.monomial (e + e') (1 : R) =
            MvPolynomial.monomial e 1 * MvPolynomial.monomial e' 1 := by
          rw [MvPolynomial.monomial_mul, one_mul]
        have h2 : MvPolynomial.monomial e r = r • MvPolynomial.monomial e (1 : R) := by
          rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
        rw [MvPolynomial.map_monomial, MvPolynomial.monomial_mul, hG, hG, mul_smul, hinc]
        generalize inc (c • m) = v
        rw [h1, h2]
        simp only [map_smul, map_mul, Module.End.mul_apply, LinearMap.smul_apply]
      | add p q hp hq =>
        simp only [mul_add, map_add, AddMonoidHom.add_apply, hp, hq]
    | add p q hp hq =>
      simp only [map_add, add_mul, AddMonoidHom.add_apply, hp, hq, LinearMap.add_apply]
  · intro b h m
    induction h using MvPolynomial.induction_on' with
    | monomial e c =>
      rw [MvPolynomial.C_mul_monomial, hG, hG, mul_comm, mul_smul]
    | add p q hp hq =>
      simp only [mul_add, map_add, AddMonoidHom.add_apply, hp, hq]

theorem UpperTheory.V.Pa.Lev.multiPhi :
    ∀ (R B M V : Type) [CommRing R] [CommRing B] [AddCommGroup M] [Module B M] [AddCommGroup V] [Module R V] (q n : ℕ) (β : R →+* B) (P : Fin q → Polynomial B) (act : PU R q n →ₐ[R] Module.End R V) (inc : M →+ V), (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) → (∀ (t : R) m, inc (β t • m) = t • inc m) → (∀ j k, k ≤ n → ∀ m, act (emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ k)) (inc m) = inc (((-1) ^ k * (P j).coeff (n - k)) • m)) → ∃ φ : MSplitAlg P n ⊗[B] M →+ V, (∀ m, φ (1 ⊗ₜ m) = inc m) ∧ ∀ (t : PU R q n) z, φ (Ideal.Quotient.mk (mSplitIdeal P n) (MvPolynomial.map β t) • z) = act t (φ z) := by
  intro R B M V _ _ _ _ _ _ q n β P act inc hmon hdeg hinc hact
  obtain ⟨G, h1, hL, hC⟩ := exists_mvPolynomial_action_extending_inc R B M V (Fin q × Fin n) β act inc hinc
  have hgen : ∀ jk : Fin q × ℕ, ∀ m, G ((∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (jk.1, i))) -
      Polynomial.map MvPolynomial.C (P jk.1)).coeff jk.2) m = 0 := by
    rintro ⟨j, k⟩ m
    dsimp only
    have hprod : (∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i) : MvPolynomial (Fin q × Fin n) B))) =
        (∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i) : PU R q n))).map (MvPolynomial.map β) := by
      simp [Polynomial.map_prod]
    rw [Polynomial.coeff_sub, Polynomial.coeff_map, hprod, Polynomial.coeff_map]
    rcases le_or_gt k n with hk | hk
    · rw [prod_coeff R q n j k hk, map_sub, AddMonoidHom.sub_apply]
      have e1 := hL ((-1) ^ (n - k) * emb ℤ R j (MvPolynomial.esymm (Fin n) ℤ (n - k))) 1 m
      rw [mul_one, h1] at e1
      have e2 := hC ((P j).coeff k) 1 m
      rw [mul_one, h1] at e2
      rw [e1, e2, map_mul, map_pow, map_neg, map_one, Module.End.mul_apply, hact j (n - k) (Nat.sub_le n k) m,
        Nat.sub_sub_self hk]
      rcases Nat.even_or_odd (n - k) with hp | hp
      · simp [hp.neg_one_pow]
      · simp [hp.neg_one_pow, neg_smul]
    · have hd : (∏ i : Fin n, (Polynomial.X - Polynomial.C (MvPolynomial.X (j, i) : PU R q n))).natDegree ≤ n :=
        (Polynomial.natDegree_prod_le _ _).trans
          ((Finset.sum_le_sum fun i _ => Polynomial.natDegree_X_sub_C_le _).trans (by simp))
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hk),
        Polynomial.coeff_eq_zero_of_natDegree_lt ((hdeg j).trans_lt hk)]
      simp
  have hI : ∀ x ∈ mSplitIdeal P n, ∀ a m, G (a * x) m = 0 := by
    intro x hx
    unfold mSplitIdeal Ideal.span at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨jk, rfl⟩ := hx
      intro a m
      induction a using MvPolynomial.induction_on' with
      | monomial e b =>
        have hm : MvPolynomial.monomial e b = MvPolynomial.C b * MvPolynomial.map β (MvPolynomial.monomial e 1) := by
          rw [MvPolynomial.map_monomial, map_one, MvPolynomial.C_mul_monomial, mul_one]
        rw [hm, mul_assoc, hC, hL, hgen jk (b • m), map_zero]
      | add p q hp hq => simp only [add_mul, map_add, AddMonoidHom.add_apply, hp, hq, add_zero]
    | zero => intro a m; simp
    | add x y _ _ hx hy => intro a m; simp only [mul_add, map_add, AddMonoidHom.add_apply, hx, hy, add_zero]
    | smul c x _ hx => intro a m; rw [smul_eq_mul, ← mul_assoc, hx]
  have hvan : (mSplitIdeal P n).toAddSubgroup ≤ G.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    ext m
    simpa using hI x hx 1 m
  let F : MSplitAlg P n →+ M →+ V := QuotientAddGroup.lift (mSplitIdeal P n).toAddSubgroup G hvan
  have hF : ∀ f, F (Ideal.Quotient.mk (mSplitIdeal P n) f) = G f := fun f => rfl
  have hbal : ∀ (b : B) (x : MSplitAlg P n) (m : M), F (b • x) m = F x (b • m) := by
    intro b x m
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hF, hF, MvPolynomial.algebraMap_eq, hC]
  refine ⟨TensorProduct.liftAddHom F hbal, ?_, ?_⟩
  · intro m
    rw [TensorProduct.liftAddHom_tmul, ← map_one (Ideal.Quotient.mk (mSplitIdeal P n)), hF, h1]
  · intro t z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m =>
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul, TensorProduct.liftAddHom_tmul, smul_eq_mul,
        ← map_mul, hF, hF, hL]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.NuChar
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep

open Polynomial in
private theorem roots_smul_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (u : ℂ) (hu : u ≠ 0) :
    (u • M).charpoly = ((M.charpoly.roots.map (· * u)).map fun α => X - C α).prod := by
  have hM := (IsAlgClosed.splits M.charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic M)
  have hc : Multiset.card M.charpoly.roots = Fintype.card ι := by
    rw [← (IsAlgClosed.splits M.charpoly).natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim]
  refine Polynomial.funext fun x => ?_
  have h1 := congrArg (eval (x / u)) hM
  rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at h1
  have e : Matrix.scalar ι x - u • M = u • (Matrix.scalar ι (x / u) - M) := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
      field_simp
    · simp [Matrix.diagonal_apply_ne _ hab]
  rw [Matrix.eval_charpoly, e, Matrix.det_smul, h1, eval_multiset_prod, Multiset.map_map,
    Multiset.map_map, ← hc, ← Multiset.prod_replicate, ← Multiset.map_const, ← Multiset.prod_map_mul]
  refine congrArg _ (Multiset.map_congr rfl fun α _ => ?_)
  simp
  field_simp

open Polynomial in
private theorem charpoly_smul_prod {V ι : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Fintype ι]
    (f : Module.End ℂ V) (u : ℂ) (hu : u ≠ 0) (c : ι → ℂ) (h : f.charpoly = ∏ i, (X - C (c i))) :
    (u • f).charpoly = ∏ i, (X - C (c i * u)) := by
  have hr : f.charpoly.roots = Finset.univ.val.map c := by
    rw [h, Finset.prod_eq_multiset_prod, ← roots_multiset_prod_X_sub_C (Finset.univ.val.map c), Multiset.map_map]
    rfl
  rw [← LinearMap.charpoly_toMatrix (u • f) (Module.finBasis ℂ V), map_smul, roots_smul_matrix _ _ hu,
    LinearMap.charpoly_toMatrix, hr, Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

private theorem absPow_neg_nat (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i : ℕ) (x : kˣ) : (absPow k (-(i : ℂ)) x : ℂ) = (resCard k : ℂ) ^ ((i : ℤ) * ord k x) := by
  rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, Complex.cpow_neg, Complex.cpow_natCast]
  push_cast
  rw [← zpow_natCast, ← zpow_mul, ← zpow_neg]
  congr 1
  ring

theorem UpperTheory.V.Pa.Lev.nuChar :
    ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (a : Weil hB →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin hB a) (ε : EpsFamily Bq) (rc : IrrGL (w.adicCompletion E) → WD hB), Laws a ha ε rc → ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (ψ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ) (χ : (Fin n → (w.adicCompletion E)ˣ) →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → torusChar ψ = χ * ((deltaHalf (w.adicCompletion E) fun _ : Fin n => Unit).comp (leviTorus (w.adicCompletion E) (Fin n)).toMonoidHom) → IsSubquotient σ.ρ (prinSeries ψ) → ∀ g : Weil hB, (rc (algNorm σ)).charPol g = ∏ i : Fin n, (Polynomial.X - Polynomial.C ((resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a g)) * (χ (Pi.mulSingle i (a g)) : ℂ))) := by
  intro l _ E Ω _ _ _ _ _ Bq w hB _ a ha ε rc L n σ ψ χ hψ hχ hs g
  have H := UpperTheory.V.AlgebraTools.jqRec E Ω Bq w hB a ha ε rc L n ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ ψ hψ hs g
  rw [algNorm, IrrGL.nu, L.tw_eq]
  change (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol g = _ at H
  generalize rc (IrrGL.of σ.ρ σ.smooth σ.irred) = x at H ⊢
  obtain ⟨m, b, rfl⟩ := x.exists_rep
  rw [WD.charPol_mk] at H
  rw [WD.lpTwist_mk, WD.charPol_mk, WDRep.twist_ρ, charpoly_smul_prod _ _ (Units.ne_zero _) _ H]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  have h1 : torusChar ψ (Pi.mulSingle i (a g)) = ψ i (a g) := by
    rw [torusChar_apply, Finset.prod_eq_single i, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  have hd : ∀ (t : Fin n → (w.adicCompletion E)ˣ) j,
      Matrix.GeneralLinearGroup.det (leviTorus (w.adicCompletion E) (Fin n) t j) = t j := fun t =>
    congrFun ((leviTorus (w.adicCompletion E) (Fin n)).left_inv t)
  have h2 : deltaHalf (w.adicCompletion E) (fun _ : Fin n => Unit)
      (leviTorus (w.adicCompletion E) (Fin n) (Pi.mulSingle i (a g))) =
      absPow (w.adicCompletion E) ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) (a g) := by
    rw [deltaHalf_apply, Finset.prod_eq_single i, hd, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [hd, Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  rw [← h1, hχ, ← absPow_neg_nat]
  have h3 : -((i : ℕ) : ℂ) = (modExp (fun _ : Fin n => Unit) i : ℂ) / 2 + (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) := by
    rw [modExp_fin _ (fun _ => by simp)]
    push_cast
    ring
  rw [h3, absPow_add]
  simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
  erw [h2]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.PairRel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem prod_conj {K : Type} [Field K] {n : ℕ} (V : Matrix (Fin n) (Fin n) K) :
    ∀ (m : ℕ) (F : Fin m → Matrix (Fin n) (Fin n) K) (d : Fin m → Fin n → K),
      (∀ k, F k * V = V * Matrix.diagonal (d k)) →
      (List.ofFn F).prod * V = V * Matrix.diagonal (fun j => ∏ k, d k j) := by
  intro m
  induction m with
  | zero => intro F d _; simp
  | succ m ih =>
    intro F d h
    rw [List.ofFn_succ, List.prod_cons, mul_assoc, ih (fun k => F k.succ) (fun k => d k.succ) (fun k => h _),
      ← mul_assoc, h 0, mul_assoc, Matrix.diagonal_mul_diagonal]
    simp only [Fin.prod_univ_succ]

private theorem exists_diag {K : Type} [Field K] {n : ℕ} (P : Matrix (Fin n) (Fin n) K) (α : Fin n → K)
    (hα : Function.Injective α)
    (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i))) :
    ∃ V : Matrix (Fin n) (Fin n) K, IsUnit V ∧ P * V = V * Matrix.diagonal α :=
  _root_.UpperTheory.Reformulated.B.ExistsDiagonalization.exists_diag P α hα hP

theorem UpperTheory.V.Pa.Lev.pairRel :
    ∀ (K : Type) [Field K] (n : ℕ) (P T : Matrix (Fin n) (Fin n) K) (α β : Fin n → K), Function.Injective α → P * T = T * P → P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i)) → (∀ a : ℕ, (P ^ a * T).trace = ∑ i, α i ^ a * β i) → ∀ i, (List.ofFn fun i' => if i' = i then 1 else P - α i' • (1 : Matrix (Fin n) (Fin n) K)).prod * (T - β i • (1 : Matrix (Fin n) (Fin n) K)) = 0 := by
  intro K _ n P T α β hα hc hP htr i
  obtain ⟨V, hV, hPV⟩ := exists_diag P α hα hP
  obtain ⟨V', h1, h2⟩ := isUnit_iff_exists.1 hV
  obtain ⟨S, hS⟩ : ∃ S, S = V' * T * V := ⟨_, rfl⟩
  have hTV : T * V = V * S := by
    rw [hS, ← mul_assoc, ← mul_assoc, h1, one_mul]
  have hSD : Matrix.diagonal α * S = S * Matrix.diagonal α := by
    refine hV.mul_left_cancel ?_
    rw [← mul_assoc, ← hPV, mul_assoc, ← hTV, ← mul_assoc, hc, mul_assoc, hPV, ← mul_assoc, hTV,
      mul_assoc]
  have hSd : S = Matrix.diagonal (fun j => S j j) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.diagonal_apply_ne _ hab]
      have := congrFun (congrFun hSD a) b
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm] at this
      by_contra h0
      exact hab (hα (mul_left_cancel₀ h0 this))
  have hpow : ∀ a : ℕ, P ^ a * V = V * Matrix.diagonal α ^ a := by
    intro a
    induction a with
    | zero => simp
    | succ a ih => rw [pow_succ, mul_assoc, hPV, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have htr' : ∀ a : ℕ, ∑ j, α j ^ a * S j j = ∑ j, α j ^ a * β j := by
    intro a
    rw [← htr a]
    have e : P ^ a * T = V * (Matrix.diagonal α ^ a * S) * V' := by
      rw [← mul_assoc, ← hpow, mul_assoc (P ^ a), ← hTV, mul_assoc, mul_assoc, h1, mul_one]
    rw [e, Matrix.trace_mul_cycle, h2, one_mul, Matrix.diagonal_pow]
    simp [Matrix.trace, Matrix.diagonal_mul]
  have hβ : (fun j => S j j - β j) = 0 := by
    refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hα (fun a => ?_)
    simp only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
    simpa only [mul_comm] using htr' a
  have hSβ : S = Matrix.diagonal β := by
    rw [hSd]
    congr 1
    ext j
    exact sub_eq_zero.1 (congrFun hβ j)
  have hE := prod_conj V n
    (fun i' => if i' = i then 1 else P - α i' • (1 : Matrix (Fin n) (Fin n) K))
    (fun k j => if k = i then 1 else α j - α k) (by
      intro k
      by_cases hk : k = i
      · simp [hk]
      · simp only [if_neg hk]
        rw [sub_mul, hPV, smul_mul_assoc, one_mul]
        ext a b
        simp [Matrix.mul_diagonal, mul_sub, mul_comm])
  have hT : (T - β i • (1 : Matrix (Fin n) (Fin n) K)) * V = V * Matrix.diagonal (fun j => β j - β i) := by
    rw [sub_mul, hTV, hSβ, smul_mul_assoc, one_mul]
    ext a b
    simp [Matrix.mul_diagonal, mul_sub, mul_comm]
  refine hV.mul_right_cancel ?_
  rw [mul_assoc, hT, ← mul_assoc, hE, mul_assoc, Matrix.diagonal_mul_diagonal, zero_mul]
  have : (fun j => (∏ k, if k = i then 1 else α j - α k) * (β j - β i)) = fun _ => (0 : K) := by
    ext j
    by_cases hj : j = i
    · simp [hj]
    · rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), zero_mul]
  rw [this, Matrix.diagonal_zero, mul_zero]
end

