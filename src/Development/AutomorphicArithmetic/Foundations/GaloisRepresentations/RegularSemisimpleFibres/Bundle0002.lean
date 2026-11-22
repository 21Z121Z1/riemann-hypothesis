import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PFinSec
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.finSec :
    FinSec := by
  intro H U V _ _ _ _ _ _ ρ σ f hf hsurj
  haveI := Fintype.ofFinite H
  obtain ⟨s₀, hs₀⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  have hs₀' : ∀ y, f (s₀ y) = y := fun y => LinearMap.congr_fun hs₀ y
  have hc : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hρ : ∀ (a b : H) (x : U), ρ (a * b) x = ρ a (ρ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hσ : ∀ (a b : H) (x : V), σ (a * b) x = σ a (σ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hσ1 : ∀ x : V, σ 1 x = x := fun x => by
    rw [map_one]; rfl
  refine ⟨(Fintype.card H : ℂ)⁻¹ • ∑ g : H, (ρ g) ∘ₗ s₀ ∘ₗ (σ g⁻¹), ?_, ?_⟩
  · intro h x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv]
    rw [← hρ, mul_inv_cancel_left, hσ]
  · intro x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    have : ∀ g : H, f (ρ g (s₀ (σ g⁻¹ x))) = x := fun g => by
      rw [hf, hs₀', ← hσ, mul_inv_cancel, hσ1]
    simp only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PFrobL
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hcL_cons_of {F : Type} [Field F] (p : Σ m : ℕ, GL (Fin m) F → ℂ)
    (Y : List (Σ m : ℕ, GL (Fin m) F → ℂ)) (b : ℕ) (h : (Y.map Sigma.fst).sum = b) (n : ℕ) :
    hcL (p :: Y) n = hc p.1 b p.2 (hcL Y b) n := by
  subst h
  exact hcL_cons p Y n

private theorem collapse {G X Z : Type} [Finite G] [Finite X] [Finite Z]
    (A : G → Prop) (B : Z → Prop) (I : G → Prop) (tl : G → X) (br : G → Z)
    (hA : ∀ p, A p ↔ I p ∧ B (br p))
    (u : X → ℂ) (v : Subtype B → ℂ) (T : G → ℂ) (w : Subtype A → ℂ)
    (hw : ∀ p (hp : A p) (hp' : B (br p)), w ⟨p, hp⟩ = u (tl p) * v ⟨br p, hp'⟩) :
    ∑ᶠ x, u x * ∑ᶠ p' : Subtype B, v p' * (∑ᶠ p : G, if I p ∧ tl p = x ∧ br p = p'.1 then T p else 0) =
      ∑ᶠ p : Subtype A, w p * T p := by
  classical
  haveI := Fintype.ofFinite G
  haveI := Fintype.ofFinite X
  haveI := Fintype.ofFinite Z
  have key : ∀ p : G, (∑ x, ∑ p' : Subtype B,
      u x * (v p' * if I p ∧ tl p = x ∧ br p = p'.1 then T p else 0)) =
      if h : A p then w ⟨p, h⟩ * T p else 0 := by
    intro p
    by_cases hI : I p
    · by_cases hB : B (br p)
      · have hAp : A p := (hA p).2 ⟨hI, hB⟩
        rw [dif_pos hAp, hw p hAp hB, Fintype.sum_eq_single (tl p), Fintype.sum_eq_single ⟨br p, hB⟩]
        · simp [hI]
          ring
        · intro q hq
          rw [if_neg]
          · simp
          · rintro ⟨_, _, h⟩
            exact hq (Subtype.ext h.symm)
        · intro x hx
          apply Finset.sum_eq_zero
          intro q _
          rw [if_neg]
          · simp
          · rintro ⟨_, h, _⟩
            exact hx h.symm
      · rw [dif_neg (fun h => hB ((hA p).1 h).2)]
        apply Finset.sum_eq_zero
        intro x _
        apply Finset.sum_eq_zero
        intro q _
        rw [if_neg]
        · simp
        · rintro ⟨_, _, h⟩
          exact hB (h ▸ q.2)
    · rw [dif_neg (fun h => hI ((hA p).1 h).1)]
      simp [hI]
  simp only [finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm, Finset.sum_comm,
    Finset.sum_congr rfl fun p _ => key p, ← Fintype.sum_subtype_add_sum_subtype A,
    Finset.sum_congr rfl fun p _ => dif_pos p.2,
    Finset.sum_congr rfl (fun (p : {p // ¬A p}) _ => dif_neg p.2), Finset.sum_const_zero, add_zero]

theorem UpperTheory.Gal.InertialTypesAlt.frobL :
    FrobTwo → ResCl → ParCons → FrobL := by
  intro hF2 hRes hPar F _ _ s
  induction s with
  | zero =>
    intro d n hd
    refine ⟨1, one_ne_zero, fun Y T _ => ?_⟩
    have hn : n = 0 := by rw [← hd]; simp
    subst hn
    have hall : ∀ g : GL (Fin 0) F, g ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks d hd) :=
      fun g => GlobalTheory.SmGL.mem_parab_iff.2 fun a => a.elim0
    simp only [List.ofFn_zero, hcL_nil, star_one, one_mul, Fin.prod_univ_zero]
    exact (finsum_comp_equiv (Equiv.subtypeUnivEquiv hall)).symm
  | succ s ih =>
    intro d n hd
    have hn : n = d 0 + ∑ i : Fin s, d i.succ := by rw [← hd, Fin.sum_univ_succ]
    obtain ⟨c1, hc1, h1⟩ := hF2 F (d 0) (∑ i : Fin s, d i.succ) n hn
    obtain ⟨c2, hc2, h2⟩ := ih (fun i => d i.succ) _ rfl
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, fun Y T hT => ?_⟩
    have htail : (List.map Sigma.fst (List.ofFn fun i : Fin s =>
        (⟨d i.succ, Y i.succ⟩ : Σ m : ℕ, GL (Fin m) F → ℂ))).sum = ∑ i : Fin s, d i.succ := by
      simp [List.sum_ofFn]
    rw [List.ofFn_succ, hcL_cons_of _ _ _ htail, h1 _ _ T hT]
    have h2' := fun x => h2 (fun i => Y i.succ) _ (hRes F _ _ n hn T hT x)
    rw [finsum_congr fun x => by rw [h2' x, mul_left_comm], ← mul_finsum, ← mul_assoc]
    clear h1 h2 h2' ih htail hF2 hRes
    refine congrArg (c1 * c2 * ·) ?_
    unfold UpperTheory.Gal.InertialTypesAlt.resT
    have hc := collapse (fun p => p ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks d hd))
      (fun z => z ∈ GlobalTheory.SmGL.parab F (GlobalTheory.SmGL.stdBlocks (fun i => d i.succ) rfl))
      (GlobalTheory.Shin.InPar (d 0)) (GlobalTheory.Shin.tlG (d 0)) (GlobalTheory.Shin.brG (d 0) _)
      (fun p => (hPar F s n d hd _ rfl p).1) (fun x => star (Y 0 x))
      (fun p' => star (∏ i, Y i.succ (GlobalTheory.SmGL.leviProj F (GlobalTheory.SmGL.stdBlocks (fun i => d i.succ) rfl) p' i)))
      T (fun p => star (∏ i, Y i (GlobalTheory.SmGL.leviProj F (GlobalTheory.SmGL.stdBlocks d hd) p i))) (by
        intro p hp hp'
        obtain ⟨h0, hs⟩ := (hPar F s n d hd _ rfl p).2 hp hp'
        rw [Fin.prod_univ_succ, h0, star_mul']
        congr 2
        exact Finset.prod_congr rfl fun i _ => by rw [hs i])
    convert hc
    rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PFrobTwo
section
noncomputable section

open GlobalTheory.Shin
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt

private theorem gal_id {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) :
    gal (RingHom.id F) n y = y := by
  ext i j
  simp [gal]

private theorem inPar_one {F : Type} [Field F] (a n : ℕ) : InPar a (1 : GL (Fin n) F) := by
  intro i j hj hi
  have hij : i ≠ j := by
    rintro rfl
    omega
  simp [Matrix.one_apply_ne hij]

theorem frobTwo : FrobTwo := by
  intro F _ _ a b n _
  haveI : Fintype (GL (Fin n) F) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin a) F) := Fintype.ofFinite _
  haveI : Fintype (GL (Fin b) F) := Fintype.ofFinite _
  have hN : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) ≠ 0 := by
    haveI : Nonempty {p : GL (Fin n) F // InPar a p} := ⟨⟨1, inPar_one a n⟩⟩
    exact_mod_cast (Nat.card_pos (α := {p : GL (Fin n) F // InPar a p})).ne'
  have hG : (Fintype.card (GL (Fin n) F) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine ⟨star ((Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹) * (Fintype.card (GL (Fin n) F) : ℂ),
    mul_ne_zero (star_ne_zero.2 (inv_ne_zero hN)) hG, ?_⟩
  intro α β T hT
  set w : GL (Fin n) F → ℂ := fun p =>
    if InPar a p then star (α (tlG a p) * β (brG a b p)) * T p else 0 with hw
  have hleft : ∑ᶠ g, star (hc a b α β n g) * T g =
      star ((Nat.card {p : GL (Fin n) F // InPar a p} : ℂ)⁻¹) *
        ((Fintype.card (GL (Fin n) F) : ℂ) * ∑ p, w p) := by
    have hy : ∀ y : GL (Fin n) F,
        ∑ g : GL (Fin n) F, star (if InPar a (y⁻¹ * (g * y)) then
          α (tlG a (y⁻¹ * (g * y))) * β (brG a b (y⁻¹ * (g * y))) else 0) * T g = ∑ p, w p := by
      intro y
      refine Fintype.sum_equiv ((Equiv.mulRight y).trans (Equiv.mulLeft y⁻¹)) _ _ fun g => ?_
      have hTg : T (y⁻¹ * (g * y)) = T g := by
        rw [← mul_assoc]
        exact hT g y
      simp only [Equiv.trans_apply, Equiv.coe_mulLeft, Equiv.coe_mulRight, hw, hTg]
      split_ifs <;> simp
    rw [finsum_eq_sum_of_fintype]
    simp only [hc, hcTw, gal_id, finsum_eq_sum_of_fintype, star_mul', star_sum, mul_assoc,
      ← Finset.mul_sum]
    congr 1
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [hy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hright : ∑ᶠ x, star (α x) * ∑ᶠ y, star (β y) * resT a b T x y = ∑ p, w p := by
    have key : ∀ p : GL (Fin n) F, ∑ x : GL (Fin a) F, ∑ y : GL (Fin b) F,
        star (α x) * (star (β y) *
          if InPar a p ∧ tlG a p = x ∧ brG a b p = y then T p else 0) = w p := by
      intro p
      rw [Finset.sum_eq_single (tlG a p), Finset.sum_eq_single (brG a b p)]
      · by_cases h : InPar a p <;> simp [hw, h, star_mul', mul_assoc]
      · intro y _ hy
        simp [Ne.symm hy]
      · simp
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    simp only [resT, finsum_eq_sum_of_fintype, Finset.mul_sum]
    rw [← Finset.sum_congr rfl fun p _ => key p]
    refine (Finset.sum_congr rfl fun x _ => Finset.sum_comm).trans ?_
    exact Finset.sum_comm
  rw [hleft, hright, mul_assoc]

end UpperTheory.Gal.InertialTypesAlt
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PKillsNil
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem frob_ne_one {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hp : (Module.finrank F F').Prime) (hs : ∀ z, s z = z ^ Nat.card F) :
    s ≠ 1 := by
  rintro rfl
  haveI : Finite F := Finite.of_injective (algebraMap F F') (algebraMap F F').injective
  haveI : Fintype F' := Fintype.ofFinite F'
  have hcard : Nat.card F' = Nat.card F ^ Module.finrank F F' := Module.natCard_eq_pow_finrank
  have hq : 1 < Nat.card F := Finite.one_lt_card
  generalize Nat.card F = q at hs hq hcard
  have hne : (X ^ q - X : F'[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F' hq
  have hdeg : (X ^ q - X : F'[X]).natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq F' hq
  have hsub : (Finset.univ : Finset F') ⊆ (X ^ q - X : F'[X]).roots.toFinset := by
    intro z _
    rw [Multiset.mem_toFinset, mem_roots hne]
    have := hs z
    simp only [AlgEquiv.one_apply] at this
    simp [IsRoot, ← this]
  have h1 : Nat.card F' ≤ q := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ Multiset.card (X ^ q - X : F'[X]).roots := Multiset.toFinset_card_le _
      _ ≤ (X ^ q - X : F'[X]).natDegree := card_roots' _
      _ = q := hdeg
  rw [hcard] at h1
  have h2 : q ^ 2 ≤ q ^ Module.finrank F F' := Nat.pow_le_pow_right (by omega) hp.two_le
  nlinarith

theorem UpperTheory.Gal.InertialTypesAlt.killsNil :
    KillsAll → KillsOn fun a => a.D = [] := by
  intro h F F' _ _ _ _ s hp hs ι θ hθ a hD hok hq
  obtain ⟨q, D, L⟩ := a
  simp only at hD hq
  subst hD
  subst hq
  have key := h F F' s hp (frob_ne_one s hp hs) ι θ hθ L (fun p hp' => hok.2.2 p hp') (deg L) rfl
  have hrk : (⟨Nat.card F, [], L⟩ : Lbl).rk = deg L := by
    have h0 : GlobalTheory.Shin.deg ([] : List (ℕ × ℕ)) = 0 := rfl
    simp [Lbl.rk, h0]
  rw [hrk]
  simpa [Lbl.lift, JD_nil] using key
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLblIso
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

section SlopeTestRemainingChoices

open GlobalTheory.Parabolic (mem_fixed)

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private def intEquiv (i : k ≃+* K) (hi : ∀ x : k, valuation K (i x) ≤ 1 ↔ valuation k x ≤ 1) : 𝒪[k] ≃+* 𝒪[K] where
  toFun x := ⟨i x, (hi x).2 x.2⟩
  invFun y := ⟨i.symm y, (hi _).1 (by rw [i.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

private def resEquiv (i₀ : 𝒪[k] ≃+* 𝒪[K]) : 𝓀[k] ≃+* 𝓀[K] := IsLocalRing.ResidueField.mapEquiv i₀

private def glEquiv {F F' : Type} [Field F] [Field F'] (r : F ≃+* F') (n : ℕ) : GL (Fin n) F ≃ GL (Fin n) F' where
  toFun := Matrix.GeneralLinearGroup.map r.toRingHom
  invFun := Matrix.GeneralLinearGroup.map r.symm.toRingHom
  left_inv g := by ext a b; simp
  right_inv g := by ext a b; simp

variable (i : k ≃+* K) (hi : ∀ x : k, valuation K (i x) ≤ 1 ↔ valuation k x ≤ 1) {n : ℕ}

include hi

private theorem map_alg (u : GL (Fin n) 𝒪[k]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) =
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[K] K)
        (Matrix.GeneralLinearGroup.map (intEquiv i hi).toRingHom u) := by
  ext a b; rfl

private theorem map_mem_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    Matrix.GeneralLinearGroup.map i.toRingHom g ∈ KO K (Fin n) := by
  obtain ⟨u, rfl⟩ := hg
  exact ⟨_, (map_alg i hi u).symm⟩

private theorem exists_KO {y : GL (Fin n) K} (hy : y ∈ KO K (Fin n)) :
    ∃ g ∈ KO k (Fin n), Matrix.GeneralLinearGroup.map i.toRingHom g = y := by
  obtain ⟨u, rfl⟩ := hy
  refine ⟨_, ⟨Matrix.GeneralLinearGroup.map (intEquiv i hi).symm.toRingHom u, rfl⟩, ?_⟩
  rw [map_alg i hi]
  congr 1
  ext a b
  simp

private theorem red_map (g : KO k (Fin n)) :
    redK K (Fin n) ⟨Matrix.GeneralLinearGroup.map i.toRingHom g, map_mem_KO i hi g.2⟩ =
      Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom (redK k (Fin n) g) := by
  ext a b
  rw [redK_apply]
  show _ = resEquiv (intEquiv i hi) ((redK k (Fin n) g : Matrix (Fin n) (Fin n) 𝓀[k]) a b)
  rw [redK_apply]
  rfl

private theorem map_mem_KOne_iff {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    Matrix.GeneralLinearGroup.map i.toRingHom g ∈ KOne K (Fin n) ↔ g ∈ KOne k (Fin n) := by
  rw [← redK_eq_one_iff ⟨g, hg⟩, ← redK_eq_one_iff ⟨_, map_mem_KO i hi hg⟩, red_map i hi ⟨g, hg⟩]
  constructor
  · intro h
    have := congrArg (glEquiv (resEquiv (intEquiv i hi)) n).symm h
    rw [show Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom (redK k (Fin n) ⟨g, hg⟩) =
      glEquiv (resEquiv (intEquiv i hi)) n (redK k (Fin n) ⟨g, hg⟩) from rfl, Equiv.symm_apply_apply] at this
    rw [this]
    exact map_one (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).symm.toRingHom)
  · intro h
    rw [h, map_one]

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GL (Fin n) k) V) (P : Representation ℂ (GL (Fin n) K) W) (e : V ≃ₗ[ℂ] W)
  (he : ∀ g x, e (π g x) = P (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x))

include he in
private theorem map_fixed :
    (fixed π (KOne k (Fin n))).map (e : V →ₗ[ℂ] W) = fixed P (KOne K (Fin n)) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_fixed.2 fun y hy => ?_
    obtain ⟨g, hg, rfl⟩ := exists_KO i hi (GlobalTheory.StepData.KOne_le_KO hy)
    show P _ (e x) = e x
    rw [← he, mem_fixed.1 hx g ((map_mem_KOne_iff i hi hg).1 hy)]
  · intro hw
    refine ⟨e.symm w, mem_fixed.2 fun g hg => ?_, by simp⟩
    apply e.injective
    rw [he, e.apply_symm_apply,
      mem_fixed.1 hw _ ((map_mem_KOne_iff i hi (GlobalTheory.StepData.KOne_le_KO hg)).2 hg)]

private def fixEquiv : fixed π (KOne k (Fin n)) ≃ₗ[ℂ] fixed P (KOne K (Fin n)) :=
  e.ofSubmodules _ _ (map_fixed i hi π P e he)

private theorem fixEquiv_level (γ : GL (Fin n) 𝓀[k]) (x : fixed π (KOne k (Fin n))) :
    fixEquiv i hi π P e he (levelZero π γ x) =
      levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ)
        (fixEquiv i hi π P e he x) := by
  obtain ⟨g, rfl⟩ := redK_surjective γ
  rw [← red_map i hi g]
  apply Subtype.ext
  rw [levelZero_apply]
  show e (levelZero π (redK k (Fin n) g) x : V) = P _ (e x)
  rw [levelZero_apply, he]

include he in
private theorem trace_level (γ : GL (Fin n) 𝓀[k]) :
    LinearMap.trace ℂ _ (levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ)) =
      LinearMap.trace ℂ _ (levelZero π γ) := by
  have h : levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ) =
      (fixEquiv i hi π P e he).conj (levelZero π γ) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := (fixEquiv i hi π P e he).surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, fixEquiv_level]
  rw [h, LinearMap.trace_conj']

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.InertialTypesAlt.lblIso :
    JDIso → LblIso := by
  intro hJ k _ _ _ _ K _ _ _ _ i hi j hj θ N V W _ _ _ _ π P e he a ha
  obtain ⟨hok, hq, hn, hm⟩ := ha
  have hjr : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (resEquiv (intEquiv i hi) x) := by
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    exact hj y (intEquiv i hi y) rfl
  refine ⟨hok, hq.trans (Nat.card_congr (resEquiv (intEquiv i hi)).toEquiv), hn, ?_⟩
  unfold Meets at hm ⊢
  rw [← finsum_comp_equiv (glEquiv (resEquiv (intEquiv i hi)) N)]
  have key : ∀ γ : GL (Fin N) 𝓀[k],
      star (JD θ a.D a.L N (glEquiv (resEquiv (intEquiv i hi)) N γ)) *
          LinearMap.trace ℂ _ (levelZero P (glEquiv (resEquiv (intEquiv i hi)) N γ)) =
        star (JD (θ.comp j.toMonoidHom) a.D a.L N γ) * LinearMap.trace ℂ _ (levelZero π γ) := by
    intro γ
    rw [← hJ _ _ (resEquiv (intEquiv i hi)) j hjr θ a.D a.L N γ, ← trace_level i hi π P e he γ]
    rfl
  rw [finsum_congr key]
  exact hm
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLeRank
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem gcd_step {m m' c l : ℕ} (hm : 0 < m) (hl : l.Prime) (h : m' * Nat.gcd m c = m) :
    (if l ∣ m' then m' / l else m') * Nat.gcd m (c * l) = m := by
  have hg : 0 < Nat.gcd m c := Nat.gcd_pos_of_pos_left _ hm
  obtain ⟨m₁, c₁, hco, hm₁, hc₁⟩ := Nat.exists_coprime m c
  have hmm : m₁ = m' := by
    apply Nat.eq_of_mul_eq_mul_right hg
    rw [← hm₁, h]
  subst hmm
  set g := Nat.gcd m c with hgdef
  have hgcd : Nat.gcd m (c * l) = Nat.gcd m₁ l * g := by
    have e : c * l = (c₁ * l) * g := by
      rw [hc₁]; ring
    rw [e]
    conv_lhs => rw [hm₁]
    rw [Nat.gcd_mul_right, Nat.Coprime.gcd_mul_left_cancel_right l hco.symm]
  rw [hgcd]
  split_ifs with hd
  · rw [Nat.gcd_eq_right hd, ← mul_assoc, Nat.div_mul_cancel hd]
    exact h
  · have : Nat.gcd m₁ l = 1 := ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).symm
    rw [this, one_mul]
    exact h

theorem UpperTheory.Gal.InertialTypesAlt.leRank :
    LiftOk → LeRank := by
  intro hOk a b ha hab
  have key : b.Ok ∧ ∃ c : ℕ, 0 < c ∧ b.q = a.q ^ c ∧
      ∀ p ∈ b.L, ∃ r ∈ a.L, p.1 * Nat.gcd r.1 c = r.1 := by
    induction hab with
    | refl =>
      refine ⟨ha, 1, Nat.one_pos, (pow_one _).symm, fun p hp => ⟨p, hp, ?_⟩⟩
      rw [Nat.gcd_one_right, mul_one]
    | @tail b' b'' _ hs ih =>
      obtain ⟨hb, c, hc, hq, hL⟩ := ih
      obtain ⟨l, hl, rfl⟩ := hs
      refine ⟨(hOk b' l hl hb).1, c * l, Nat.mul_pos hc hl.pos, ?_, ?_⟩
      · change b'.q ^ l = _
        rw [hq, pow_mul]
      · intro p hp
        have hp' : p ∈ liftAll b'.q l b'.L := hp
        unfold liftAll at hp'
        obtain ⟨s, hs, hps⟩ := List.mem_flatMap.1 hp'
        obtain ⟨r, hr, hsr⟩ := hL s hs
        refine ⟨r, hr, ?_⟩
        have hm : 0 < r.1 := (ha.2.2 r hr).1
        have hstep := gcd_step (l := l) hm hl hsr
        have hp1 : p.1 = if l ∣ s.1 then s.1 / l else s.1 := by
          split_ifs at hps ⊢ with hd
          · simp only [liftL, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map] at hps
            obtain ⟨i, -, rfl⟩ := hps
            rfl
          · simp only [List.mem_singleton] at hps
            rw [hps]
        rw [hp1]
        exact hstep
  exact key.2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLiftsFix
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.liftsFix :
    LiftsFix := by
  intro E Ω _ _ _ n X Y h x
  induction h with
  | refl => exact ⟨x, rfl⟩
  | @tail B C _ hs ih =>
    obtain ⟨y, hy⟩ := ih
    obtain ⟨i₁, i₂, -⟩ := hs
    refine ⟨algebraMap B.K C.K y, ?_⟩
    rw [← hy]
    exact (IsScalarTower.algebraMap_apply B.K C.K Ω y).symm
end

