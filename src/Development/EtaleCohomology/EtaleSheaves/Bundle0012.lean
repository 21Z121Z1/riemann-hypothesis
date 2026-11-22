import Development.EtaleCohomology.EtaleSheaves.Bundle0005
import Development.EtaleCohomology.EtaleSheaves.LineHigh

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPicCut
section
noncomputable section
open nonZeroDivisors

namespace LateralTheory.E.LeafPicCut

def sel (B : Type) [CommRing B] [IsDomain B] (q : ℕ) : Subgroup (FractionRing B)ˣ :=
  (powMonoidHom q : (FractionalIdeal B⁰ (FractionRing B))ˣ →* _).range.comap (toPrincipalIdeal B (FractionRing B))

abbrev selPow (B : Type) [CommRing B] [IsDomain B] (q : ℕ) : Subgroup (sel B q) :=
  (powMonoidHom q : (FractionRing B)ˣ →* (FractionRing B)ˣ).range.subgroupOf (sel B q)

abbrev selQ (B : Type) [CommRing B] [IsDomain B] (q : ℕ) : Type := sel B q ⧸ selPow B q

def LeafTorsPrime : Prop := ∀ (G : Type) [CommGroup G] (q : ℕ), q ≠ 0 →
  (∀ p : ℕ, p.Prime → p ∣ q → Finite {x : G // x ^ p = 1}) → Finite {x : G // x ^ q = 1}

def LeafSelPic : Prop := ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (q : ℕ) [NeZero q],
  Finite (selQ B q) → Finite {c : ClassGroup B // c ^ q = 1}

def LeafBound : Prop := ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ∃ V : Submodule k (FractionRing B), FiniteDimensional k V ∧
  ∀ f ∈ sel B q, ∃ g ∈ sel B q, (g : FractionRing B) ∈ V ∧ ∃ u : (FractionRing B)ˣ, f = g * u ^ q

def LeafRigid : Prop := LateralTheory.E.E4.Hyps → ∀ (q : ℕ) [NeZero q], q.Prime → ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B]
  [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) →
  ∀ V : Submodule k (FractionRing B), FiniteDimensional k V →
  Set.Finite ((QuotientGroup.mk : sel B q → selQ B q) '' {f | ((f : (FractionRing B)ˣ) : FractionRing B) ∈ V})

theorem goal_of (hT : LeafTorsPrime) (hS : LeafSelPic) (hB : LeafBound) (hR : LeafRigid) : LateralTheory.E.E4.LeafPic := by
  intro hH q _ k B _ _ _ _ _ _ hq
  have key : Finite {c : ClassGroup B // c ^ q = 1} := by
    apply hT (ClassGroup B) q (NeZero.ne q)
    intro p hp hpq
    have : NeZero p := ⟨hp.ne_zero⟩
    have hpk : IsUnit (p : k) := by
      obtain ⟨m, rfl⟩ := hpq
      push_cast at hq
      exact isUnit_of_mul_isUnit_left hq
    apply hS B p
    obtain ⟨V, hV, hb⟩ := hB p k B
    have hfin := hR hH p hp k B hpk V hV
    refine Set.finite_univ_iff.mp (hfin.subset ?_)
    rintro x -
    induction x using QuotientGroup.induction_on with
    | H f =>
      obtain ⟨g, hg, hgV, u, hu⟩ := hb f f.2
      refine ⟨⟨g, hg⟩, hgV, ?_⟩
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      refine ⟨u, ?_⟩
      simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv, hu]
      group
  exact Finite.of_equiv _ (@Equiv.subtypeEquiv _ _ (fun c : ClassGroup B => c ^ q = 1) (fun c : CommRing.Pic B => c ^ q = 1)
    (ClassGroup.equivPic B).toEquiv (fun c => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow, MulEquiv.map_eq_one_iff]))

end LateralTheory.E.LeafPicCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafProjPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafProjPf

theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f _ _ x) := by
  subst hn; subst hi; rfl

theorem cast_zero (q : ℕ) {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    Ht.cast hn hi (0 : Ht q E n i) = 0 := by
  subst hn; subst hi; rfl

theorem pull_cpow (hN : DivisorNaturality) (q : ℕ) [NeZero q] {E E' : Spc} (f : E ⟶ E') (hE : Inv q E') (x : Ht q E' 2 1) (k : ℕ) :
    pull _ f _ _ (cpow q x k) = cpow q (pull _ f _ _ x) k := by
  induction k with
  | zero => rw [cpow_zero, cpow_zero, pull_cast, (hN q).2.1 f hE]
  | succ k ih => rw [cpow_succ, cpow_succ, pull_cast, (hN q).1, ih]

theorem inv_pb (q : ℕ) {E : Spc} {P : Spc} (g : P ⟶ E) (hE : Inv q E) : Inv q P :=
  fun U ⟨x⟩ => hE U ⟨LateralTheory.E.t_E6Cut.sxMap g x⟩

def Phi (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (n i : ℤ) :
    (∀ j : Fin N, Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))) → Ht q (pullback V (PGL.pr N)) n i := fun a =>
  ∑ j : Fin N, ((cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ (a j))
      (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)).cast (by ring) (by ring) : Ht q _ n i)

theorem LeafProj_of (hNat : LateralTheory.E.t_E6Cut.LeafNat) : LateralTheory.E.t_E6Cut.LeafProj := by
  intro a1 a5 a7 a9 a10 d1 q _ i E N V V' hE s hs1 hs2
  have hN : DivisorNaturality := hNat a1 a5 a7 a9 a10
  have hP' : Inv q (pullback V' (PGL.pr (N + 1))) := inv_pb q (pullback.fst _ _) hE
  have term : ∀ {m k m' k' : ℤ} (x : Ht q E m k) (j : ℕ) (hn : m + 2 * (j : ℤ) = m') (hi : k + (j : ℤ) = k'),
      pull _ s _ _ (Ht.cast hn hi (cup q (pull _ (pullback.fst V' (PGL.pr (N + 1))) _ _ x)
        (cpow q (c1 q (pullback.snd V' (PGL.pr (N + 1)) ≫ PGL.line (N + 1))) j))) =
      Ht.cast hn hi (cup q (pull _ (pullback.fst V (PGL.pr N)) _ _ x)
        (cpow q (c1 q (pullback.snd V (PGL.pr N) ≫ PGL.line N)) j)) := by
    intro m k m' k' x j hn hi
    rw [pull_cast, (hN q).1, ← pull_comp, hs1, pull_cpow hN q s hP', (hN q).2.2.1 s _ hP', hs2]
  have key : ∀ n : ℤ, n < 2 * N → Function.Bijective (pull _ s (tw q i) n) := by
    intro n hn
    have hsub : Subsingleton (Ht q E (n - 2 * ((Fin.last N : Fin (N + 1)) : ℕ)) (i - ((Fin.last N : Fin (N + 1)) : ℕ))) :=
      (a9 (ZMod q) (tw q _)).1 E _ (by simp only [Fin.val_last]; omega)
    have h' : Function.Bijective (Phi q V' n i) := d1 q V' hE n i
    have h : Function.Bijective (Phi q V n i) := d1 q V hE n i
    have hcomp : ∀ a, pull _ s _ _ (Phi q V' n i a) = Phi q V n i (fun j => a j.castSucc) := by
      intro a
      simp only [Phi, map_sum]
      rw [Fin.sum_univ_castSucc]
      have hl : a (Fin.last N) = 0 := Subsingleton.elim _ _
      rw [hl, map_zero, map_zero, AddMonoidHom.zero_apply, cast_zero, map_zero, add_zero]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact term _ _ _ _
    have hres : ∀ a b : (∀ j : Fin (N + 1), Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))),
        (fun j : Fin N => a j.castSucc) = (fun j : Fin N => b j.castSucc) → a = b := by
      intro a b hab
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · exact Subsingleton.elim _ _
      · exact congrFun hab j
    constructor
    · intro x y hxy
      obtain ⟨a, rfl⟩ := h'.2 x
      obtain ⟨b, rfl⟩ := h'.2 y
      rw [hcomp, hcomp] at hxy
      rw [hres a b (h.1 hxy)]
    · intro y
      obtain ⟨b, rfl⟩ := h.2 y
      refine ⟨Phi q V' n i (Fin.lastCases (motive := fun j : Fin (N + 1) => Ht q E (n - 2 * (j : ℕ)) (i - (j : ℕ))) 0
        (fun j => b j)), ?_⟩
      rw [hcomp]
      congr 1
      funext j
      exact Fin.lastCases_castSucc _
  intro n
  exact ⟨fun hn => key n (by omega), fun hn => (key n hn).1⟩

end LateralTheory.E.LeafProjPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafPtPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

theorem eq_generic_of_dim {X : Scheme.{0}} [IsIntegral X] (hd : topologicalKrullDim X ≤ 0) (x : X) :
    x = genericPoint X := by
  have hmax := (Order.krullDim_nonpos_iff_forall_isMax).1 hd
  let S : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let T : TopologicalSpace.IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hST : S ≤ T := fun _ _ => Set.mem_univ _
  have hTS : T ≤ S := hmax S hST
  have h1 : genericPoint X ⤳ x := genericPoint_specializes x
  have h2 : x ⤳ genericPoint X := by
    rw [specializes_iff_mem_closure]
    exact hTS (Set.mem_univ (genericPoint X))
  exact (h2.antisymm h1).eq

theorem subsingleton_of_dim {X : Scheme.{0}} [IsIntegral X] (hd : topologicalKrullDim X ≤ 0) : Subsingleton X :=
  ⟨fun x y => (eq_generic_of_dim hd x).trans (eq_generic_of_dim hd y).symm⟩

theorem leafPtIso (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p]
    (hd : topologicalKrullDim X ≤ 0) : IsIso p := by
  haveI := subsingleton_of_dim hd
  haveI : IsAffine X := inferInstance
  let F : CommRingCat.of k ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso _).inv ≫ p.appTop
  have hfin : p.appTop.hom.Finite := finite_appTop_of_universallyClosed k p
  have hFfin : F.hom.Finite := by
    simp only [F, CommRingCat.hom_comp]
    exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.symm.surjective)
  letI : Algebra k Γ(X, ⊤) := F.hom.toAlgebra
  haveI : Algebra.IsIntegral k Γ(X, ⊤) := ⟨fun a => hFfin.to_isIntegral a⟩
  have hb : Function.Bijective F.hom := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))
  haveI : IsIso F := (ConcreteCategory.isIso_iff_bijective F).2 hb
  haveI : IsIso p.appTop := by
    have : p.appTop = (Scheme.ΓSpecIso _).hom ≫ F := by simp [F]
    rw [this]; infer_instance
  have e : p = X.isoSpec.hom ≫ Spec.map p.appTop ≫ (Sp k).isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [e]; infer_instance

theorem sh_of_isAlgClosed (k : Type) [Field k] [IsAlgClosed k] : SH k := by
  refine ⟨inferInstance, ?_⟩
  have hb : Function.Bijective (IsLocalRing.residue k) := by
    exact ⟨(IsLocalRing.residue k).injective, IsLocalRing.residue_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField k) := IsAlgClosed.of_ringEquiv k _ (RingEquiv.ofBijective _ hb)
  infer_instance

theorem finite_sp (hH : Hyps) (h0 : H0TwistOverClosedField) (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k] (hq : IsUnit (q : k))
    (n i : ℤ) : Finite (Ht q (sch.obj (Sp k)) n i) := by
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · haveI := (hH.2.2.2.2.2.2.2.1 (ZMod q) (tw q i)).1 (sch.obj (Sp k)) n hn
    exact Finite.of_subsingleton
  · exact (h0 hH q k hq i).1
  · haveI := hH.2.2.2.2.2.2.2.2.2.2.2.1 (ZMod q) k (sh_of_isAlgClosed k) (tw q i) n hn
    exact Finite.of_subsingleton

theorem LeafPt_of (h0 : H0TwistOverClosedField) : LeafPt := by
  intro hH q _ k _ _ hq X _ p _ hd n i
  have := leafPtIso k p hd
  haveI := finite_sp hH h0 q k hq n i
  refine Finite.of_injective (pull (ZMod q) (sch.map (inv p)) (tw q i) n) ?_
  intro x y hxy
  have key : ∀ z : Ht q (sch.obj X) n i,
      pull (ZMod q) (sch.map p) (tw q i) n (pull (ZMod q) (sch.map (inv p)) (tw q i) n z) = z := by
    intro z
    rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [← key x, ← key y, hxy]

end LateralTheory.E.E4
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafRelPf
section
noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafRelPf

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] {A B : CochainComplex C ℤ} (φ : A ⟶ B)
  [HomologicalComplex.HasHomotopyCofiber φ] (M : CochainComplex C ℤ)

lemma δ_desc' {m n : ℤ} (α : Cochain A M m) (β : Cochain B M n) (h : m + 1 = n) (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (mappingCone.descCochain φ α β h) = mappingCone.descCochain φ
      (δ m n α + n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (δ n n' β) (by omega) := by
  rw [mappingCone.δ_descCochain _ _ _ _ _ hn']; rfl

lemma desc_eq_iff {m n : ℤ} (h : m + 1 = n) (α α' : Cochain A M m) (β β' : Cochain B M n) :
    mappingCone.descCochain φ α β h = mappingCone.descCochain φ α' β' h ↔ α = α' ∧ β = β' := by
  constructor
  · intro e
    have h1 := congrArg (fun w => (mappingCone.inl φ).comp w (show -1 + n = m by omega)) e
    have h2 := congrArg (fun w => (Cochain.ofHom (mappingCone.inr φ)).comp w (zero_add n)) e
    simp only [mappingCone.inl_descCochain, mappingCone.inr_descCochain] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma desc_zero {m n : ℤ} (h : m + 1 = n) :
    mappingCone.descCochain φ (0 : Cochain A M m) (0 : Cochain B M n) h = 0 := by
  simp [mappingCone.descCochain]

lemma desc_eq_zero_iff {m n : ℤ} (h : m + 1 = n) (α : Cochain A M m) (β : Cochain B M n) :
    mappingCone.descCochain φ α β h = 0 ↔ α = 0 ∧ β = 0 := by
  rw [← desc_zero φ M h, desc_eq_iff]

lemma eq_desc {p d : ℤ} (hp : p + 1 = d) (y : Cochain (mappingCone φ) M d) :
    y = mappingCone.descCochain φ ((mappingCone.inl φ).comp y (show -1 + d = p by omega))
      ((Cochain.ofHom (mappingCone.inr φ)).comp y (zero_add d)) hp := by
  rw [mappingCone.ext_cochain_from_iff φ p d hp]
  simp

lemma core_inj (d p : ℤ) (hp : p + 1 = d)
    (hE : ∀ z : Cochain (mappingCone φ) M d, δ d (d + 1) z = 0 → ∃ y : Cochain (mappingCone φ) M p, δ p d y = z)
    (b : Cochain B M d) (hb : δ d (d + 1) b = 0) (g : Cochain A M p)
    (hg : δ p d g = (Cochain.ofHom φ).comp b (zero_add d)) : ∃ y : Cochain B M p, δ p d y = b := by
  obtain ⟨y, hy⟩ := hE (mappingCone.descCochain φ (-((d + 1).negOnePow • g)) b hp) (by
    rw [δ_desc' _ _ _ _ _ _ rfl]
    simp [hb, hg, desc_zero])
  refine ⟨(Cochain.ofHom (mappingCone.inr φ)).comp y (zero_add p), ?_⟩
  rw [δ_ofHom_comp, hy, mappingCone.inr_descCochain]

lemma core_surj (d p : ℤ) (hp : p + 1 = d)
    (hE : ∀ z : Cochain (mappingCone φ) M (d + 1), δ (d + 1) (d + 1 + 1) z = 0 →
      ∃ y : Cochain (mappingCone φ) M d, δ d (d + 1) y = z)
    (a : Cochain A M d) (ha : δ d (d + 1) a = 0) : ∃ (c : Cochain B M d) (e : Cochain A M p),
      δ d (d + 1) c = 0 ∧ a = (Cochain.ofHom φ).comp c (zero_add d) + δ p d e := by
  obtain ⟨y, hy⟩ := hE (mappingCone.descCochain φ a 0 rfl) (by
    rw [δ_desc' _ _ _ _ _ _ rfl]
    simp [ha, desc_zero])
  rw [eq_desc φ M hp y, δ_desc' _ _ _ _ _ _ rfl, desc_eq_iff] at hy
  obtain ⟨h1, h2⟩ := hy
  refine ⟨(d + 1).negOnePow • (Cochain.ofHom (mappingCone.inr φ)).comp y (zero_add d),
    (mappingCone.inl φ).comp y (show -1 + d = p by omega), by simp [h2], ?_⟩
  rw [← h1, Cochain.comp_units_smul, add_comm]

lemma core_E (p k : ℤ) (hk : k + 1 = p)
    (hI : ∀ b : Cochain B M (p + 1), δ (p + 1) (p + 1 + 1) b = 0 → ∀ g : Cochain A M p,
      δ p (p + 1) g = (Cochain.ofHom φ).comp b (zero_add _) → ∃ y : Cochain B M p, δ p (p + 1) y = b)
    (hS : ∀ a : Cochain A M p, δ p (p + 1) a = 0 → ∃ (c : Cochain B M p) (e : Cochain A M k),
      δ p (p + 1) c = 0 ∧ a = (Cochain.ofHom φ).comp c (zero_add p) + δ k p e)
    (z : Cochain (mappingCone φ) M (p + 1)) (hz : δ (p + 1) (p + 1 + 1) z = 0) :
    ∃ y : Cochain (mappingCone φ) M p, δ p (p + 1) y = z := by
  have hzd := eq_desc φ M (rfl : p + 1 = p + 1) z
  set α := (mappingCone.inl φ).comp z (show -1 + (p + 1) = p by omega)
  set β := (Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add (p + 1))
  rw [hzd, δ_desc' _ _ _ _ _ _ rfl, desc_eq_zero_iff] at hz
  obtain ⟨hX, hY⟩ := hz
  obtain ⟨β'', hβ''⟩ := hI β hY (-((p + 1 + 1).negOnePow • α)) (by
    rw [δ_neg, δ_units_smul, eq_neg_of_add_eq_zero_left hX, smul_neg, neg_neg, smul_smul,
      Int.units_mul_self, one_smul])
  obtain ⟨c, e, hc, he⟩ := hS (α + (p + 1 + 1).negOnePow • (Cochain.ofHom φ).comp β'' (zero_add p)) (by
    rw [δ_add, δ_units_smul, δ_ofHom_comp, hβ'', hX])
  refine ⟨mappingCone.descCochain φ e (β'' + (p + 1).negOnePow • c) hk, ?_⟩
  rw [δ_desc' _ _ _ _ _ _ rfl, hzd, desc_eq_iff]
  constructor
  · rw [Cochain.comp_add, Cochain.comp_units_smul, smul_add, smul_smul, Int.units_mul_self, one_smul]
    have he' : δ k p e = α + (p + 1 + 1).negOnePow • (Cochain.ofHom φ).comp β'' (zero_add p) -
        (Cochain.ofHom φ).comp c (zero_add p) := by rw [he]; abel
    rw [he', Int.negOnePow_succ (p + 1)]
    simp only [Units.neg_smul]
    abel
  · rw [δ_add, δ_units_smul, hβ'', hc, smul_zero, add_zero]

lemma sub_iff (X : CochainComplex C ℤ) (n m : ℤ) (hm : m + 1 = n) :
    Subsingleton (CohomologyClass X M n) ↔
      ∀ z : Cochain X M n, δ n (n + 1) z = 0 → ∃ y : Cochain X M m, δ m n y = z := by
  constructor
  · intro hs z hz
    have h0 := Subsingleton.elim (CohomologyClass.mk (Cocycle.mk z (n + 1) rfl hz)) 0
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm] at h0
    simpa using h0
  · intro h
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := x.mk_surjective
    obtain ⟨y, rfl⟩ := y.mk_surjective
    rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ m hm]
    exact h _ (Cocycle.δ_eq_zero _ _)

omit [HomologicalComplex.HasHomotopyCofiber φ] in
lemma inj_iff (n m : ℤ) (hm : m + 1 = n) :
    Function.Injective (cpre (Cocycle.ofHom φ) M n n (zero_add n)) ↔
      ∀ b : Cochain B M n, δ n (n + 1) b = 0 → ∀ g : Cochain A M m,
        δ m n g = (Cochain.ofHom φ).comp b (zero_add n) → ∃ y : Cochain B M m, δ m n y = b := by
  constructor
  · intro hi b hb g hg
    have h0 : cpre (Cocycle.ofHom φ) M n n (zero_add n) (CohomologyClass.mk (Cocycle.mk b (n + 1) rfl hb)) = 0 := by
      rw [cpre_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
      exact ⟨g, by simp [zcomp, hg]⟩
    have h1 := (injective_iff_map_eq_zero _).1 hi _ h0
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm] at h1
    simpa using h1
  · intro h
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨b, rfl⟩ := x.mk_surjective
    rw [cpre_mk, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm] at hx
    obtain ⟨g, hg⟩ := hx
    obtain ⟨y, hy⟩ := h b.1 (Cocycle.δ_eq_zero _ _) g (by simpa [zcomp] using hg)
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ m hm]
    exact ⟨y, hy⟩

omit [HomologicalComplex.HasHomotopyCofiber φ] in
lemma surj_iff (n m : ℤ) (hm : m + 1 = n) :
    Function.Surjective (cpre (Cocycle.ofHom φ) M n n (zero_add n)) ↔
      ∀ a : Cochain A M n, δ n (n + 1) a = 0 → ∃ (c : Cochain B M n) (e : Cochain A M m),
        δ n (n + 1) c = 0 ∧ a = (Cochain.ofHom φ).comp c (zero_add n) + δ m n e := by
  constructor
  · intro hs a ha
    obtain ⟨x, hx⟩ := hs (CohomologyClass.mk (Cocycle.mk a (n + 1) rfl ha))
    obtain ⟨c, rfl⟩ := x.mk_surjective
    rw [cpre_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ m hm] at hx
    obtain ⟨e, he⟩ := hx
    refine ⟨c.1, -e, Cocycle.δ_eq_zero _ _, ?_⟩
    simp [zcomp] at he
    rw [δ_neg, he]
    abel
  · intro h x
    obtain ⟨a, rfl⟩ := x.mk_surjective
    obtain ⟨c, e, hc, he⟩ := h a.1 (Cocycle.δ_eq_zero _ _)
    refine ⟨CohomologyClass.mk (Cocycle.mk c (n + 1) rfl hc), ?_⟩
    rw [cpre_mk, ← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ m hm]
    refine ⟨-e, ?_⟩
    simp [zcomp, he]

theorem conn_iff (c : ℤ) :
    (∀ n : ℤ, (n < c - 1 → Function.Bijective (cpre (Cocycle.ofHom φ) M n n (zero_add n))) ∧
      (n < c → Function.Injective (cpre (Cocycle.ofHom φ) M n n (zero_add n)))) ↔
      ∀ n < c, Subsingleton (CohomologyClass (mappingCone φ) M n) := by
  constructor
  · intro h n hn
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    rw [sub_iff M _ (p + 1) p rfl]
    exact core_E φ M p (p - 1) (by omega) ((inj_iff φ M (p + 1) p rfl).1 ((h (p + 1)).2 hn))
      ((surj_iff φ M p (p - 1) (by omega)).1 ((h p).1 (by omega)).2)
  · intro h n
    have hinj : n < c → Function.Injective (cpre (Cocycle.ofHom φ) M n n (zero_add n)) := fun hn =>
      (inj_iff φ M n (n - 1) (by omega)).2 (core_inj φ M n (n - 1) (by omega)
        ((sub_iff M _ n (n - 1) (by omega)).1 (h n hn)))
    refine ⟨fun hn => ⟨hinj (by omega), ?_⟩, hinj⟩
    exact (surj_iff φ M n (n - 1) (by omega)).2 (core_surj φ M n (n - 1) (by omega)
      ((sub_iff M _ (n + 1) n rfl).1 (h (n + 1) (by omega))))

end LateralTheory.E.LeafRelPf

theorem LateralTheory.E.t_E6Cut.LeafRel_of : LateralTheory.E.t_E6Cut.LeafRel := by
  intro R _ F c K L f
  exact LateralTheory.E.LeafRelPf.conn_iff f (res R F) c
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfA
section
namespace LateralTheory.E.E4

def LeafUnitsFG : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], Group.FG (Bˣ ⧸ (Units.map (algebraMap k B).toMonoidHom).range)

theorem units_range_le_pow (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] :
    (Units.map (algebraMap k B).toMonoidHom).range ≤ (powMonoidHom q : Bˣ →* Bˣ).range := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : k) (Nat.pos_of_ne_zero (NeZero.ne q))
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne q)] at hz
    exact a.ne_zero hz.symm
  refine ⟨Units.map (algebraMap k B).toMonoidHom (Units.mk0 z hz0), ?_⟩
  ext
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0]
  rw [← map_pow, hz]

theorem LeafUnits_of (hFG : LeafUnitsFG) : LeafUnits := by
  intro q _ k B _ _ _ _ _ _
  have hle := units_range_le_pow q k B
  let N := (powMonoidHom q : Bˣ →* Bˣ).range
  let M := (Units.map (algebraMap k B).toMonoidHom).range
  have : Group.FG (Bˣ ⧸ M) := hFG k B
  let φ : Bˣ ⧸ M →* Bˣ ⧸ N := QuotientGroup.map M N (MonoidHom.id _) hle
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨QuotientGroup.mk u, rfl⟩
  have : Group.FG (Bˣ ⧸ N) := Group.fg_of_surjective hφ
  apply CommGroup.finite_of_fg_isMulTorsion
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨q, Nat.pos_of_ne_zero (NeZero.ne q), ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact ⟨u, rfl⟩

end LateralTheory.E.E4
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LineOneCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineOneCut

abbrev fib {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Scheme.{0} :=
  pullback p (cpt A)

def fibMap {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    fib (ι ≫ p) ⟶ fib p :=
  pullback.map (ι ≫ p) (cpt A) p (cpt A) ι (𝟙 _) (𝟙 _) (by simp) (by simp)

def Charts : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p →
  ∃ (U V : Scheme.{0}) (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ ∧ IsOpenImmersion ι₂ ∧ IsAffine U ∧ IsAffine V ∧
    Set.range ι₁ ∪ Set.range ι₂ = Set.univ

def FibCover : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A))
  (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  IsOpenImmersion (fibMap p ι₁) ∧ IsOpenImmersion (fibMap p ι₂) ∧ Set.range (fibMap p ι₁) ∪ Set.range (fibMap p ι₂) = Set.univ

def ChartAcyc : Prop := Hyp → ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] {Z U : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z), IsOpenImmersion ι → IsAffine U → AICSch Z → IsUnit (q : A) →
  Acyc q (sch.obj (fib (ι ≫ p)))

def ChartSurj : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∀ {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z),
  IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → IsAffine U → IsAffine V → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  ∀ w : Ht q (sch.obj (pullback (fibMap p ι₁) (fibMap p ι₂))) 0 i, ∃ a b,
    w = pull _ (sch.map (pullback.fst (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 a -
      pull _ (sch.map (pullback.snd (fibMap p ι₁) (fibMap p ι₂))) (tw q i) 0 b

theorem goal_of (hMV : MV) (hC : Charts) (hF : FibCover) (hA : ChartAcyc) (hS : ChartSurj) : LineOne := by
  intro H q i A _ _ hSH hq Z p hp hZ
  obtain ⟨U, V, ι₁, ι₂, h1, h2, hU, hV, hcov⟩ := hC A p hp
  obtain ⟨hf1, hf2, hfcov⟩ := hF A p ι₁ ι₂ h1 h2 hcov
  obtain ⟨δ, hex, -⟩ := hMV H (ZMod q) (tw q i)
  have e := hex (fibMap p ι₁) (fibMap p ι₂) hfcov 0
  have aU := hA H q A p ι₁ h1 hU hZ hq
  have aV := hA H q A p ι₂ h2 hV hZ hq
  have key : ∀ x : Ht q (sch.obj (fib p)) 1 i, x = 0 := by
    intro x
    have s1 := aU 1 i one_pos
    have s2 := aV 1 i one_pos
    obtain ⟨w, hw⟩ := (e.2.2 x).1 ⟨@Subsingleton.elim _ s1 _ _, @Subsingleton.elim _ s2 _ _⟩
    obtain ⟨a, b, hab⟩ := hS H q i A hSH hq p hp hZ ι₁ ι₂ h1 h2 hU hV hcov w
    rw [← hw]
    exact (e.2.1 w).2 ⟨a, b, hab⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end LateralTheory.E.LineOneCut
end
end

