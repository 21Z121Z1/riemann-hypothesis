import Development.EtaleCohomology.EtaleSheaves.Bundle0010
import Development.EtaleCohomology.EtaleSheaves.Bundle0012
import Development.EtaleCohomology.EtaleSheaves.Bundle0007
import Development.EtaleCohomology.EtaleSheaves.Bundle0006
import Development.EtaleCohomology.EtaleSheaves.Bundle0015
import Development.EtaleCohomology.EtaleSheaves.InstCommRingR

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChainTower
section
noncomputable section
open CategoryTheory Limits Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.E.LeafRelPf

namespace LateralTheory.E.ChainTower

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C]

def Rl {A B : CochainComplex C ℤ} (φ : A ⟶ B) (M : CochainComplex C ℤ) (k m n : ℤ) : Prop :=
  ∀ (α : Cochain A M m) (β : Cochain B M n), δ n (n + 1) β = 0 → δ m n α = (Cochain.ofHom φ).comp β (zero_add n) →
    ∃ (a : Cochain A M k) (b : Cochain B M m), δ m n b = β ∧ δ k m a + (Cochain.ofHom φ).comp b (zero_add m) = α

def El {X Y : C} (g : X ⟶ Y) (M : CochainComplex C ℤ) (k m n : ℤ) : Prop :=
  ∀ (α : X ⟶ M.X m) (β : Y ⟶ M.X n), β ≫ M.d n (n + 1) = 0 → α ≫ M.d m n = g ≫ β →
    ∃ (a : X ⟶ M.X k) (b : Y ⟶ M.X m), b ≫ M.d m n = β ∧ a ≫ M.d k m + g ≫ b = α

theorem sub_iff_Rl {A B : CochainComplex C ℤ} (φ : A ⟶ B) [HomologicalComplex.HasHomotopyCofiber φ]
    (M : CochainComplex C ℤ) (k m n : ℤ) (hk : k + 1 = m) (hm : m + 1 = n) :
    Subsingleton (CohomologyClass (mappingCone φ) M n) ↔ Rl φ M k m n := by
  rw [sub_iff M _ n m hm]
  constructor
  · intro h α β hβ hα
    obtain ⟨y, hy⟩ := h (mappingCone.descCochain φ α (n.negOnePow • β) hm) (by
      rw [δ_desc' _ _ _ _ _ _ rfl, desc_eq_zero_iff]
      refine ⟨?_, by rw [δ_units_smul, hβ, smul_zero]⟩
      rw [hα, Cochain.comp_units_smul, smul_smul, Int.negOnePow_succ, neg_mul, Int.units_mul_self]
      simp)
    rw [eq_desc φ M hk y, δ_desc' _ _ _ _ _ _ hm, desc_eq_iff] at hy
    obtain ⟨h1, h2⟩ := hy
    refine ⟨(mappingCone.inl φ).comp y (show -1 + m = k by omega),
      n.negOnePow • (Cochain.ofHom (mappingCone.inr φ)).comp y (zero_add m), ?_, ?_⟩
    · rw [δ_units_smul, h2, smul_smul, Int.units_mul_self, one_smul]
    · rw [Cochain.comp_units_smul]; exact h1
  · intro h z hz
    have hzd := eq_desc φ M hm z
    set α := (mappingCone.inl φ).comp z (show -1 + n = m by omega)
    set β := (Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add n)
    rw [hzd, δ_desc' _ _ _ _ _ _ rfl, desc_eq_zero_iff] at hz
    obtain ⟨hX, hY⟩ := hz
    obtain ⟨a, b, h1, h2⟩ := h α (n.negOnePow • β) (by rw [δ_units_smul, hY, smul_zero]) (by
      rw [eq_neg_of_add_eq_zero_left hX, Cochain.comp_units_smul, Int.negOnePow_succ]
      simp)
    refine ⟨mappingCone.descCochain φ a (n.negOnePow • b) hk, ?_⟩
    rw [δ_desc' _ _ _ _ _ _ hm, hzd, desc_eq_iff]
    constructor
    · rw [Cochain.comp_units_smul, smul_smul, Int.units_mul_self, one_smul, h2]
    · rw [δ_units_smul, h1, smul_smul, Int.units_mul_self, one_smul]

theorem El_iso {X Y X' Y' : C} {g : X ⟶ Y} {g' : X' ⟶ Y'} (e : X' ≅ X) (e' : Y' ≅ Y) (w : e.hom ≫ g = g' ≫ e'.hom)
    (M : CochainComplex C ℤ) (k m n : ℤ) (h : El g M k m n) : El g' M k m n := by
  intro α β hβ hα
  have w' : g ≫ e'.inv = e.inv ≫ g' := by
    rw [Iso.comp_inv_eq, Category.assoc, ← w, Iso.inv_hom_id_assoc]
  obtain ⟨a, b, h1, h2⟩ := h (e.inv ≫ α) (e'.inv ≫ β) (by simp [hβ]) (by
    rw [Category.assoc, hα, ← Category.assoc, ← w', Category.assoc])
  refine ⟨e.hom ≫ a, e'.hom ≫ b, by simp [h1], ?_⟩
  rw [← Category.assoc g', ← w, Category.assoc, Category.assoc, ← Preadditive.comp_add, h2, Iso.hom_inv_id_assoc]

theorem δ_top {A M : CochainComplex C ℤ} {m n : ℤ} (hm : m + 1 = n) (z : Cochain A M m) (s e d : ℤ) (he : s + m = e)
    (hd : s + n = d) (hz : ∀ q (h : s + 1 + m = q), z.v (s + 1) q h = 0 ∨ A.d s (s + 1) = 0) :
    (δ m n z).v s d hd = z.v s e he ≫ M.d e d := by
  rw [δ_v m n hm z s d hd e (s + 1) (by omega) rfl]
  rcases hz d (by omega) with h | h <;> rw [h] <;> simp

theorem comp_ofHom_v {A B M : CochainComplex C ℤ} (φ : A ⟶ B) {n : ℤ} (z : Cochain B M n) (p q : ℤ) (h : p + n = q) :
    ((Cochain.ofHom φ).comp z (zero_add n)).v p q h = φ.f p ≫ z.v p q h := by
  rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]

def V {A M : CochainComplex C ℤ} {n : ℤ} (s : ℤ) (z : Cochain A M n) : Prop :=
  ∀ p q (h : p + n = q), s < p → z.v p q h = 0

theorem V_single {A M : CochainComplex C ℤ} {s e : ℤ} (g : A.X s ⟶ M.X e) (n : ℤ) : V s (Cochain.single g n) :=
  fun _ _ _ hp => Cochain.single_v_eq_zero _ _ _ _ _ (by omega)

theorem V_δ {A M : CochainComplex C ℤ} {m n : ℤ} (hm : m + 1 = n) (s : ℤ) (z : Cochain A M m) (hz : V s z) :
    V s (δ m n z) := by
  intro p q h hp
  rw [δ_top hm z p (p + m) q rfl h (fun _ _ => Or.inl (hz _ _ _ (by omega))), hz _ _ _ hp, zero_comp]

def Rs {A B : CochainComplex C ℤ} (φ : A ⟶ B) (M : CochainComplex C ℤ) (k m n s : ℤ) : Prop :=
  ∀ (α : Cochain A M m) (β : Cochain B M n), V s α → V s β → δ n (n + 1) β = 0 →
    δ m n α = (Cochain.ofHom φ).comp β (zero_add n) →
    ∃ (a : Cochain A M k) (b : Cochain B M m), δ m n b = β ∧ δ k m a + (Cochain.ofHom φ).comp b (zero_add m) = α

theorem step {A B : CochainComplex C ℤ} (φ : A ⟶ B) (M : CochainComplex C ℤ) (k m n s : ℤ) (hk : k + 1 = m)
    (hm : m + 1 = n) (hE : El (φ.f s) M (s + k) (s + m) (s + n)) (h : Rs φ M k m n (s - 1)) : Rs φ M k m n s := by
  intro α β vα vβ hβ hα
  obtain ⟨a, b, h1, h2⟩ := hE (α.v s _ rfl) (β.v s _ rfl) (by
      rw [← δ_top rfl β s _ (s + n + 1) rfl (by omega) (fun _ _ => Or.inl (vβ _ _ _ (by omega))), hβ]; rfl) (by
      rw [← δ_top hm α s _ _ rfl rfl (fun _ _ => Or.inl (vα _ _ _ (by omega))), hα, comp_ofHom_v])
  have va := V_single a k
  have vb := V_single b m
  obtain ⟨a', b', h3, h4⟩ := h (α - (δ k m (Cochain.single a k) + (Cochain.ofHom φ).comp (Cochain.single b m) (zero_add m)))
    (β - δ m n (Cochain.single b m)) (by
      intro p q hpq hp
      rw [Cochain.sub_v, Cochain.add_v, comp_ofHom_v]
      rcases lt_or_eq_of_le (show s ≤ p by omega) with h' | h'
      · rw [vα _ _ _ h', V_δ hk s _ va _ _ _ h', vb _ _ _ h']; simp
      · subst h' hpq
        rw [δ_top hk _ s _ _ rfl rfl (fun _ _ => Or.inl (va _ _ _ (by omega))), Cochain.single_v, Cochain.single_v, h2,
          sub_self]) (by
      intro p q hpq hp
      rw [Cochain.sub_v]
      rcases lt_or_eq_of_le (show s ≤ p by omega) with h' | h'
      · rw [vβ _ _ _ h', V_δ hm s _ vb _ _ _ h']; simp
      · subst h' hpq
        rw [δ_top hm _ s _ _ rfl rfl (fun _ _ => Or.inl (vb _ _ _ (by omega))), Cochain.single_v, h1, sub_self])
    (by rw [δ_sub, δ_δ, hβ, sub_zero])
    (by rw [δ_sub, δ_add, δ_δ, zero_add, δ_ofHom_comp, hα, Cochain.comp_sub])
  refine ⟨a' + Cochain.single a k, b' + Cochain.single b m, ?_, ?_⟩
  · rw [δ_add, h3]; abel
  · rw [δ_add, Cochain.comp_add, add_add_add_comm, h4]; abel

theorem base {A B : CochainComplex C ℤ} (φ : A ⟶ B) (M : CochainComplex C ℤ) (hM : ∀ q < 0, IsZero (M.X q))
    (k m n s : ℤ) (hm : m + 1 = n) (hs : s + n < 0) : Rs φ M k m n s := by
  intro α β vα vβ _ _
  have hα : α = 0 := Cochain.ext _ _ (fun p q hpq => by
    rcases lt_or_ge s p with h | h
    · exact vα p q hpq h
    · exact (hM q (by omega)).eq_of_tgt _ _)
  have hβ : β = 0 := Cochain.ext _ _ (fun p q hpq => by
    rcases lt_or_ge s p with h | h
    · exact vβ p q hpq h
    · exact (hM q (by omega)).eq_of_tgt _ _)
  exact ⟨0, 0, by simp [hβ], by simp [hα]⟩

theorem tower {A B : CochainComplex C ℤ} (φ : A ⟶ B) (M : CochainComplex C ℤ) (hM : ∀ q < 0, IsZero (M.X q))
    (hA : ∀ q, 0 < q → IsZero (A.X q)) (hB : ∀ q, 0 < q → IsZero (B.X q)) (k m n : ℤ) (hk : k + 1 = m) (hm : m + 1 = n)
    (hE : ∀ p : ℕ, El (φ.f (-(p : ℤ))) M (-(p : ℤ) + k) (-(p : ℤ) + m) (-(p : ℤ) + n)) : Rl φ M k m n := by
  have ind : ∀ j p : ℕ, n < p + j → Rs φ M k m n (-(p : ℤ)) := by
    intro j
    induction j with
    | zero => intro p hp; exact base φ M hM k m n _ hm (by push_cast at hp; omega)
    | succ j ih =>
      intro p hp
      have h2 := ih (p + 1) (by push_cast at hp ⊢; omega)
      have e : (-((p + 1 : ℕ) : ℤ)) = -(p : ℤ) - 1 := by push_cast; ring
      rw [e] at h2
      exact step φ M k m n _ hk hm (hE p) h2
  intro α β
  exact ind (n.toNat + 1) 0 (by omega) α β (fun p q _ hp => (hA p (by simpa using hp)).eq_of_src _ _)
    (fun p q _ hp => (hB p (by simpa using hp)).eq_of_src _ _)

theorem El_of_single [HasZeroObject C] {X Y : C} (g : X ⟶ Y) (M : CochainComplex C ℤ) (k m n : ℤ) (hk : k + 1 = m)
    (hm : m + 1 = n) (h : Rl ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map g) M k m n) : El g M k m n := by
  refine El_iso (g := ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map g).f 0)
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).symm
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 Y).symm
    (by simp [HomologicalComplex.single_map_f_self]) M k m n ?_
  intro α β hβ hα
  have hz : ∀ (Z : C) (p : ℤ), p ≠ 0 → IsZero (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Z).X p) :=
    fun Z p hp => HomologicalComplex.isZero_single_obj_X _ _ _ _ hp
  have hd : ∀ (Z : C), ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj Z).d 0 (0 + 1) = 0 :=
    fun Z => (hz Z _ (by norm_num)).eq_of_tgt _ _
  obtain ⟨a, b, h1, h2⟩ := h (Cochain.single α m) (Cochain.single β n) (Cochain.ext _ _ (fun p q hpq => by
      by_cases hp : p = 0
      · subst hp
        obtain rfl : q = n + 1 := by omega
        rw [δ_top rfl _ 0 n _ (zero_add n) hpq (fun _ _ => Or.inr (hd Y)), Cochain.single_v, hβ]; rfl
      · exact (hz Y p hp).eq_of_src _ _)) (Cochain.ext _ _ (fun p q hpq => by
      by_cases hp : p = 0
      · subst hp
        obtain rfl : n = q := by omega
        rw [δ_top hm _ 0 m _ (zero_add m) hpq (fun _ _ => Or.inr (hd X)), Cochain.single_v, comp_ofHom_v,
          Cochain.single_v, hα]
      · exact (hz X p hp).eq_of_src _ _))
  refine ⟨a.v 0 k (zero_add k), b.v 0 m (zero_add m), ?_, ?_⟩
  · rw [← δ_top hm b 0 m n (zero_add m) (zero_add n) (fun _ _ => Or.inr (hd Y)), h1, Cochain.single_v]
  · rw [← δ_top hk a 0 k m (zero_add k) (zero_add m) (fun _ _ => Or.inr (hd X)), ← comp_ofHom_v, ← Cochain.add_v, h2,
      Cochain.single_v]

theorem chains_zero (R : Type) [CommRing R] (U : Spc) (i : ℤ) (hi : 0 < i) : IsZero (((chains R).obj U).X i) := by
  change IsZero ((((chainsN R).obj U).extend ComplexShape.embeddingDownNat).X i)
  apply HomologicalComplex.isZero_extend_X
  intro j hj
  have : -(j : ℤ) = i := hj
  omega

theorem res_zero (R : Type) [CommRing R] (F : Shv R) (q : ℤ) (hq : q < 0) : IsZero ((res R F).X q) := by
  have : (res R F).IsStrictlyGE 0 := by unfold res; infer_instance
  exact CochainComplex.isZero_of_isStrictlyGE _ 0 q (by omega)

theorem chains_nat (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p))) =
      ((chains R).map f).f (-(p : ℤ)) ≫ (chainsXIso R E' p).hom := by
  have := HomologicalComplex.extendMap_f ((chainsN R).map f) ComplexShape.embeddingDownNat (i := p) (i' := -(p : ℤ)) rfl
  change _ = (HomologicalComplex.extendMap ((chainsN R).map f) ComplexShape.embeddingDownNat).f (-(p : ℤ)) ≫ _
  rw [this]
  unfold chainsXIso
  erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem tower_body (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E')
    (h : ∀ p : ℕ, ∀ n : ℤ, n < c - p →
      Subsingleton (HK R (LateralTheory.E.LeafLevelPf.cone0 R (f.app (op (SimplexCategory.mk p)))) F n))
    (n : ℤ) (hn : n < c) : Subsingleton (HK R (mappingCone ((chains R).map f)) F n) := by
  refine (sub_iff_Rl _ (res R F) (n - 2) (n - 1) n (by omega) (by omega)).2 ?_
  refine tower _ _ (res_zero R F) (chains_zero R E) (chains_zero R E') _ _ _ (by omega) (by omega) (fun p => ?_)
  refine El_iso (chainsXIso R E p) (chainsXIso R E' p) (chains_nat R f p) _ _ _ _ ?_
  refine El_of_single _ _ _ _ _ (by omega) (by omega) ?_
  exact (sub_iff_Rl _ (res R F) _ _ _ (by omega) (by omega)).1 (h p _ (by omega))

theorem LeafFilt_of : LateralTheory.E.LeafLevelPf.LeafFilt :=
  fun _ R _ F c _ _ f h n hn => tower_body R F c f h n hn

end LateralTheory.E.ChainTower
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChartAcycPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut

namespace LateralTheory.E.ChartAcycPf

theorem acyc_of_iso {q : ℕ} {E E' : Spc} (e : E ≅ E') (h : Acyc q E') : Acyc q E := by
  intro n i hn
  have := h n i hn
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : Ht q E n i, z = pull _ e.hom (tw q i) n (pull _ e.inv (tw q i) n z) := by
    intro z
    rw [← pull_comp, e.hom_inv_id, pull_id]
  rw [key x, key y, Subsingleton.elim (pull _ e.inv (tw q i) n x) (pull _ e.inv (tw q i) n y)]

theorem aic_of_equiv {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (h : AIC R) : AIC S := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _)
    (by rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have h2 : (p.map e.symm.toRingHom).map e.toRingHom = p := by
    rw [Polynomial.map_map]; ext n; simp
  rw [← h2]
  change Polynomial.eval (e.toRingHom a) _ = 0
  rw [Polynomial.eval_map_apply, ha, map_zero]

theorem fib_iso_quot {A : Type} [CommRing A] [IsLocalRing A] {U : Scheme.{0}} [IsAffine U]
    (f : U ⟶ Spec (CommRingCat.of A)) :
    ∃ (φ : A →+* Γ(U, ⊤)), Nonempty (fib f ≅ Spec (CommRingCat.of
      (Γ(U, ⊤) ⧸ (IsLocalRing.maximalIdeal A).map φ))) := by
  let e := U.isoSpec
  let φ := Spec.preimage (e.inv ≫ f)
  have hf : f = e.hom ≫ Spec.map φ := by
    rw [Spec.map_preimage]; simp
  letI : Algebra A Γ(U, ⊤) := φ.hom.toAlgebra
  refine ⟨φ.hom, ⟨?_⟩⟩
  refine (pullback.congrHom hf rfl) ≪≫
    (asIso (pullback.map (e.hom ≫ Spec.map φ) (cpt A) (Spec.map φ) (cpt A) e.hom (𝟙 _) (𝟙 _) (by simp) (by simp))) ≪≫ ?_
  refine (pullbackSpecIso A Γ(U, ⊤) (IsLocalRing.ResidueField A)) ≪≫ ?_
  let i := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := A) Γ(U, ⊤)
    (IsLocalRing.maximalIdeal A)).toRingEquiv.toCommRingCatIso
  exact Scheme.Spec.mapIso i.op

theorem ChartAcyc_of (hQ : QuotAcyc) : ChartAcyc := by
  intro H q A _ _ Z U p ι hι hU hZ hq
  have : IsIntegral Z := hZ.1
  by_cases hne : Nonempty U
  · have : IsIntegral U := isIntegral_of_isOpenImmersion ι
    obtain ⟨φ, ⟨e⟩⟩ := fib_iso_quot (ι ≫ p)
    have hdom : IsDomain Γ(U, ⊤) := inferInstance
    have haff : IsAffineOpen (ι ''ᵁ (⊤ : U.Opens)) := (isAffineOpen_top U).image_of_isOpenImmersion ι
    have hnV : ((ι ''ᵁ (⊤ : U.Opens) : Z.Opens) : Set Z).Nonempty := by
      obtain ⟨x⟩ := hne
      exact ⟨ι x, x, trivial, rfl⟩
    have haic : AIC Γ(U, ⊤) :=
      aic_of_equiv (ι.appIso ⊤).commRingCatIsoToRingEquiv (hZ.2 _ haff hnV)
    have hqB : IsUnit (q : Γ(U, ⊤)) := by
      simpa using hq.map φ
    exact acyc_of_iso (sch.mapIso e) (hQ H q Γ(U, ⊤) _ haic hqB)
  · rw [not_nonempty_iff] at hne
    obtain ⟨x⟩ : Nonempty Z := inferInstance
    obtain ⟨V, ⟨W, hW, rfl⟩, hxW, -⟩ := (Z.isBasis_affineOpens).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hWne : Nonempty W := ⟨⟨x, hxW⟩⟩
    have hdom : IsDomain Γ(Z, W) := inferInstance
    have haic : AIC Γ(Z, W) := hZ.2 W hW ⟨x, hxW⟩
    let ψ : CommRingCat.of A ⟶ Γ(Z, W) :=
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop ≫ Z.presheaf.map (homOfLE le_top).op
    have hqC : IsUnit (q : Γ(Z, W)) := by
      simpa using hq.map ψ.hom
    have h1 := hQ H q Γ(Z, W) ⊤ haic hqC
    have : IsEmpty (fib (ι ≫ p)) := ⟨fun y => hne.elim ((pullback.fst (ι ≫ p) (cpt A)) y)⟩
    have : Subsingleton (Γ(Z, W) ⧸ (⊤ : Ideal Γ(Z, W))) := Ideal.Quotient.subsingleton_iff.mpr rfl
    have : IsEmpty (Spec (CommRingCat.of (Γ(Z, W) ⧸ (⊤ : Ideal Γ(Z, W))))) :=
      ⟨fun y => (show PrimeSpectrum (Γ(Z, W) ⧸ (⊤ : Ideal Γ(Z, W))) from y).isPrime.ne_top (Subsingleton.elim _ _)⟩
    exact acyc_of_iso (sch.mapIso (isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty)) h1

end LateralTheory.E.ChartAcycPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChartsPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChartsPf

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev D (i : Fin 2) : P1.Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) (MvPolynomial.X i)

lemma X_mem (i : Fin 2) : (MvPolynomial.X i : MvPolynomial (Fin 2) ℤ) ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℤ 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X ℤ i)

lemma D_affine (i : Fin 2) : IsAffineOpen (D i) :=
  Proj.isAffineOpen_basicOpen _ _ (X_mem i) one_pos

lemma D_cover : ⨆ i, D i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top'
  · exact fun i => ⟨1, X_mem i⟩
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ Algebra.adjoin ℤ (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) := by
      rw [MvPolynomial.adjoin_range_X]; trivial
    have h : Algebra.adjoin ℤ (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ)) ≤
        (Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ 0)
          (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℤ))).restrictScalars ℤ :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact h hx

end LateralTheory.E.ChartsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChernClassSpecialization
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleExistenceAndUniqueness

open LateralTheory.E.CupProductRingLaws

section Ext
variable {R : Type} [CommRing R]

theorem free_hom_ext {P : PSh} {F : Shv R} (f g : (free R).obj P ⟶ F)
    (h : ∀ U x, (f.hom.app (op U)).hom (freeGen R P U x) = (g.hom.app (op U)).hom (freeGen R P U x)) : f = g := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (J := Scheme.etaleTopology) f.hom g.hom F.cond
  ext U : 2
  induction U using Opposite.rec with | _ U => ?_
  apply ModuleCat.free_hom_ext
  rintro ⟨x⟩
  exact h U x

theorem cochain_ext_ev {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (hev : ∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev α p s h U x = ev β p s h U x) :
    α = β := by
  apply Cochain.ext
  intro p s hps
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨p.natAbs, by omega⟩
    have : (chainsXIso R E k).inv ≫ α.v _ _ hps = (chainsXIso R E k).inv ≫ β.v _ _ hps :=
      free_hom_ext _ _ (fun U x => hev k s hps U x)
    simpa using this
  · refine (HomologicalComplex.isZero_extend_X _ _ p (fun i => ?_)).eq_of_src _ _
    show -(i : ℤ) ≠ p
    omega

theorem res_isZero (F : Shv R) (s : ℤ) (hs : s < 0) : IsZero ((res R F).X s) :=
  HomologicalComplex.isZero_extend_X _ _ s (fun i => by show (i : ℤ) ≠ s; omega)

end Ext

def EtaleKummerChernCocycleEvaluationsUnique : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∀ γ γ', IsEtaleFirstChernClassCocycle q L γ → IsEtaleFirstChernClassCocycle q L γ' →
    (∀ (U : Scheme.{0}) (x : Sx E 1 U), ev γ.1 1 1 (by simp) U x = ev γ'.1 1 1 (by simp) U x) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U), ev γ.1 2 0 (by simp) U x = ev γ'.1 2 0 (by simp) U x

def EtaleKummerChernCocycleExists : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
  ∃ γ, IsEtaleFirstChernClassCocycle q L γ

theorem etale_kummer_chern_cocycle_eq_of_evaluation_uniqueness (hU : EtaleKummerChernCocycleEvaluationsUnique) (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hq : Inv q E)
    (γ γ' : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (h : IsEtaleFirstChernClassCocycle q L γ) (h' : IsEtaleFirstChernClassCocycle q L γ') :
    γ = γ' := by
  obtain ⟨h1, h2⟩ := hU q L hq γ γ' h h'
  apply Subtype.ext
  apply cochain_ext_ev
  intro p s hs U x
  rcases p with _ | _ | _ | p
  · obtain rfl : s = 2 := by omega
    rw [h.1 U x, h'.1 U x]
  · obtain rfl : s = 1 := by omega
    exact h1 U x
  · obtain rfl : s = 0 := by omega
    exact h2 U x
  · unfold ev
    rw [(res_isZero (tw q 1) s (by omega)).eq_of_tgt ((chainsXIso _ E _).inv ≫ γ.1.v _ _ hs)
      ((chainsXIso _ E _).inv ≫ γ'.1.v _ _ hs)]

theorem etale_first_chern_class_represented_of_cocycle_exists_and_evaluations_unique (hE : EtaleKummerChernCocycleExists) (hU : EtaleKummerChernCocycleEvaluationsUnique) : EtaleFirstChernClassRepresentedByChernCocycle := by
  intro q _ E L hq
  obtain ⟨γ0, h0⟩ := hE q L hq
  refine ⟨⟨γ0, h0⟩, fun γ hγ => ?_⟩
  have hex : ∃ c : Ht q E 2 1, ∃ γ : Cocycle _ _ 2, CohomologyClass.mk γ = c ∧ IsEtaleFirstChernClassCocycle q L γ :=
    ⟨_, γ0, rfl, h0⟩
  obtain ⟨γ1, hc, h1⟩ := pick_spec hex
  have : γ1 = γ := etale_kummer_chern_cocycle_eq_of_evaluation_uniqueness hU q L hq γ1 γ h1 hγ
  subst this
  exact hc.symm

end LateralTheory.E.ChernCocycleExistenceAndUniqueness
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChowLCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ChowLCut

inductive IterLine {S : Scheme.{0}} : ∀ {Y : Scheme.{0}}, (Y ⟶ S) → Prop
  | iso {Y : Scheme.{0}} (e : Y ⟶ S) : IsIso e → IterLine e
  | comp {Y T : Scheme.{0}} (l : Y ⟶ T) (k : T ⟶ S) : IsLine l → IterLine k → IterLine (l ≫ k)

theorem IT_of_iterLine {S Y : Scheme.{0}} {k : Y ⟶ S} (hk : IterLine k) :
    ∀ {X : Scheme.{0}} (u : X ⟶ Y), IsIntegralHom u → IT (u ≫ k) := by
  induction hk with
  | iso e he => intro X u hu; exact IT.int _ (by infer_instance)
  | comp l k hl _ ih =>
    intro X u hu
    refine IT.step (u ≫ l) k _ ?_ ⟨_, u, l, hu, hl, rfl⟩ (Category.assoc _ _ _)
    simpa using ih (𝟙 _) inferInstance

def LineEx : Prop := ∀ S : Scheme.{0}, ∃ (L : Scheme.{0}) (l : L ⟶ S), IsLine l

def LineBC : Prop := ∀ {L S S' : Scheme.{0}} (l : L ⟶ S) (g : S' ⟶ S), IsLine l → IsLine (pullback.snd l g)

def IterBC : Prop := ∀ {P S X : Scheme.{0}} (q : P ⟶ S) (g : X ⟶ S), IterLine q → IterLine (pullback.fst g q)

def ChowGraph : Prop := ∀ (A : Type) [CommRing A] {X₁ : Scheme.{0}} (p₁ : X₁ ⟶ Spec (CommRingCat.of A)) [IsProper p₁],
  IsIntegral X₁ → ∃ (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of A)) (X' : Scheme.{0}) (i : X' ⟶ pullback p₁ q)
    (U : X₁.Opens) (s : U.toScheme ⟶ X'), IterLine q ∧ IsClosedImmersion i ∧ IsClosedImmersion (i ≫ pullback.snd p₁ q) ∧
    (U : Set X₁).Nonempty ∧ s ≫ i ≫ pullback.fst p₁ q = U.ι

theorem goal_of (hB : IterBC) (hG : ChowGraph) : LateralTheory.E.ChowCut.ChowL := by
  intro A _ X₁ p₁ _ hX₁
  obtain ⟨P, q, X', i, U, s, hq, hi, his, hU, hs⟩ := hG A p₁ hX₁
  refine ⟨X', i ≫ pullback.fst p₁ q, U, s, hU, hs, IT_of_iterLine (hB q p₁ hq) i inferInstance, ?_⟩
  have e : (i ≫ pullback.fst p₁ q) ≫ p₁ = (i ≫ pullback.snd p₁ q) ≫ q := by
    rw [Category.assoc, pullback.condition, Category.assoc]
  rw [e]
  exact IT_of_iterLine hq _ inferInstance

end LateralTheory.E.ChowLCut

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ContStepPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.ContStepPf

def PCS (X0 : Scheme.{0}) : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ j0 : J, Nonempty (D.obj j0 ≅ X0) →
  ∀ n i : ℤ, ∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x

def PCK (X0 : Scheme.{0}) : Prop := ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D),
  IsLimit c → (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) →
  (∀ j, QuasiSeparatedSpace (D.obj j)) → (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ j0 : J, Nonempty (D.obj j0 ≅ X0) →
  ∀ n i : ℤ, ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
    ∃ (k : J) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0

theorem PC_of {X0 : Scheme.{0}} (h1 : PCS X0) (h2 : PCK X0) : PC X0 := by
  intro q J _ _ D c hc ha hcs hqs hu j0 e n i
  exact ⟨h1 q D c hc ha hcs hqs hu j0 e n i, h2 q D c hc ha hcs hqs hu j0 e n i⟩

def StepS : Prop := Hyp → MV → ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) →
  U ⊔ V = ⊤ → PC U.toScheme → PC V.toScheme → PC (U ⊓ V).toScheme → PCS X

def StepK : Prop := Hyp → MV → ∀ (X : Scheme.{0}) (U V : X.Opens), IsCompact (U : Set X) → IsCompact (V : Set X) →
  U ⊔ V = ⊤ → PC U.toScheme → PC V.toScheme → PC (U ⊓ V).toScheme → PCK X

theorem ContStep_of (hS : StepS) (hK : StepK) : ContStep := by
  intro h hmv X U V hU hV hUV pU pV pW
  exact PC_of (hS h hmv X U V hU hV hUV pU pV pW) (hK h hmv X U V hU hV hUV pU pV pW)

end LateralTheory.E.ContStepPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleCohomologyThirdStatementHolds
section
namespace LateralTheory.Fin.EtaleChapterDThree
theorem etale_cohomology_third_statement_holds_alt : LateralTheory.E.EtaleChapterDThree := by
  apply LateralTheory.E.t_D3Cut.goal
theorem intersectionNumber_baseChange : LateralTheory.E.EtaleChapterDThree := etale_cohomology_third_statement_holds_alt
end LateralTheory.Fin.EtaleChapterDThree
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.GoalOf
section
namespace LateralTheory.E.LeafA6ringCut

theorem goal_of (h5 : LateralTheory.E.CupProductRingLaws.LeafRingUnit) (h6 : LateralTheory.E.CupProductRingLaws.LeafRingAssoc)
    (h7 : LateralTheory.E.CupProductRingLaws.LeafRingComm) : LateralTheory.E.D2.LeafA6ring :=
  fun q _ E => ⟨h5 q E, h6 q E, h7 q E⟩

end LateralTheory.E.LeafA6ringCut
end

