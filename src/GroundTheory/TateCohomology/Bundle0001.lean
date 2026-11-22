import Mathlib

-- bundled from GroundTheory.TateCohomology.DeltaMap
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory groupCohomology Rep

universe u

variable {k G H : Type u} [CommRing k] [Group G] [Group H]

noncomputable def cochainsMapShortComplex (f : G →* H) {X : ShortComplex (Rep k H)}
    {Y : ShortComplex (Rep k G)} (F : X.map (resFunctor f) ⟶ Y) :
    X.map (cochainsFunctor k H) ⟶ Y.map (cochainsFunctor k G) where
  τ₁ := cochainsMap f F.τ₁
  τ₂ := cochainsMap f F.τ₂
  τ₃ := cochainsMap f F.τ₃
  comm₁₂ := by
    ext n x
    refine funext fun g => ?_
    exact congrArg (fun φ => φ.hom (x (f ∘ g))) F.comm₁₂
  comm₂₃ := by
    ext n x
    refine funext fun g => ?_
    exact congrArg (fun φ => φ.hom (x (f ∘ g))) F.comm₂₃

theorem δ_comp_map (f : G →* H) {X : ShortComplex (Rep k H)} {Y : ShortComplex (Rep k G)}
    (hX : X.ShortExact) (hY : Y.ShortExact) (F : X.map (resFunctor f) ⟶ Y)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f F.τ₁ j = map f F.τ₃ i ≫ δ hY i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality (cochainsMapShortComplex f F)
    (map_cochainsFunctor_shortExact hX) (map_cochainsFunctor_shortExact hY) i j hij

theorem δ_comp_map_res (f : G →* H) {X : ShortComplex (Rep k H)} (hX : X.ShortExact)
    (i j : ℕ) (hij : i + 1 = j) :
    δ hX i j hij ≫ map f (𝟙 (res f X.X₁)) j =
      map f (𝟙 (res f X.X₃)) i ≫ δ ((shortExact_res f).2 hX) i j hij :=
  δ_comp_map f hX ((shortExact_res f).2 hX) (𝟙 _) i j hij

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.DiagonalSuccIsoFreeInvSingle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupCohomology Rep

universe v w u

section HomComplex

variable {R : Type w} [Ring R] {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

noncomputable def linearYonedaObjMap {X Y : ChainComplex C ℕ} (f : X ⟶ Y) (B : C) :
    Y.linearYonedaObj R B ⟶ X.linearYonedaObj R B :=
  (HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
    ((((linearYoneda R C).obj B).rightOp.mapHomologicalComplex _).map f).op

lemma linearYonedaObjMap_f_apply {X Y : ChainComplex C ℕ} (f : X ⟶ Y) (B : C) (n : ℕ)
    (x : Y.X n ⟶ B) : (linearYonedaObjMap (R := R) f B).f n x = f.f n ≫ x := rfl

lemma linearYonedaObjMap_comp {X Y Z : ChainComplex C ℕ} (f : X ⟶ Y) (g : Y ⟶ Z) (B : C) :
    linearYonedaObjMap (R := R) (f ≫ g) B = linearYonedaObjMap g B ≫ linearYonedaObjMap f B := by
  ext n x
  change (f ≫ g).f n ≫ x = f.f n ≫ g.f n ≫ x
  rw [HomologicalComplex.comp_f]
  exact Category.assoc _ _ _

lemma linearYonedaObjMap_id (X : ChainComplex C ℕ) (B : C) :
    linearYonedaObjMap (R := R) (𝟙 X) B = 𝟙 _ := by
  ext n x
  change (𝟙 X : X ⟶ X).f n ≫ x = x
  rw [HomologicalComplex.id_f]
  exact Category.id_comp _

noncomputable def linearYonedaObjHomotopy {X Y : ChainComplex C ℕ} {f g : X ⟶ Y}
    (h : Homotopy f g) (B : C) :
    Homotopy (linearYonedaObjMap (R := R) f B) (linearYonedaObjMap g B) :=
  ((((linearYoneda R C).obj B).rightOp).mapHomotopy h).unop

noncomputable def linearYonedaObjHomotopyEquiv {X Y : ChainComplex C ℕ} (e : HomotopyEquiv X Y)
    (B : C) : HomotopyEquiv (Y.linearYonedaObj R B) (X.linearYonedaObj R B) where
  hom := linearYonedaObjMap e.hom B
  inv := linearYonedaObjMap e.inv B
  homotopyHomInvId := (Homotopy.ofEq (linearYonedaObjMap_comp _ _ _).symm).trans
    ((linearYonedaObjHomotopy e.homotopyInvHomId B).trans
      (Homotopy.ofEq (linearYonedaObjMap_id _ _)))
  homotopyInvHomId := (Homotopy.ofEq (linearYonedaObjMap_comp _ _ _).symm).trans
    ((linearYonedaObjHomotopy e.homotopyHomInvId B).trans
      (Homotopy.ofEq (linearYonedaObjMap_id _ _)))

end HomComplex

section Bar

variable {k G : Type u} [CommRing k] [Group G]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

lemma diagonalSuccIsoFree_inv_single (m : ℕ) (f : Fin m → G) (g : G) (r : k) :
    (diagonalSuccIsoFree k G m).inv.hom (Finsupp.single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  simp only [diagonalSuccIsoFree, diagonalSuccIsoTensorTrivial, Iso.trans_inv, Rep.hom_comp,
    Representation.IntertwiningMap.comp_apply]
  have step1 : (Hom.hom (leftRegularTensorTrivialIsoFree k G (Fin m → G)).inv)
      (Finsupp.single f (.single g r)) = .single g 1 ⊗ₜ[k] .single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
  rw [step1]
  simp only [mkIso_inv, Representation.linearizeOfMulActionIso, Representation.Equiv.mk_symm,
    LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom, Action.tensorObj_V, Action.trivial_V,
    Functor.mapIso_inv, tensor_V, tensor_ρ, Iso.symm_inv, Functor.Monoidal.μIso_hom, μ_hom,
    MonoidalCategory.tensorIso_inv, Representation.linearizeTrivialIso, hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply, Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
  have key₁ := Representation.linearizeMap_single (k := k)
    (Action.diagonalSuccIsoTensorTrivial G m).inv (g, f) ((1 : k) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := k)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin m → G)) g f 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G m).inv) z) key₂).trans key₁).trans (by simp)

lemma barResolution_π_f_zero_single (v : Fin 0 → G) (g : G) (r : k) :
    ((barResolution k G).π.f 0).hom (Finsupp.single v (MonoidAlgebra.single g r)) = r := by
  change (standardComplex.ε k G).hom ((diagonalSuccIsoFree k G 0).inv.hom
    (Finsupp.single v (MonoidAlgebra.single g r))) = r
  rw [diagonalSuccIsoFree_inv_single]
  simp [standardComplex.ε]

end Bar

section Norm

variable {k H : Type u} [CommRing k] [Group H] [Fintype H]

lemma ρ_apply_norm (B : Rep.{u} k H) (b : B) (s : H) : B.ρ s (B.ρ.norm b) = B.ρ.norm b := by
  rw [Representation.norm, LinearMap.sum_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun t => ?_
  simp [← Module.End.mul_apply, ← map_mul]

end Norm

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.Induced
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupCohomology groupHomology Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

def TateAcyclic (M : Rep.{u} k G) : Prop := ∀ n : ℤ, IsZero (tateCohomology M n)

theorem TateAcyclic.of_retract {M N : Rep.{u} k G} (i : M ⟶ N) (r : N ⟶ M) (h : i ≫ r = 𝟙 M)
    (hN : TateAcyclic N) : TateAcyclic M := fun n => by
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 ((tateCohomologyFunctor n).obj M) = 0
  rw [← (tateCohomologyFunctor n).map_id, ← h, Functor.map_comp,
    (hN n).eq_of_tgt ((tateCohomologyFunctor n).map i) 0, zero_comp]

theorem TateAcyclic.of_iso {M N : Rep.{u} k G} (e : M ≅ N) (hN : TateAcyclic N) :
    TateAcyclic M :=
  hN.of_retract e.hom e.inv e.hom_inv_id

theorem isZero_tateCohomology_zero_of_forall (M : Rep.{u} k G)
    (h : ∀ m : M, (∀ g : G, M.ρ g m = m) → ∃ y : M, M.ρ.norm y = m) :
    IsZero (tateCohomology M 0) := by
  rw [tateCohomology, tateCohomologyFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-1) 0 1 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ x₂ : (inhomogeneousCochains M).X 0, (inhomogeneousCochains M).d 0 1 x₂ = 0 →
    ∃ x₁ : (inhomogeneousChains M).X 0, M.tateNorm x₁ = x₂
  intro x₂ hd
  have hinv : ∀ g : G, M.ρ g ((cochainsIso₀ M).hom x₂) = (cochainsIso₀ M).hom x₂ := by
    intro g
    have key : (d₀₁ M).hom ((cochainsIso₀ M).hom.hom x₂) =
        (cochainsIso₁ M).hom.hom (((inhomogeneousCochains M).d 0 1).hom x₂) := by
      rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, comp_d₀₁_eq]; rfl
    rw [show ((inhomogeneousCochains M).d 0 1).hom x₂ = 0 from hd, map_zero] at key
    have := congr_fun key g
    exact sub_eq_zero.mp this
  obtain ⟨y, hy⟩ := h _ hinv
  refine ⟨(chainsIso₀ M).inv y, ?_⟩
  simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  change (cochainsIso₀ M).inv (M.ρ.norm y) = x₂
  rw [hy, Iso.hom_inv_id_apply]

theorem isZero_tateCohomology_neg_one_of_forall (M : Rep.{u} k G)
    (h : ∀ m : M, M.ρ.norm m = 0 → ∃ z : G →₀ M, d₁₀ M z = m) :
    IsZero (tateCohomology M (-1)) := by
  rw [tateCohomology, tateCohomologyFunctor, Functor.comp_obj,
    HomologicalComplex.homologyFunctor_obj, ← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  change ∀ x₂ : (inhomogeneousChains M).X 0, M.tateNorm x₂ = 0 →
    ∃ x₁ : (inhomogeneousChains M).X 1, (inhomogeneousChains M).d 1 0 x₁ = x₂
  intro x₂ hx
  have hn : M.ρ.norm ((chainsIso₀ M).hom x₂) = 0 := by
    have := congr_arg (fun x => (cochainsIso₀ M).hom x) hx
    simp only [Rep.tateNorm, ConcreteCategory.comp_apply, Iso.inv_hom_id_apply, map_zero] at this
    exact this
  obtain ⟨z, hz⟩ := h _ hn
  refine ⟨(chainsIso₁ M).inv z, ?_⟩
  rw [eq_d₁₀_comp_inv_apply, hz, Iso.hom_inv_id_apply]

theorem isZero_tateCohomology_zero_of_sum_eq (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M 0) := by
  refine isZero_tateCohomology_zero_of_forall M fun m hm => ⟨φ m, ?_⟩
  rw [Representation.norm, LinearMap.sum_apply]
  conv_rhs => rw [← hφ m]
  simp only [hm]

theorem isZero_tateCohomology_neg_one_of_sum_eq (M : Rep.{u} k G) (φ : M.V →ₗ[k] M.V)
    (hφ : ∀ m : M, ∑ g : G, M.ρ g (φ (M.ρ g⁻¹ m)) = m) :
    IsZero (tateCohomology M (-1)) := by
  refine isZero_tateCohomology_neg_one_of_forall M fun m hm =>
    ⟨∑ g : G, Finsupp.single g⁻¹ (φ (M.ρ g⁻¹ m)), ?_⟩
  have hsum : ∑ g : G, M.ρ g⁻¹ m = M.ρ.norm m := by
    rw [Representation.norm, LinearMap.sum_apply]
    exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun _ => rfl)
  show (Finsupp.lsum k fun g : G => M.ρ g⁻¹ - LinearMap.id)
    (∑ g : G, Finsupp.single g⁻¹ (φ (M.ρ g⁻¹ m))) = m
  simp only [map_sum, Finsupp.lsum_single, LinearMap.sub_apply, LinearMap.id_apply, inv_inv]
  rw [Finset.sum_sub_distrib, ← map_sum, hsum, hm, map_zero, sub_zero, hφ]

section Coind

variable (B : Rep.{u} k (⊥ : Subgroup G))

open scoped Classical in

noncomputable def coindBotProj :
    (coind (⊥ : Subgroup G).subtype B).V →ₗ[k] (coind (⊥ : Subgroup G).subtype B).V :=
  LinearMap.codRestrict _ ((LinearMap.single k (fun _ : G => B.V) 1) ∘ₗ LinearMap.proj 1 ∘ₗ
    (Representation.coindV (⊥ : Subgroup G).subtype B.ρ).subtype) fun f => by
      rw [Representation.mem_coindV]
      intro s x
      obtain rfl : s = 1 := Subsingleton.elim _ _
      simp

open scoped Classical in

theorem sum_coindBotProj (f : coind (⊥ : Subgroup G).subtype B) :
    ∑ g : G, (coind (⊥ : Subgroup G).subtype B).ρ g
      (coindBotProj B ((coind (⊥ : Subgroup G).subtype B).ρ g⁻¹ f)) = f := by
  apply Subtype.ext
  funext x
  rw [Submodule.coe_sum, Finset.sum_apply]
  change ∑ g : G, (Pi.single (M := fun _ : G => B.V) (1 : G) (f.1 (1 * g⁻¹)) (x * g)) = f.1 x
  rw [Fintype.sum_eq_single x⁻¹]
  · simp
  · intro g hg
    rw [Pi.single_apply, if_neg]
    exact fun h => hg (eq_inv_of_mul_eq_one_right h)

theorem isZero_tateCohomology_coind_bot (n : ℤ) :
    IsZero (tateCohomology (coind (⊥ : Subgroup G).subtype B) n) := by
  classical
  rcases n with (_ | n) | (_ | n)
  · exact isZero_tateCohomology_zero_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)
  · exact ((isZero_groupCohomology_succ_of_subsingleton B n).of_iso (coindIso B (n + 1))).of_iso
      ((TateCohomology.isoGroupCohomology (n + 1)).app _)
  · exact isZero_tateCohomology_neg_one_of_sum_eq _ (coindBotProj B) (sum_coindBotProj B)
  · have e := (TateCohomology.isoGroupHomology (Int.negSucc (n + 1)) (n + 1)
      (by simp [Int.negSucc_eq])).app (coind (⊥ : Subgroup G).subtype B)
    refine (((isZero_groupHomology_succ_of_subsingleton B n).of_iso
      (indIso (⊥ : Subgroup G) B (n + 1))).of_iso ?_).of_iso e
    exact (groupHomology.functor k G (n + 1)).mapIso (indCoindIso B).symm

theorem isZero_tateCohomology_ind_bot (n : ℤ) :
    IsZero (tateCohomology (ind (⊥ : Subgroup G).subtype B) n) := by
  classical
  exact (isZero_tateCohomology_coind_bot B n).of_iso
    ((tateCohomologyFunctor n).mapIso (indCoindIso B))

theorem tateAcyclic_coind_bot : TateAcyclic (coind (⊥ : Subgroup G).subtype B) :=
  isZero_tateCohomology_coind_bot B

theorem tateAcyclic_ind_bot : TateAcyclic (ind (⊥ : Subgroup G).subtype B) :=
  isZero_tateCohomology_ind_bot B

end Coind

end GroundTheory.GroupCoh
end

-- bundled from GroundTheory.TateCohomology.ModuleHomologyData
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits

universe u

section ModuleHomologyData

variable {R : Type u} [CommRing R]

noncomputable def moduleKernelIsLimit (S : ShortComplex (ModuleCat.{u} R))
    (K : Type u) [AddCommGroup K] [Module R K] (ι : K →ₗ[R] S.X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker S.g.hom) (wi : ModuleCat.ofHom ι ≫ S.g = 0) :
    IsLimit (KernelFork.ofι (ModuleCat.ofHom ι) wi) :=
  KernelFork.IsLimit.ofι _ _
    (fun {A} k hk => ModuleCat.ofHom ((LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ
      k.hom.codRestrict (LinearMap.range ι) (fun a => by
        rw [hrange, LinearMap.mem_ker]
        exact congr($hk a))))
    (fun {A} k hk => by
      ext a
      simp)
    (fun {A} k hk m hm => by
      ext a
      apply hι
      simp [← hm])

noncomputable def moduleLeftHomologyData (S : ShortComplex (ModuleCat.{u} R))
    (K : Type u) [AddCommGroup K] [Module R K] (ι : K →ₗ[R] S.X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker S.g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range S.f.hom) : S.LeftHomologyData :=
  have wi : ModuleCat.ofHom ι ≫ S.g = 0 := by
    ext x
    have : ι x ∈ LinearMap.ker S.g.hom := hrange ▸ LinearMap.mem_range_self ι x
    simpa using LinearMap.mem_ker.1 this
  have hi := moduleKernelIsLimit S K ι hι hrange wi
  have hlift : ∀ c, ι ((hi.lift (KernelFork.ofι S.f S.zero)).hom c) = S.f.hom c := fun c =>
    congr($(Fork.IsLimit.lift_ι hi) c)
  have wπ : hi.lift (KernelFork.ofι S.f S.zero) ≫ ModuleCat.ofHom N.mkQ = 0 := by
    ext c
    simp [Submodule.Quotient.mk_eq_zero, hN, hlift]
  { K := ModuleCat.of R K
    H := ModuleCat.of R (K ⧸ N)
    i := ModuleCat.ofHom ι
    wi := wi
    hi := hi
    π := ModuleCat.ofHom N.mkQ
    wπ := wπ
    hπ := CokernelCofork.IsColimit.ofπ _ _
      (fun {A} k hk => ModuleCat.ofHom (N.liftQ k.hom (fun x hx => by
        obtain ⟨c, hc⟩ := (hN x).1 hx
        have : (hi.lift (KernelFork.ofι S.f S.zero)).hom c = x := hι (by rw [hlift, hc])
        rw [LinearMap.mem_ker, ← this]
        exact congr($hk c))))
      (fun {A} k hk => by
        ext x
        simp)
      (fun {A} k hk m hm => by
        ext x
        simp [← hm]) }

variable (S : ShortComplex (ModuleCat.{u} R))
    (K : Type u) [AddCommGroup K] [Module R K] (ι : K →ₗ[R] S.X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker S.g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range S.f.hom)

@[simp]
lemma moduleLeftHomologyData_i_hom :
    (moduleLeftHomologyData S K ι hι hrange N hN).i.hom = ι := rfl

@[simp]
lemma moduleLeftHomologyData_π_hom :
    (moduleLeftHomologyData S K ι hι hrange N hN).π.hom = N.mkQ := rfl

lemma moduleLeftHomologyData_homologyIso_hom_homologyπ [S.HasHomology]
    (z : S.cycles) (x : K) (hx : ι x = S.iCycles.hom z) :
    (moduleLeftHomologyData S K ι hι hrange N hN).homologyIso.hom.hom (S.homologyπ.hom z) =
      Submodule.Quotient.mk x := by
  set h := moduleLeftHomologyData S K ι hι hrange N hN
  have h1 : (S.homologyπ ≫ h.homologyIso.hom).hom z = (h.cyclesIso.hom ≫ h.π).hom z := by
    rw [h.homologyπ_comp_homologyIso_hom]
  have h2 : (h.cyclesIso.hom ≫ h.i).hom z = S.iCycles.hom z := by
    rw [h.cyclesIso_hom_comp_i]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [h1]
  have : h.cyclesIso.hom.hom z = x := hι (by rw [hx, ← h2]; rfl)
  rw [this]
  rfl

variable {S₁ S₂ : ShortComplex (ModuleCat.{u} R)} (φ : S₁ ⟶ S₂)
    (K₁ : Type u) [AddCommGroup K₁] [Module R K₁] (ι₁ : K₁ →ₗ[R] S₁.X₂)
    (hι₁ : Function.Injective ι₁) (hrange₁ : LinearMap.range ι₁ = LinearMap.ker S₁.g.hom)
    (N₁ : Submodule R K₁) (hN₁ : ∀ x, x ∈ N₁ ↔ ι₁ x ∈ LinearMap.range S₁.f.hom)
    (K₂ : Type u) [AddCommGroup K₂] [Module R K₂] (ι₂ : K₂ →ₗ[R] S₂.X₂)
    (hι₂ : Function.Injective ι₂) (hrange₂ : LinearMap.range ι₂ = LinearMap.ker S₂.g.hom)
    (N₂ : Submodule R K₂) (hN₂ : ∀ x, x ∈ N₂ ↔ ι₂ x ∈ LinearMap.range S₂.f.hom)

noncomputable def moduleLeftHomologyMapData (φK : K₁ →ₗ[R] K₂)
    (hφK : ∀ x, ι₂ (φK x) = φ.τ₂.hom (ι₁ x)) (hφN : N₁ ≤ N₂.comap φK) :
    ShortComplex.LeftHomologyMapData φ (moduleLeftHomologyData S₁ K₁ ι₁ hι₁ hrange₁ N₁ hN₁)
      (moduleLeftHomologyData S₂ K₂ ι₂ hι₂ hrange₂ N₂ hN₂) where
  φK := ModuleCat.ofHom φK
  φH := ModuleCat.ofHom (N₁.mapQ N₂ φK hφN)
  commi := by
    ext x
    exact hφK x
  commf' := by
    ext c
    apply hι₂
    have e₁ : ι₁ ((moduleLeftHomologyData S₁ K₁ ι₁ hι₁ hrange₁ N₁ hN₁).f'.hom c) = S₁.f.hom c :=
      congr($((moduleLeftHomologyData S₁ K₁ ι₁ hι₁ hrange₁ N₁ hN₁).f'_i).hom c)
    have e₂ : ι₂ ((moduleLeftHomologyData S₂ K₂ ι₂ hι₂ hrange₂ N₂ hN₂).f'.hom (φ.τ₁.hom c)) =
        S₂.f.hom (φ.τ₁.hom c) :=
      congr($((moduleLeftHomologyData S₂ K₂ ι₂ hι₂ hrange₂ N₂ hN₂).f'_i).hom (φ.τ₁.hom c))
    have e₃ : S₂.f.hom (φ.τ₁.hom c) = φ.τ₂.hom (S₁.f.hom c) := congr($(φ.comm₁₂).hom c)
    exact (hφK _).trans ((congrArg φ.τ₂.hom e₁).trans (e₃.symm.trans e₂.symm))
  commπ := by
    ext x
    rfl

end ModuleHomologyData
section Complexes

variable {R : Type u} [CommRing R]

lemma homologyFunctorIso'_moduleLeftHomologyData_apply {ιc : Type*} {c : ComplexShape ιc}
    (C : HomologicalComplex (ModuleCat.{u} R) c) (i j k : ιc) (hi : c.prev j = i)
    (hk : c.next j = k) (K : Type u) [AddCommGroup K] [Module R K]
    (ι : K →ₗ[R] (C.sc' i j k).X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker (C.sc' i j k).g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range (C.sc' i j k).f.hom)
    (z : C.cycles j) (x : K) (hx : ι x = (C.iCycles j).hom z) :
    (moduleLeftHomologyData _ K ι hι hrange N hN).homologyIso.hom.hom
      (((HomologicalComplex.homologyFunctorIso' _ c i j k hi hk).hom.app C).hom
        ((C.homologyπ j).hom z)) = Submodule.Quotient.mk x := by
  set e := (HomologicalComplex.natIsoSc' (ModuleCat.{u} R) c i j k hi hk).hom.app C
  have h1 : (HomologicalComplex.homologyFunctorIso' _ c i j k hi hk).hom.app C =
      ShortComplex.homologyMap e := by
    simp [HomologicalComplex.homologyFunctorIso', e]
    exact Category.id_comp _
  have h2 : (ShortComplex.homologyMap e).hom ((C.sc j).homologyπ.hom z) =
      (C.sc' i j k).homologyπ.hom ((ShortComplex.cyclesMap e).hom z) :=
    congr(($(ShortComplex.homologyπ_naturality e)).hom z)
  have h3 : (C.sc' i j k).iCycles.hom ((ShortComplex.cyclesMap e).hom z) =
      e.τ₂.hom ((C.sc j).iCycles.hom z) :=
    congr(($(ShortComplex.cyclesMap_i e)).hom z)
  have h4 : (C.sc' i j k).iCycles.hom ((ShortComplex.cyclesMap e).hom z) = (C.iCycles j).hom z := by
    rw [h3]
    simp [e]
    rfl
  rw [h1]
  refine (congrArg (fun w => (moduleLeftHomologyData _ K ι hι hrange N hN).homologyIso.hom.hom w)
    h2).trans ?_
  exact moduleLeftHomologyData_homologyIso_hom_homologyπ _ K ι hι hrange N hN _ x (hx.trans h4.symm)

lemma exists_cycles_of_moduleLeftHomologyData {ιc : Type*} {c : ComplexShape ιc}
    (C : HomologicalComplex (ModuleCat.{u} R) c) (i j k : ιc) (hi : c.prev j = i)
    (hk : c.next j = k) (K : Type u) [AddCommGroup K] [Module R K]
    (ι : K →ₗ[R] (C.sc' i j k).X₂) (hι : Function.Injective ι)
    (hrange : LinearMap.range ι = LinearMap.ker (C.sc' i j k).g.hom) (N : Submodule R K)
    (hN : ∀ x, x ∈ N ↔ ι x ∈ LinearMap.range (C.sc' i j k).f.hom) (x : K) :
    ∃ z : C.cycles j, (C.iCycles j).hom z = ι x := by
  set e := (HomologicalComplex.natIsoSc' (ModuleCat.{u} R) c i j k hi hk).inv.app C
  set h := moduleLeftHomologyData _ K ι hι hrange N hN
  refine ⟨(ShortComplex.cyclesMap e).hom (h.cyclesIso.inv.hom x), ?_⟩
  have h3 : (C.sc j).iCycles.hom ((ShortComplex.cyclesMap e).hom (h.cyclesIso.inv.hom x)) =
      e.τ₂.hom ((C.sc' i j k).iCycles.hom (h.cyclesIso.inv.hom x)) :=
    congr(($(ShortComplex.cyclesMap_i e)).hom (h.cyclesIso.inv.hom x))
  have h4 : (C.sc' i j k).iCycles.hom (h.cyclesIso.inv.hom x) = ι x :=
    congr(($(h.cyclesIso_inv_comp_iCycles)).hom x)
  refine h3.trans ?_
  rw [h4]
  simp [e]
  rfl

end Complexes

end GroundTheory.GroupCoh
end

