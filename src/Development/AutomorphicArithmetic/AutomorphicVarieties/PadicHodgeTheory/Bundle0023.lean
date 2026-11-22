import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SnocZeroLastCoordinateLast
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0022
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0013

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CrystallineTransferSurjection
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem crystalline_transfer_surjection {l : ℕ} [Fact l.Prime] {G G' A A' V V' : Type} [Group G] [Group G'] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [CommRing A']
    [Algebra ℚ_[l] A'] [AddCommGroup V'] [Module A' V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A' V']
    (φ : G →* GQ l) (e : G' →* G) (he : Function.Surjective e) (ρ : Representation A G V)
    (ρ' : Representation A' G' V') (f : V ≃ₗ[ℚ_[l]] V') (hf : ∀ g x, f (ρ (e g) x) = ρ' g (f x)) :
    IsCr φ ρ ↔ IsCr (φ.comp e) ρ' := by
  have hr : (φ.comp e).range = φ.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 he, ← MonoidHom.range_eq_map]
  let F : V ⊗[ℚ_[l]] Bcr l ≃ₗ[ℚ_[l]] V' ⊗[ℚ_[l]] Bcr l := TensorProduct.congr f (LinearEquiv.refl _ _)
  have hF : ∀ g x, F (actC φ (resCoef ℚ_[l] ρ) (e g) x) = actC (φ.comp e) (resCoef ℚ_[l] ρ') g (F x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul v b => simp [F, actC, resCoef, hf]
  have hD : (Dcr φ (resCoef ℚ_[l] ρ)).map F.toLinearMap = Dcr (φ.comp e) (resCoef ℚ_[l] ρ') := by
    ext x
    obtain ⟨x, rfl⟩ := F.surjective x
    rw [Submodule.mem_map_equiv, F.symm_apply_apply]
    simp only [Dcr, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
      ← hF, F.injective.eq_iff]
    exact he.forall
  unfold IsCr
  rw [hr, ← hD, LinearEquiv.finrank_map_eq, f.finrank_eq]

private theorem crystalline_iff_on_top {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A]
    [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]
    (φ : G →* GQ l) (ρ : Representation A G V) : IsCr φ ρ ↔ CrOn φ ρ ⊤ :=
  crystalline_transfer_surjection φ (⊤ : Subgroup G).subtype (fun g => ⟨⟨g, trivial⟩, rfl⟩) ρ _ (LinearEquiv.refl _ _)
    fun _ _ => rfl

private theorem crystalline_conj_invariant {l : ℕ} [Fact l.Prime] {G A : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A] {n : ℕ}
    (φ : G →* GQ l) (r : G →* GL (Fin n) A) (h : GL (Fin n) A) :
    IsCr φ (colRep r) ↔ IsCr φ (colRep (conjGL h r)) := by
  have := crystalline_transfer_surjection φ (MonoidHom.id G) Function.surjective_id (colRep r) (colRep (conjGL h r))
    ((Matrix.toLinearEquiv' (h : Matrix (Fin n) (Fin n) A) h.invertible).restrictScalars ℚ_[l]) fun g x => by
      simp [colRep, conjGL, Matrix.toLinearEquiv', Matrix.mul_assoc]
  simpa using this

private theorem continuous_dual_number_qcont {l : ℕ} [Fact l.Prime] {X E : Type} [TopologicalSpace X] [Field E] [Algebra ℚ_[l] E]
    [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] (f : X → DualNumber E) (hf : Continuous f) : QCont l f := by
  have h1 : Continuous fun x => (f x).fst := TrivSqZeroExt.continuous_fst.comp hf
  have h2 : Continuous fun x => (f x).snd := TrivSqZeroExt.continuous_snd.comp hf
  have e : f = fun x => ((TrivSqZeroExt.inlAlgHom ℚ_[l] E E).toLinearMap (f x).fst) +
      (((TrivSqZeroExt.inrHom E E).restrictScalars ℚ_[l]) (f x).snd) :=
    funext fun x => (TrivSqZeroExt.inl_fst_add_inr_snd_eq _).symm
  unfold QCont
  clear hf
  letI : TopologicalSpace (DualNumber E) := moduleTopology ℚ_[l] _
  haveI : IsModuleTopology ℚ_[l] (DualNumber E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd ℚ_[l] (DualNumber E)
  rw [e]
  exact ((IsModuleTopology.continuous_of_linearMap _).comp h1).add
    ((IsModuleTopology.continuous_of_linearMap _).comp h2)

private theorem open_subgroup_finite_index {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) (H : Subgroup G) (hH : IsOpen (H : Set G)) : H.FiniteIndex := by
  have hc : IsClosed (φ.range : Set (GQ l)) := φ.range.isClosed_of_isOpen hφ.isOpen_range
  haveI : CompactSpace G := (IsClosedEmbedding.mk hφ.isEmbedding hc).compactSpace
  haveI := H.quotient_finite_of_isOpen hH
  exact Subgroup.finiteIndex_of_finite_quotient

theorem UpperTheory.V.Loc.pr6 :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] {Y : Type} [AddCommGroup Y] [Module E Y] [Module ℚ_[l] Y] [IsScalarTower ℚ_[l] E Y] [FiniteDimensional ℚ_[l] Y] [TopologicalSpace Y] [IsModuleTopology ℚ_[l] Y] [IsTopologicalAddGroup Y] [ContinuousConstSMul E Y] (ρ : Representation E G Y), ContAction ρ → ∀ y ∈ Z1 ρ, ∀ (H : Subgroup G) [H.Normal], IsOpen (H : Set G) → ∀ {n : ℕ} (r : H →* GL (Fin n) E), Continuous (fun g => (r g : Matrix (Fin n) (Fin n) E)) → ∀ (ι : Y →ₗ[E] Matrix (Fin n) (Fin n) E) (p : Matrix (Fin n) (Fin n) E →ₗ[E] Y), (∀ x, p (ι x) = x) → (∀ (g : H) x, ι (ρ g x) = adGL r g (ι x)) → (∀ (g : H) X, p (adGL r g X) = ρ g (p X)) → ∀ r' : H →* GL (Fin n) (DualNumber E), (∀ (g : H) i j, (r' g : Matrix (Fin n) (Fin n) (DualNumber E)) i j = ⟨(r g : Matrix (Fin n) (Fin n) E) i j, (ι (y g) * (r g : Matrix (Fin n) (Fin n) E)) i j⟩) → ∀ (h : GL (Fin n) (DualNumber E)) (κ : Fin n → H →* (DualNumber E)ˣ) (w : Fin n → ℤ), UpperTri (conjGL h r') κ → StrictAnti w → (∀ i (g : H), φ g ∈ Iq l → κ i g = cycA l l (DualNumber E) (φ g) ^ w i) → (∀ i j, i < j → ∃ g : H, (κ i g : DualNumber E).fst ≠ (κ j g : DualNumber E).fst * (cycA l l E (φ g) : E)) → IsCr (φ.comp H.subtype) (colRep r) ∧ IsCr (φ.comp H.subtype) (colRep r') ∧ y ∈ UpperTheory.V.Loc.finiteCocycles φ ρ := by
  intro P l _ G _ _ _ φ hφ E _ _ _ _ _ _ _ _ Y _ _ _ _ _ _ _ _ _ ρ hρ y hy H _ hH n r hr ι p hp hι hpe r' hr' h κ w
    hU hw hκ hne
  haveI := open_subgroup_finite_index φ hφ H hH
  have hφH : IsOpenEmbedding (φ.comp H.subtype) := hφ.comp hH.isOpenEmbedding_subtypeVal
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin n) (Fin n) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin n → Fin n → E))
  have hyc : Continuous fun g : H => ι (y g) :=
    (IsModuleTopology.continuous_of_linearMap (ι.restrictScalars ℚ_[l])).comp (hy.1.comp continuous_subtype_val)
  have hy' : (fun g : H => ι (y g)) ∈ Z1 (adGL r) := ⟨hyc, fun g k => by
    simp only []
    rw [Subgroup.coe_mul, hy.2, map_add, hι]⟩
  have hr'c : Continuous fun g => (r' g : Matrix (Fin n) (Fin n) (DualNumber E)) := by
    refine continuous_matrix fun i j => ?_
    simp only [hr']
    exact Continuous.prodMk (hr.matrix_elem i j) ((hyc.matrix_mul hr).matrix_elem i j)
  have hcc : ∀ i j, QCont l fun g => (conjGL h r' g : Matrix (Fin n) (Fin n) (DualNumber E)) i j := fun i j =>
    continuous_dual_number_qcont _ (((continuous_const.matrix_mul hr'c).matrix_mul continuous_const).matrix_elem i j)
  haveI : Module.Finite E (DualNumber E) := inferInstanceAs (Module.Finite E (E × E))
  have h1 : IsCr (φ.comp H.subtype) (colRep r') :=
    (crystalline_conj_invariant _ r' h).2 (prC P _ hφH (TrivSqZeroExt.fstHom E E E)
      (fun a ha => ⟨2, by ext <;> simp_all [pow_two]⟩) (conjGL h r') hcc κ w hU hw hκ hne)
  obtain ⟨h2, h3⟩ := (deformCr _ hφH r hr _ hy' r' hr' ⊤ (by simp)).1 ((crystalline_iff_on_top _ _).1 h1)
  refine ⟨(crystalline_iff_on_top _ _).2 h2, h1, (z1fDesc φ ρ H y hy).2 ?_⟩
  have := (z1fMap (φ.comp H.subtype) (adGL r) (ρ.comp H.subtype : Representation E H Y)).2
    (p.restrictScalars ℚ_[l]) hpe _ h3
  simpa [hp] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DualCr
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

private theorem crOn_top {l : ℕ} [Fact l.Prime] {G A V : Type} [Group G] [CommRing A] [Algebra ℚ_[l] A]
    [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (φ : G →* GQ l)
    (ρ : Representation A G V) : CrOn φ ρ ⊤ ↔ IsCr φ ρ := by
  have he : Function.Surjective (fun g : (⊤ : Subgroup G) => (g : G)) := fun g => ⟨⟨g, trivial⟩, rfl⟩
  have hr : (φ.comp (⊤ : Subgroup G).subtype).range = φ.range := by
    ext σ
    exact ⟨fun ⟨g, hg⟩ => ⟨g, hg⟩, fun ⟨g, hg⟩ => ⟨⟨g, trivial⟩, hg⟩⟩
  have hc : Dcr (φ.comp (⊤ : Subgroup G).subtype)
      (resCoef ℚ_[l] (ρ.comp (⊤ : Subgroup G).subtype : Representation A (⊤ : Subgroup G) V)) =
      Dcr φ (resCoef ℚ_[l] ρ) := by
    unfold Dcr
    exact he.iInf_comp (fun g => LinearMap.ker (actC φ (resCoef ℚ_[l] ρ) g - LinearMap.id))
  unfold CrOn IsCr
  rw [hr, hc]

private def glOn {G R : Type} [Group G] [CommRing R] {m : ℕ} (H : Subgroup G) (r : G →* GG m R)
    (h : ∀ g ∈ H, (r g).right = 1) : H →* GL (Fin m) R where
  toFun g := (r g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

private theorem isLCr_iff {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    (D : Dat3 l O) {B : Type} [CommRing B] [Algebra O B] [Algebra ℚ_[l] B] (r : GQ l →* GG 3 B)
    (h : ∀ g ∈ D.HL, (r g).right = 1) : D.IsLCr r ↔ IsCr D.HL.subtype (colRep (glOn D.HL r h)) := by
  refine ⟨fun ⟨ρ, h1, h2⟩ => ?_, fun h2 => ⟨_, fun _ => rfl, h2⟩⟩
  have : ρ = glOn D.HL r h := MonoidHom.ext h1
  exact this ▸ h2

theorem UpperTheory.V.Loc.dualCr :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E] (r : GQ l →* GG 3 E), HasMult D.η r → Continuous (fun g => (r g).mat) → ∀ γ ∈ Z1 (adRep r), ∀ r' : GQ l →* GG 3 (DualNumber E), DualDef r γ r' → (D.IsLCr r' ↔ D.IsLCr r ∧ γ ∈ finiteCocycles (MonoidHom.id _) (adRep r)) := by
  intro l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ _ _ r hm hr γ hγ r' hd
  haveI : IsModuleTopology ℚ_[l] (Matrix (Fin 3) (Fin 3) E) :=
    inferInstanceAs (IsModuleTopology ℚ_[l] (Fin 3 → Fin 3 → E))
  have hη : IsOpen (D.η.ker : Set (GQ l)) := by
    have e : D.η.ker = GK D.Kv := Subgroup.ext fun g => D.η_ker g
    haveI := D.Kv.2
    rw [e]
    exact IntermediateField.fixingSubgroup_isOpen D.Kv.1
  have hH : IsOpen (D.HL : Set (GQ l)) := hη.inter D.τ_open
  haveI : D.HL.Normal := inferInstanceAs (D.η.ker ⊓ D.τ.ker).Normal
  haveI : Finite (GQ l ⧸ D.HL) := Subgroup.quotient_finite_of_isOpen _ hH
  haveI : D.HL.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have h1 : ∀ g ∈ D.HL, (r g).right = 1 := fun g hg => (hm g).trans hg.1
  have h1' : ∀ g ∈ D.HL, (r' g).right = 1 := fun g hg => (hd g).1.trans (h1 g hg)
  have had : ((adRep r).comp D.HL.subtype : Representation E D.HL _) = adGL (glOn D.HL r h1) := by
    refine MonoidHom.ext fun g => LinearMap.ext fun X => ?_
    change (r g).adFun X = _
    rw [GG.adFun, if_pos (h1 g g.2)]
    rfl
  have hy : (fun h : D.HL => γ h) ∈ Z1 (adGL (glOn D.HL r h1)) := by
    rw [← had]
    exact ⟨hγ.1.comp continuous_subtype_val, fun g h => hγ.2 g h⟩
  have key := deformCr D.HL.subtype hH.isOpenEmbedding_subtypeVal (glOn D.HL r h1)
    (hr.comp continuous_subtype_val) _ hy (glOn D.HL r' h1') (fun g i j => (hd g).2 i j) ⊤ (by simp)
  rw [isLCr_iff D r' h1', isLCr_iff D r h1, ← crOn_top, ← crOn_top, key,
    z1fDesc (MonoidHom.id _) (adRep r) D.HL γ hγ, had, MonoidHom.id_comp]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCrystallinePeriodMatrixBcrisOfIsCrys
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology Polynomial

section Generic

open GlobalTheory.RegularRing GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module Qp V] [FiniteDimensional Qp V] [IsDomain B]

private theorem exists_inv_matrix (hf : FracInv PD) (hu : LineUnit PD) (ρ : Representation Qp G V) {d : ℕ}
    (v : Basis (Fin d) Qp V) (h : IsCrys PD ρ) :
    ∃ M M' : Matrix (Fin d) (Fin d) B, M * M' = 1 ∧
      ∀ g, (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) * M.map (PD.actB g) = M := by
  classical
  obtain ⟨h1, -⟩ := finite_le₀ PD hf ρ
  have h2 : finrank K₀ ↥(DcrisK₀ PD ρ) = d := by
    rw [(isCrys_iff_finrank PD ρ).1 h, finrank_eq_card_basis v, Fintype.card_fin]
  let d₀ := Module.finBasisOfFinrankEq K₀ ↥(DcrisK₀ PD ρ) h2
  let b := (Algebra.TensorProduct.basis B d₀).map
    (LinearEquiv.ofBijective _ (comparison_bijective PD hf hu ρ h))
  have hd : ∀ g i, sig PD ρ g (b i) = b i := by
    intro g i
    have : b i = (d₀ i : B ⊗[Qp] V) := by simp [b, comparison_tmul]
    rw [this]
    exact (mem_DcrisK₀ PD ρ _).1 (d₀ i).2 g
  let e := Algebra.TensorProduct.basis B v
  have hrep : ∀ g (w : B ⊗[Qp] V) k, e.repr (sig PD ρ g w) k =
      ∑ j, algebraMap Qp B (v.repr (ρ g (v j)) k) * PD.actB g (e.repr w j) := by
    intro g w k
    conv_lhs => rw [← e.sum_repr w]
    simp only [map_sum, sig_smul, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    congr 1
    simp [e, sig_tmul, Algebra.algebraMap_eq_smul_one]
  refine ⟨e.toMatrix b, b.toMatrix e, Basis.toMatrix_mul_toMatrix_flip _ _, fun g => ?_⟩
  ext k i
  rw [Matrix.mul_apply]
  change _ = e.repr (b i) k
  conv_rhs => rw [← hd g i, hrep]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [LinearMap.toMatrix_apply, Basis.toMatrix_apply]

private theorem exists_period_matrix (hf : FracInv PD) (hu : LineUnit PD) (ρ : Representation Qp G V) {d : ℕ}
    (v : Basis (Fin d) Qp V) (h : IsCrys PD ρ) :
    ∃ (M M' : Matrix (Fin d) (Fin d) B) (A : Matrix (Fin d) (Fin d) K₀), M * M' = 1 ∧ IsUnit A.det ∧
      M.map PD.φ = M * A.map (algebraMap K₀ B) ∧
      ∀ g, (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) * M.map (PD.actB g) = M := by
  obtain ⟨M, M', hM, hg⟩ := exists_inv_matrix PD hf hu ρ v h
  have hM' : M' * M = 1 := mul_eq_one_comm.1 hM
  have hinv : ∀ g, (M' * M.map PD.φ).map (PD.actB g) = M' * M.map PD.φ := by
    intro g
    set R := (LinearMap.toMatrix v v (ρ g)).map (algebraMap Qp B) with hR
    have h1 : M.map (PD.actB g) * M'.map (PD.actB g) = 1 := by
      rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : M'.map (PD.actB g) = M' * R := by
      have : R * (M.map (PD.actB g) * M'.map (PD.actB g)) = M * M'.map (PD.actB g) := by
        rw [← Matrix.mul_assoc, hg g]
      rw [h1, Matrix.mul_one] at this
      rw [this, ← Matrix.mul_assoc, hM', Matrix.one_mul]
    have h3 : R * (M.map PD.φ).map (PD.actB g) = M.map PD.φ := by
      have h4 : R.map PD.φ = R := by
        ext i j
        simp [hR]
      have h5 : (M.map PD.φ).map (PD.actB g) = (M.map (PD.actB g)).map PD.φ := by
        ext i j
        simp [PD.φ_comm]
      rw [h5, ← h4, ← Matrix.map_mul, hg g]
    rw [Matrix.map_mul, h2, Matrix.mul_assoc, h3]
  choose A hA using fun i j => PD.invB ((M' * M.map PD.φ) i j) fun g => congrFun (congrFun (hinv g) i) j
  have hA' : (Matrix.of A).map (algebraMap K₀ B) = M' * M.map PD.φ := by
    ext i j
    exact hA i j
  refine ⟨M, M', Matrix.of A, hM, ?_, by rw [hA', ← Matrix.mul_assoc, hM, Matrix.one_mul], hg⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have h1 : ((Matrix.of A).map (algebraMap K₀ B)).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have h2 : (M' * M.map PD.φ) * (M'.map PD.φ * M) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (M.map PD.φ), ← Matrix.map_mul, hM,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, hM']
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_mul, ← hA', h1, zero_mul, Matrix.det_one] at h3
  exact zero_ne_one h3

end Generic

theorem UpperTheory.exists_crystalline_period_matrix_bcris_of_isCrys :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V), IsCrys ((PP l).PD K) ρ → ∃ (M M' : Matrix (Fin d) (Fin d) (Bcr l)) (A : Matrix (Fin d) (Fin d) ↥(K0 K)), M * M' = 1 ∧ IsUnit A.det ∧ M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) ∧ (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) := by
  intro l _ K V _ _ _ ρ d e h
  obtain ⟨T⟩ := tiedP l
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  obtain ⟨M, M', A, h1, h2, h3, h4⟩ := exists_period_matrix ((PP l).PD K)
    (GlobalTheory.TateDualCrys.fracInv_of_tied T K) (GlobalTheory.TateDualCrys.lineUnit_of_tied T K) ρ e h
  refine ⟨M, M', A, h1, h2, ?_, fun g => ?_⟩
  · rw [← h3]
    ext i j
    exact ((PP l).PD_φ K _).symm
  · have h5 : M.map ((PP l).actQ (g : GQ l)) = M.map (((PP l).PD K).actB g) := by
      ext i j
      exact ((PP l).PD_actB K g _).symm
    rw [h5, h4]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineTriangularIffOfCharData
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

private theorem coc {G B : Type} [Group G] [CommRing B] (a b : G →* Bˣ) (x : G → B) (g h : G)
    (H : x (g * h) * (b (g * h) : B) = (a g : B) * (x h * b h) + x g * b g * b h) :
    x (g * h) = x g + ((a / b) g : Bˣ) * x h := by
  have e : (((a / b) g : Bˣ) : B) * b g = a g := by
    rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
  refine (b (g * h)).mul_left_inj.1 ?_
  rw [H, map_mul, Units.val_mul, ← e]
  ring

theorem UpperTheory.isCrystalline_triangular_iff_of_charData :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {e : ℕ} {ψ : G →* Eˣ} {κ : Fin 3 → G →* Bˣ}, Chars φ π e ψ κ → ∀ (x y z : G → B) (ρ : G →* GL (Fin 3) B), Continuous x → Continuous y → Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) → IsCr φ (colRep ρ) → x ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 0 / κ 1)) ∧ y ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 1 / κ 2)) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π _ e ψ κ hκ x y z ρ hx hy hz hρ hcr
  have hm : ∀ g h, triM (fun i => κ i (g * h)) (x (g * h)) (y (g * h)) (z (g * h)) =
      triM (fun i => κ i g) (x g) (y g) (z g) * triM (fun i => κ i h) (x h) (y h) (z h) := fun g h => by
    rw [← hρ, ← hρ, ← hρ, map_mul, Units.val_mul]
  have cx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h := fun g h => by
    refine coc _ _ _ g h ?_
    have := congrFun (congrFun (hm g h) 0) 1
    simpa [triM, Matrix.mul_apply, Fin.sum_univ_three] using this
  have cy : ∀ g h, y (g * h) = y g + ((κ 1 / κ 2) g : Bˣ) * y h := fun g h => by
    refine coc _ _ _ g h ?_
    have := congrFun (congrFun (hm g h) 1) 2
    simpa [triM, Matrix.mul_apply, Fin.sum_univ_three] using this
  have hch : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ (chRep (κ i)) (contAction_chRep (hκ.cont i)) ((e : ℤ) * wt1 i) fun g hg v => by
      rw [chRep_apply, hκ.ine g hg i, smul_eq_mul]
  have hc : ContAction (colRep ρ) := contAction_colRep (by
    simp only [hρ]
    exact continuous_triM (t := fun g i => κ i g) hκ.cont hx hy hz)
  let f1 : (B × B) →ₗ[ℚ_[l]] (Fin 3 → B) :=
    { toFun := fun v => ![v.1, v.2, 0]
      map_add' := fun v w => by ext i; fin_cases i <;> simp
      map_smul' := fun c v => by ext i; fin_cases i <;> simp }
  let f2 : (Fin 3 → B) →ₗ[ℚ_[l]] (B × B) :=
    { toFun := fun v => (v 1, v 2)
      map_add' := fun v w => rfl
      map_smul' := fun c v => rfl }
  refine ⟨(UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ.cont 0) (hκ.cont 1) x cx hx (hch 0) (hch 1)).1 ?_,
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ.cont 1) (hκ.cont 2) y cy hy (hch 1) (hch 2)).1 ?_⟩
  · refine ((isCrys_isDR_sub_quot φ hφ _ _ (contAction_charExtension_of_continuous_cocycle (hκ.cont 0) (hκ.cont 1) cx hx) hc f1 fun g v => ?_).1
      fun v w h => ?_).1 hcr
    · rw [colRep_apply, hρ, characterExtensionRep_apply]
      ext i
      fin_cases i <;> simp [f1, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · exact Prod.ext (congrFun h 0) (congrFun h 1)
  · refine ((isCrys_isDR_sub_quot φ hφ _ _ hc (contAction_charExtension_of_continuous_cocycle (hκ.cont 1) (hκ.cont 2) cy hy) f2 fun g v => ?_).2
      fun v => ⟨![0, v.1, v.2], rfl⟩).1 hcr
    rw [colRep_apply, hρ, characterExtensionRep_apply]
    ext <;> simp [f2, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
end

