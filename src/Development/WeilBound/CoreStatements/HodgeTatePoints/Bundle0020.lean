import Mathlib
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.Bundle0001
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.RgProd
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace PositivityTheory.HtPt.Rg

open scoped TensorProduct

section
variable {R : Type} [CommRing R] {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G']

theorem lift_mul' {X : Over (Spec (CommRingCat.of R))} (a b : X ⟶ G) (a' b' : X ⟶ G') :
    lift (a * b) (a' * b') = lift a a' * lift b b' := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [MonObj.mul_comp]
  · simp [MonObj.mul_comp]

theorem pow_eq_one_iff' {X : Over (Spec (CommRingCat.of R))} (z : X ⟶ G ⊗ G') (p : ℕ) :
    z ^ p = 1 ↔ (z ≫ fst G G') ^ p = 1 ∧ (z ≫ snd G G') ^ p = 1 := by
  have key : z ^ p = lift ((z ≫ fst G G') ^ p) ((z ≫ snd G G') ^ p) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.pow_comp]
  have one : (1 : X ⟶ G ⊗ G') = lift 1 1 := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.one_comp]
  rw [key, one]
  constructor
  · intro h
    exact ⟨by simpa using congrArg (· ≫ fst G G') h, by simpa using congrArg (· ≫ snd G G') h⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

theorem lift_right {A B S : Type} [CommRing A] [CommRing B] [CommRing S] [Algebra R A] [Algebra R B]
    [Algebra R S] (f : A →ₐ[R] S) (g : B →ₐ[R] S) (h : ∀ x y, Commute (f x) (g y)) :
    (Algebra.TensorProduct.lift f g h).comp Algebra.TensorProduct.includeRight = g :=
  Algebra.TensorProduct.lift_comp_includeRight f g h

variable {p : ℕ}

def prodPt (T : TorsRep G p) (T' : TorsRep G' p) : sp (R₀ := R) (T.A ⊗[R] T'.A) ⟶ G ⊗ G' :=
  lift (spMap (Algebra.TensorProduct.includeLeft : T.A →ₐ[R] T.A ⊗[R] T'.A) ≫ T.y)
    (spMap (Algebra.TensorProduct.includeRight : T'.A →ₐ[R] T.A ⊗[R] T'.A) ≫ T'.y)

theorem prodPt_iff (T : TorsRep G p) (T' : TorsRep G' p) {S : Type} [CommRing S] [Algebra R S]
    (φ : T.A ⊗[R] T'.A →ₐ[R] S) (z : sp (R₀ := R) S ⟶ G ⊗ G') :
    spMap φ ≫ prodPt T T' = z ↔
      spMap (φ.comp Algebra.TensorProduct.includeLeft) ≫ T.y = z ≫ fst G G' ∧
      spMap (φ.comp Algebra.TensorProduct.includeRight) ≫ T'.y = z ≫ snd G G' := by
  constructor
  · rintro rfl
    refine ⟨?_, ?_⟩
    · rw [prodPt, Category.assoc, lift_fst, ← Category.assoc, Chart.spMap_comp]
    · rw [prodPt, Category.assoc, lift_snd, ← Category.assoc, Chart.spMap_comp]
  · rintro ⟨h1, h2⟩
    apply CartesianMonoidalCategory.hom_ext
    · rw [prodPt, Category.assoc, lift_fst, ← Category.assoc, Chart.spMap_comp, h1]
    · rw [prodPt, Category.assoc, lift_snd, ← Category.assoc, Chart.spMap_comp, h2]

def prodRep (T : TorsRep G p) (T' : TorsRep G' p) : TorsRep (G ⊗ G') p where
  A := T.A ⊗[R] T'.A
  free := by
    have := T.free
    have := T'.free
    infer_instance
  fin := by
    have := T.fin
    have := T'.fin
    infer_instance
  y := prodPt T T'
  y_p := by
    rw [pow_eq_one_iff', prodPt, lift_fst, lift_snd, ← MonObj.comp_pow, ← MonObj.comp_pow, T.y_p, T'.y_p]
    exact ⟨MonObj.comp_one _, MonObj.comp_one _⟩
  univ := by
    intro S _ _ z hz
    rw [pow_eq_one_iff'] at hz
    obtain ⟨φ, hφ, uφ⟩ := T.univ S _ hz.1
    obtain ⟨ψ, hψ, uψ⟩ := T'.univ S _ hz.2
    refine ⟨Algebra.TensorProduct.lift φ ψ fun _ _ => Commute.all _ _, ?_, ?_⟩
    · show _ ≫ _ = _
      rw [prodPt_iff, Algebra.TensorProduct.lift_comp_includeLeft, lift_right]
      exact ⟨hφ, hψ⟩
    · intro χ hχ
      obtain ⟨h, h'⟩ := (prodPt_iff T T' χ z).1 hχ
      apply Algebra.TensorProduct.ext
      · rw [Algebra.TensorProduct.lift_comp_includeLeft]
        exact uφ _ h
      · exact (uψ _ h').trans (Algebra.TensorProduct.lift_comp_includeRight _ _ _).symm

theorem isTorsPts_prod {N N' : Type} [AddCommGroup N] [AddCommGroup N']
    {pt : N → (sp (R₀ := R) R ⟶ G)} {pt' : N' → (sp (R₀ := R) R ⟶ G')}
    (h : IsTorsPts G p pt) (h' : IsTorsPts G' p pt') :
    IsTorsPts (G ⊗ G') p (fun z : N × N' => lift (pt z.1) (pt' z.2)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, a'⟩ ⟨b, b'⟩ e
    have e1 := congrArg (· ≫ fst G G') e
    have e2 := congrArg (· ≫ snd G G') e
    simp only [lift_fst, lift_snd] at e1 e2
    exact Prod.ext (h.inj e1) (h'.inj e2)
  · rintro ⟨a, a'⟩ ⟨b, b'⟩
    simp only [Prod.fst_add, Prod.snd_add, h.add, h'.add]
    exact lift_mul' _ _ _ _
  · intro z
    rw [pow_eq_one_iff', h.range, h'.range]
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      refine ⟨(a, b), ?_⟩
      apply CartesianMonoidalCategory.hom_ext <;> simp [ha, hb]
    · rintro ⟨⟨a, b⟩, rfl⟩
      exact ⟨⟨a, by simp⟩, ⟨b, by simp⟩⟩

theorem exists_ev (T : TorsRep G p) {N : Type} [AddCommGroup N] {pt : N → (sp (R₀ := R) R ⟶ G)}
    (h : IsTorsPts G p pt) : ∃ e : N → (T.A →ₐ[R] R), (∀ x, spMap (e x) ≫ T.y = pt x) ∧
      ∀ x φ, spMap φ ≫ T.y = pt x → φ = e x := by
  choose e he ue using fun x => T.univ R (pt x) ((h.range _).2 ⟨x, rfl⟩)
  exact ⟨e, he, ue⟩

theorem mem_torsFun_iff {C : Type} [Field C] [Algebra R C] (T : TorsRep G p) {N : Type}
    {pt : N → (sp (R₀ := R) R ⟶ G)} {e : N → (T.A →ₐ[R] R)} (he : ∀ x, spMap (e x) ≫ T.y = pt x)
    (ue : ∀ x φ, spMap φ ≫ T.y = pt x → φ = e x) (f : N → C) :
    f ∈ torsFun C T pt ↔ ∃ a : T.A, f = fun x => algebraMap R C (e x a) := by
  show (∃ a : T.A, ∀ x φ, spMap φ ≫ T.y = pt x → f x = algebraMap R C (φ a)) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, funext fun x => ha x (e x) (he x)⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a, fun x φ hφ => ?_⟩
    rw [ue x φ hφ]

theorem torsFun_prod (C : Type) [Field C] [Algebra R C] (T : TorsRep G p) (T' : TorsRep G' p)
    {N N' : Type} [AddCommGroup N] [AddCommGroup N']
    {pt : N → (sp (R₀ := R) R ⟶ G)} {pt' : N' → (sp (R₀ := R) R ⟶ G')}
    (h : IsTorsPts G p pt) (h' : IsTorsPts G' p pt') :
    torsFun C (prodRep T T') (fun z : N × N' => lift (pt z.1) (pt' z.2)) =
      tens (torsFun C T pt) (torsFun C T' pt') := by
  obtain ⟨e, he, ue⟩ := exists_ev T h
  obtain ⟨e', he', ue'⟩ := exists_ev T' h'
  let E : N × N' → (T.A ⊗[R] T'.A →ₐ[R] R) := fun z =>
    Algebra.TensorProduct.lift (e z.1) (e' z.2) (fun _ _ => Commute.all _ _)
  have hE : ∀ z, spMap (E z) ≫ (prodRep T T').y = lift (pt z.1) (pt' z.2) := by
    intro z
    show spMap (E z) ≫ prodPt T T' = _
    rw [prodPt_iff]
    refine ⟨?_, ?_⟩
    · simp only [E]
      rw [Algebra.TensorProduct.lift_comp_includeLeft, he, lift_fst]
    · simp only [E]
      rw [lift_right, he', lift_snd]
  have uE : ∀ z (φ : T.A ⊗[R] T'.A →ₐ[R] R), spMap φ ≫ (prodRep T T').y = lift (pt z.1) (pt' z.2) →
      φ = E z := by
    intro z φ hφ
    obtain ⟨h1, h2⟩ := (prodPt_iff T T' φ _).1 hφ
    rw [lift_fst] at h1
    rw [lift_snd] at h2
    apply Algebra.TensorProduct.ext
    · simp only [E]
      rw [Algebra.TensorProduct.lift_comp_includeLeft]
      exact ue _ _ h1
    · exact (ue' _ _ h2).trans (lift_right (e z.1) (e' z.2) (fun _ _ => Commute.all _ _)).symm
  have hS := mem_torsFun_iff (C := C) T he ue
  have hS' := mem_torsFun_iff (C := C) T' he' ue'
  have hP := mem_torsFun_iff (C := C) (prodRep T T') hE uE
  have hten : ∀ (z : N × N') (a : T.A) (b : T'.A),
      algebraMap R C (E z (a ⊗ₜ[R] b)) = algebraMap R C (e z.1 a) * algebraMap R C (e' z.2 b) := by
    intro z a b
    simp [E]
  have aux : ∀ t : T.A ⊗[R] T'.A,
      (fun z : N × N' => algebraMap R C (E z t)) ∈ tens (torsFun C T pt) (torsFun C T' pt') := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero =>
      have h0 : (fun z : N × N' => algebraMap R C (E z 0)) = 0 := by
        funext z
        simp
      rw [h0]
      exact zero_mem _
    | tmul a b =>
      apply Submodule.subset_span
      refine ⟨fun x => algebraMap R C (e x a), (hS _).2 ⟨a, rfl⟩,
        fun x => algebraMap R C (e' x b), (hS' _).2 ⟨b, rfl⟩, ?_⟩
      funext z
      exact hten z a b
    | add s t hs ht =>
      have h2 : (fun z : N × N' => algebraMap R C (E z (s + t))) =
          (fun z => algebraMap R C (E z s)) + (fun z => algebraMap R C (E z t)) := by
        funext z
        simp
      rw [h2]
      exact add_mem hs ht
  apply le_antisymm
  · intro f hf
    obtain ⟨t, rfl⟩ := (hP f).1 hf
    exact aux t
  · unfold tens
    rw [Submodule.span_le]
    rintro F ⟨g, hg, k, hk, rfl⟩
    obtain ⟨a, rfl⟩ := (hS g).1 hg
    obtain ⟨b, rfl⟩ := (hS' k).1 hk
    exact (hP _).2 ⟨(a ⊗ₜ[R] b : T.A ⊗[R] T'.A), funext fun z => (hten z a b).symm⟩

end

end PositivityTheory.HtPt.Rg
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfFin
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Twhopf

theorem finite_part : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  intro R _ _ X f _ _ _ _
  exact ⟨GlobalTheory.finitePart f, GlobalTheory.isFinite_finitePart (R := CommRingCat.of R) f,
    GlobalTheory.mem_finitePart_of_eq_closedPoint (R := CommRingCat.of R) f⟩

theorem finite_le : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' := by
  intro R _ _ X f U U' hU hU' x hx
  exact (GlobalTheory.preimage_eq_top_of_closedFibre_subset (R := CommRingCat.of R) f U' hU' U.ι).ge
    (Set.mem_univ ⟨x, hx⟩)

theorem mem_of_finite {R : Type} [CommRing R] [IsLocalRing R]
    {X : Over (Spec (CommRingCat.of R))} (W : X.left.Opens)
    (hW : ∀ x : X.left, X.hom x = IsLocalRing.closedPoint R → x ∈ W)
    (Y : Over (Spec (CommRingCat.of R))) (hY : IsFinite Y.hom) (h : Y ⟶ X) (z : Y.left) :
    h.left z ∈ W := by
  haveI : IsFinite (h.left ≫ X.hom) := by rw [Over.w h]; exact hY
  exact (GlobalTheory.preimage_eq_top_of_closedFibre_subset (R := CommRingCat.of R) X.hom W hW h.left).ge
    (Set.mem_univ z)

theorem finite_sub : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) → Γ.IsFinOpenSub U := by
  intro R _ _ _ T _ Γ U hfin hU
  haveI := hfin
  have hV : IsFinite (openOver Γ.G U).hom := hfin
  haveI := hV
  refine ⟨hfin, ?_, ?_, ?_⟩
  · intro x
    refine mem_of_finite U hU (𝟙_ _) ?_ η[Γ.G] x
    show IsFinite (𝟙 _)
    infer_instance
  · intro S x y hx hy z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    obtain ⟨y', rfl⟩ := exists_factor_openIncl U y hy
    have hP : IsFinite (openOver Γ.G U ⊗ openOver Γ.G U).hom := by
      rw [Over.tensorObj_hom]
      infer_instance
    have key := mem_of_finite U hU _ hP
      ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U))
    have heq : x' ≫ openIncl Γ.G U * y' ≫ openIncl Γ.G U =
        lift x' y' ≫ ((fst _ _ ≫ openIncl Γ.G U) * (snd _ _ ≫ openIncl Γ.G U)) := by
      rw [comp_mul]
      simp
    rw [heq]
    simpa using key ((lift x' y').left z)
  · intro S x hx z
    obtain ⟨x', rfl⟩ := exists_factor_openIncl U x hx
    have key := mem_of_finite U hU _ hV (openIncl Γ.G U)⁻¹
    have heq : (x' ≫ openIncl Γ.G U)⁻¹ = x' ≫ (openIncl Γ.G U)⁻¹ := by
      simp [Hom.inv_def]
    rw [heq]
    simpa using key (x'.left z)

theorem mem_iff_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ g : Γ.G.left, Γ.G.hom g = IsLocalRing.closedPoint R → g ∈ U) → ∀ t, (⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U ↔ ∃ σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G, toUnit (genPt R) ≫ σ = Γ.pt t) := by
  intro R _ _ _ _ T _ _ Γ U hfin hU t
  constructor
  · intro ht
    obtain ⟨σ, -, hσ⟩ := exists_section_of_generic_point R T Γ U hfin t ht
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, hσ⟩ z _
    have key := mem_of_finite U hU (𝟙_ _) (show IsFinite (𝟙 _) from inferInstance) σ
      ((toUnit (genPt R)).left z)
    rw [← hσ]
    simpa using key

open Polynomial in

theorem exists_root_near (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)]
    (a₀ : V) (n : ℕ) : ∀ f : V[X], f.Monic → f.natDegree = n → f.eval a₀ ∈ IsLocalRing.maximalIdeal V →
      ∃ a, f.IsRoot a ∧ a - a₀ ∈ IsLocalRing.maximalIdeal V := by
  induction n with
  | zero =>
    intro f hf hn h
    rw [hf.natDegree_eq_zero.1 hn, eval_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) (IsLocalRing.maximalIdeal.isMaximal V).ne_top
  | succ n ih =>
    intro f hf hn h
    have hinj := IsFractionRing.injective V (FractionRing V)
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective (FractionRing V) hinj f
      (by rw [degree_eq_natDegree hf.ne_zero, hn]; exact_mod_cast n.succ_ne_zero)
    obtain ⟨r, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 (⟨f, hf, by rwa [← aeval_def]⟩ : IsIntegral V x)
    have hr : f.IsRoot r := hinj (by rw [map_zero, ← hx, aeval_algebraMap_apply_eq_algebraMap_eval])
    obtain ⟨g, rfl⟩ := dvd_iff_isRoot.2 hr
    have hg : g.Monic := (monic_X_sub_C r).of_mul_monic_left hf
    rw [eval_mul] at h
    rcases (IsLocalRing.maximalIdeal.isMaximal V).isPrime.mem_or_mem h with h | h
    · refine ⟨r, hr, ?_⟩
      have := neg_mem h
      simpa using this
    · have hd : g.natDegree = n := by
        rw [(monic_X_sub_C r).natDegree_mul hg, natDegree_X_sub_C] at hn
        omega
      obtain ⟨a, ha, ha'⟩ := ih g hg hd h
      exact ⟨a, ha.dvd (dvd_mul_left _ _), ha'⟩

theorem henselian_of_algClosed : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)], HenselianLocalRing V := by
  intro V _ _ _ _
  exact ⟨fun f hf a₀ h _ => exists_root_near V a₀ _ f hf rfl h⟩

theorem padic_alg : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O), Nonempty (Algebra ℤ_[p] O) ∧ HenselianLocalRing O ∧ IsIntegrallyClosed O ∧ ValuationRing O ∧ IsAlgClosed (FractionRing O) ∧ IsFractionRing O C := by
  intro p _ C _ _ _ v O _ _ _ hv _ hO
  haveI := hO
  haveI hval : ValuationRing O := ValuationRing.of_integers v hv
  haveI hfr : IsFractionRing O C := hv.isFractionRing
  haveI hac : IsAlgClosed (FractionRing O) :=
    IsAlgClosed.of_ringEquiv C _ (FractionRing.algEquiv O C).symm.toRingEquiv
  exact ⟨(GlobalTheory.ChF.padicInt_algebra_of_isAdicComplete_and_matrix_unique p O).1,
    henselian_of_algClosed O, inferInstance, hval, hac, hfr⟩

theorem prime_eq_bot_or_max : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] [IsLocalRing O], v.Integers O → ∀ P : Ideal O, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal O := by
  intro C _ v O _ _ _ _ hv P hP
  by_cases h0 : P = ⊥
  · exact .inl h0
  right
  refine le_antisymm (IsLocalRing.le_maximalIdeal hP.ne_top) fun x hx => ?_
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have hx1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_of_one' h)
  have ha : 0 < v (algebraMap O C a) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff v).2 ((map_ne_zero_iff _ hv.hom_inj).2 ha0))
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one ha hx1
  have hd : a ∣ x ^ n := hv.dvd_of_le (by rw [map_pow, map_pow]; exact hn.le)
  exact hP.mem_of_pow_mem n (P.mem_of_dvd hd haP)

end PositivityTheory.HtPt.Twhopf
end

