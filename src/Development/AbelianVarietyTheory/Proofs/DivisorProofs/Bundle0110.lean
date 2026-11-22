import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemPowSucc
section
namespace GlobalTheory.AlgEquivTrivialPowerCongruence

theorem sub_mem_pow_succ {B : Type} [CommRing B] (Q : Ideal B) (ρ : B →+* B)
    (h0 : ∀ x, ρ x - x ∈ Q) (h1 : ∀ x ∈ Q, ρ x - x ∈ Q ^ 2) :
    ∀ (k : ℕ), ∀ x ∈ Q ^ k, ρ x - x ∈ Q ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro x _; simpa using h0 x
  | succ k ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha q hq
      have hd := ih a ha
      have hρa : ρ a ∈ Q ^ k := by
        have h2 : ρ a - a ∈ Q ^ k := Ideal.pow_le_pow_right (Nat.le_succ k) hd
        have h3 := Ideal.add_mem _ h2 ha
        simpa using h3
      have e : ρ (a * q) - a * q = ρ a * (ρ q - q) + (ρ a - a) * q := by
        rw [map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · have h4 := Ideal.mul_mem_mul hρa (h1 q hq)
        rw [← pow_add] at h4
        exact h4
      · have h4 := Ideal.mul_mem_mul hd hq
        rw [← pow_succ] at h4
        exact h4
    · intro a b ha hb
      have e : ρ (a + b) - (a + b) = (ρ a - a) + (ρ b - b) := by
        rw [map_add]; ring
      rw [e]
      exact Ideal.add_mem _ ha hb

theorem algEquiv_eq_one (A B : Type) [CommRing A] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Algebra A B] (Q : Ideal B) (ρ : B ≃ₐ[A] B) (m : ℕ) (hQ : Q ≠ ⊤) (hm : IsUnit (m : B))
    (hρ : ρ ^ m = 1) (h0 : ∀ x : B, ρ x - x ∈ Q) (h1 : ∀ x ∈ Q, ρ x - x ∈ Q ^ 2) :
    ρ = 1 := by
  have step : ∀ (k : ℕ), ∀ x ∈ Q ^ k, ρ x - x ∈ Q ^ (k + 1) :=
    sub_mem_pow_succ Q (ρ : B →+* B) h0 h1
  have key : ∀ (k : ℕ) (x : B), ρ x - x ∈ Q ^ k := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have hy := ih x
      have hj : ∀ j : ℕ, (ρ ^ j) x - x - (j : B) * (ρ x - x) ∈ Q ^ (k + 1) := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
          have hz := step (k + 1) _ ihj
          have hz' := Ideal.add_mem _ (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)) hz) ihj
          rw [sub_add_cancel] at hz'
          have hw := Ideal.mul_mem_left _ (j : B) (step k _ hy)
          have h5 := Ideal.add_mem _ hz' hw
          convert h5 using 1
          rw [pow_succ', AlgEquiv.mul_apply]
          simp only [map_sub, map_mul, map_natCast]
          push_cast
          ring
      have hmm := hj m
      rw [hρ] at hmm
      simp only [AlgEquiv.one_apply, sub_self, zero_sub, neg_mem_iff] at hmm
      exact (Ideal.unit_mul_mem_iff_mem _ hm).1 hmm
  have hbot : ⨅ k : ℕ, Q ^ k = ⊥ := Ideal.iInf_pow_eq_bot_of_isDomain Q hQ
  ext x
  have hx : ρ x - x ∈ ⨅ k : ℕ, Q ^ k := Ideal.mem_iInf.2 fun k => key k x
  rw [hbot, Ideal.mem_bot, sub_eq_zero] at hx
  simpa using hx

end GlobalTheory.AlgEquivTrivialPowerCongruence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubNatCompSubIncl
section
open AlgebraicGeometry CategoryTheory Limits Opposite

namespace GlobalTheory.QcSub

variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)

def gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) : Subring (F.obj (op W)) :=
  Subring.closure (Set.range (α.app (op W)).hom ∪ (F.map (homOfLE h).op).hom '' T)

lemma algebraMap_mem_gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) (r : Γ(X, W)) :
    (α.app (op W)).hom r ∈ gen F α h T :=
  Subring.subset_closure (Or.inl ⟨r, rfl⟩)

lemma res_mem_gen {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) {t : F.obj (op V)}
    (ht : t ∈ T) : (F.map (homOfLE h).op).hom t ∈ gen F α h T :=
  Subring.subset_closure (Or.inr ⟨t, ht, rfl⟩)

lemma map_gen_le {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (T : Set (F.obj (op V))) :
    (gen F α h T).map (F.map (homOfLE h').op).hom ≤ gen F α (h'.trans h) T := by
  rw [gen, RingHom.map_closure, Subring.closure_le]
  rintro _ ⟨y, (⟨r, rfl⟩ | ⟨t, ht, rfl⟩), rfl⟩
  · have := congr($(α.naturality (homOfLE h').op).hom r)
    simp only [CommRingCat.comp_apply] at this
    rw [← this]
    exact algebraMap_mem_gen F α _ T _
  · rw [← CommRingCat.comp_apply, ← F.map_comp]
    exact res_mem_gen F α _ T ht

lemma res_mem_gen_of_mem {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (T : Set (F.obj (op V)))
    {b : F.obj (op W)} (hb : b ∈ gen F α h T) :
    (F.map (homOfLE h').op).hom b ∈ gen F α (h'.trans h) T :=
  map_gen_le F α h h' T ⟨b, hb, rfl⟩

lemma gen_eq_adjoin {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) :
    letI := (α.app (op W)).hom.toAlgebra
    gen F α h T = (Algebra.adjoin Γ(X, W) ((F.map (homOfLE h).op).hom '' T)).toSubring := by
  letI := (α.app (op W)).hom.toAlgebra
  rw [Algebra.adjoin_eq_ring_closure]
  rfl

variable {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))

def sub (W : X.Opens) : Subring (F.obj (op W)) :=
  ⨅ (j : ι) (W' : X.Opens) (_ : IsAffineOpen W') (hW : W' ≤ W) (hV : W' ≤ V j),
    (gen F α hV (T j)).comap (F.map (homOfLE hW).op).hom

lemma mem_sub {W : X.Opens} {b : F.obj (op W)} :
    b ∈ sub F α V T W ↔ ∀ (j : ι) (W' : X.Opens), IsAffineOpen W' → ∀ (hW : W' ≤ W)
      (hV : W' ≤ V j), (F.map (homOfLE hW).op).hom b ∈ gen F α hV (T j) := by
  simp only [sub, Subring.mem_iInf, Subring.mem_comap]

lemma algebraMap_mem_sub (W : X.Opens) (r : Γ(X, W)) : (α.app (op W)).hom r ∈ sub F α V T W := by
  rw [mem_sub]
  intro j W' _ hW hV
  have := congr($(α.naturality (homOfLE hW).op).hom r)
  simp only [CommRingCat.comp_apply] at this
  rw [← this]
  exact algebraMap_mem_gen F α _ _ _

lemma res_mem_sub {W W₁ : X.Opens} (h : W₁ ≤ W) {b : F.obj (op W)} (hb : b ∈ sub F α V T W) :
    (F.map (homOfLE h).op).hom b ∈ sub F α V T W₁ := by
  rw [mem_sub] at hb ⊢
  intro j W' hW' hW hV
  rw [← CommRingCat.comp_apply, ← F.map_comp]
  exact hb j W' hW' (hW.trans h) hV

def subMap (W : X.Opens) : Γ(X, W) →+* sub F α V T W :=
  (α.app (op W)).hom.codRestrict _ (algebraMap_mem_sub F α V T W)

@[simps obj]
def subFunctor : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat where
  obj W := CommRingCat.of (sub F α V T W.unop.1)
  map {W W₁} f := CommRingCat.ofHom
    ((F.map ((Scheme.AffineZariskiSite.toOpensFunctor X).map f.unop).op).hom.restrict _ _
      (fun _ hb ↦ res_mem_sub F α V T _ hb))
  map_id W := by
    ext b
    change (F.map _).hom b.1 = b.1
    rw [Subsingleton.elim ((Scheme.AffineZariskiSite.toOpensFunctor X).map (𝟙 W).unop).op (𝟙 _)]
    erw [F.map_id]
    rfl
  map_comp {W₁ W₂ W₃} f g := by
    ext b
    change (F.map _).hom b.1 = (F.map _).hom ((F.map _).hom b.1)
    rw [← CommRingCat.comp_apply]
    erw [← F.map_comp]
    rfl

def subNat : (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ subFunctor F α V T where
  app W := CommRingCat.ofHom (subMap F α V T W.unop.1)
  naturality {W W₁} f := by
    ext r
    exact Subtype.ext congr($(α.naturality ((Scheme.AffineZariskiSite.toOpensFunctor X).map f.unop).op).hom r)

def subIncl : subFunctor F α V T ⟶ (Scheme.AffineZariskiSite.toOpensFunctor X).op ⋙ F where
  app W := CommRingCat.ofHom (sub F α V T W.unop.1).subtype
  naturality _ _ _ := rfl

lemma subNat_comp_subIncl :
    subNat F α V T ≫ subIncl F α V T = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α :=
  rfl

lemma subIncl_injective (W : X.AffineZariskiSiteᵒᵖ) : Function.Injective ((subIncl F α V T).app W).hom :=
  Subtype.val_injective

lemma isLocalizationAway
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    {W : X.Opens} (hW : IsAffineOpen W) (f : Γ(X, W)) :
    letI := (F.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    IsLocalization.Away ((α.app (op W)).hom f) (F.obj (op (X.basicOpen f))) :=
  Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway.mp hα ⟨W, hW⟩ f

end GlobalTheory.QcSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleFgOfLocallyLeFg
section
namespace GlobalTheory

theorem submodule_fg_of_locally_le_fg {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] (M : Submodule R A) (s : Set R) (hs : Ideal.span s = ⊤)
    (hE : ∀ g ∈ s, ∃ E : Finset A, ∀ b ∈ M, ∃ m : ℕ,
      algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A)) : M.FG := by
  classical
  obtain ⟨s0, hs0s, hs0⟩ := (Ideal.span_eq_top_iff_finite s).1 hs
  choose! E hEm using hE
  let T : Set A := ⋃ g ∈ (s0 : Set R), (E g : Set A)
  have hT : T.Finite := Set.Finite.biUnion s0.finite_toSet fun g _ => (E g).finite_toSet
  refine Submodule.FG.of_le (Submodule.fg_span hT) ?_
  intro b hb
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (s0 : Set R) hs0 b ?_
  intro g
  obtain ⟨m, hm⟩ := hEm g.1 (hs0s g.2) b hb
  refine ⟨m, ?_⟩
  have hle : Submodule.span R (E g.1 : Set A) ≤ Submodule.span R T :=
    Submodule.span_mono (Set.subset_biUnion_of_mem (u := fun g => (E g : Set A)) g.2)
  have : (g.1 ^ m) • b = algebraMap R A g.1 ^ m * b := by
    rw [Algebra.smul_def, map_pow]
  rw [this]
  exact hle hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonOfResidueFieldFibres
section
namespace GlobalTheory

open TensorProduct

open TensorProduct in
open TensorProduct in

theorem _root_.GlobalTheory.subsingleton_of_residueField_fibres (O Q : Type) [CommRing O]
    [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    (h : ∀ q : PrimeSpectrum O, Subsingleton (q.asIdeal.ResidueField ⊗[O] Q)) :
    Subsingleton Q := by
  rw [← Module.support_eq_empty_iff (R := O), Set.eq_empty_iff_forall_notMem]
  intro q hq
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hq
  exact not_nontrivial_iff_subsingleton.mpr (h q) hq

open TensorProduct in
open TensorProduct in
theorem _root_.GlobalTheory.surjective_of_fibre_rank (O M N : Type) [CommRing O] [AddCommGroup M]
    [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N)
    (h : ∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField
      (LinearMap.range (f.baseChange q.asIdeal.ResidueField)) =
      Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) :
    Function.Surjective f := by
  rw [← LinearMap.range_eq_top, ← Submodule.Quotient.subsingleton_iff]
  refine _root_.GlobalTheory.subsingleton_of_residueField_fibres O _ fun q => ?_
  have htop : LinearMap.range (f.baseChange q.asIdeal.ResidueField) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (h q)
  have hex := lTensor_exact q.asIdeal.ResidueField (LinearMap.exact_map_mkQ_range f)
    (Submodule.mkQ_surjective _)
  refine ⟨fun y y' => ?_⟩
  suffices ∀ y : q.asIdeal.ResidueField ⊗[O] (N ⧸ LinearMap.range f), y = 0 by
    rw [this y, this y']
  intro y
  obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective q.asIdeal.ResidueField
    (Submodule.mkQ_surjective (LinearMap.range f)) y
  have hx : x ∈ LinearMap.range (f.baseChange q.asIdeal.ResidueField) := htop ▸ Submodule.mem_top
  obtain ⟨z, rfl⟩ := hx
  rw [LinearMap.baseChange_eq_ltensor]
  exact hex.apply_apply_eq_zero z

theorem injective_of_fibre_rank (O M N : Type) [CommRing O] [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N)
    [Module.Finite O M] [Module.Projective O N] (hf : Function.Surjective f)
    (h : ∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField
      (TensorProduct O q.asIdeal.ResidueField M) =
      Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) :
    Function.Injective f := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf

  have hsurj : Function.Surjective s := by
    apply surjective_of_fibre_rank O N M s
    intro q
    have hinj : Function.Injective (s.baseChange q.asIdeal.ResidueField) := by
      apply Function.LeftInverse.injective (g := f.baseChange q.asIdeal.ResidueField)
      intro x
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hs]
      simp
    rw [LinearMap.finrank_range_of_inj hinj, h q]
  intro a b hab
  obtain ⟨x, rfl⟩ := hsurj a
  obtain ⟨y, rfl⟩ := hsurj b
  have hx : f (s x) = x := LinearMap.congr_fun hs x
  have hy : f (s y) = y := LinearMap.congr_fun hs y
  rw [hx, hy] at hab
  rw [hab]

theorem surjective_injective_of_fibre_rank :
    ∀ (O M N : Type) [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] [Module.Finite O N] (f : M →ₗ[O] N), ((∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField (LinearMap.range (f.baseChange q.asIdeal.ResidueField)) = Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) → Function.Surjective f) ∧ (Module.Finite O M → Module.Projective O N → Function.Surjective f → (∀ q : PrimeSpectrum O, Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField M) = Module.finrank q.asIdeal.ResidueField (TensorProduct O q.asIdeal.ResidueField N)) → Function.Injective f) := by
  intro O M N _ _ _ _ _ _ f
  exact ⟨surjective_of_fibre_rank O M N f,
    fun _ _ hf h => injective_of_fibre_rank O M N f hf h⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumBoundOfStepDiff
section
namespace GlobalTheory

theorem sum_bound_of_step_diff :
    ∀ (a : ℕ → ℕ) (d p C : ℕ), 1 ≤ p →
      (∀ m : ℕ, a (m + p) ≤ a m + C * (d * (m + p + 1) ^ (d - 1))) →
      ∃ C' : ℕ, ∀ m : ℕ, a m ≤ C' * ((d + 1) * (m + 1) ^ d) := by
  intro a d p C hp h
  have key : ∀ m : ℕ, a m ≤ (∑ j ∈ Finset.range p, a j) + C * (d * (m + 1) ^ (d - 1)) * m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hm : m < p
      · exact le_trans (Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hm)) (Nat.le_add_right _ _)
      · obtain ⟨n, rfl⟩ : ∃ n, m = n + p := ⟨m - p, by omega⟩
        have h1 := ih n (by omega)
        have h2 := h n
        have h3 : C * (d * (n + 1) ^ (d - 1)) * n ≤ C * (d * (n + p + 1) ^ (d - 1)) * n := by
          gcongr
          omega
        have h4 : C * (d * (n + p + 1) ^ (d - 1)) * (n + 1)
            ≤ C * (d * (n + p + 1) ^ (d - 1)) * (n + p) := by
          gcongr
        rw [Nat.mul_succ] at h4
        omega
  refine ⟨(∑ j ∈ Finset.range p, a j) + C, fun m => (key m).trans ?_⟩
  have h1 : 1 ≤ (d + 1) * (m + 1) ^ d := Nat.succ_le_of_lt (by positivity)
  have h2 : d * (m + 1) ^ (d - 1) * m ≤ (d + 1) * (m + 1) ^ d := by
    cases d with
    | zero => simp
    | succ k =>
      rw [Nat.add_sub_cancel, pow_succ, mul_assoc]
      gcongr <;> omega
  rw [add_mul, mul_assoc C]
  exact add_le_add (Nat.le_mul_of_pos_right _ h1) (Nat.mul_le_mul_left _ h2)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFourSwap
section
namespace GlobalTheory.FourTermSumSwap

theorem sum_four_swap : ∀ {R α β : Type} [inst : AddCommMonoid R] [inst_1 : Fintype α] [inst_2 : Fintype β]
    (f : α → β → α → β → R),
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e := by
  intro R α β _ _ _ f
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ a : α, ∑ c : α, ∑ b : β, ∑ e : β, f a b c e :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ b : β, ∑ e : β, f a b c e := Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ e : β, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

end GlobalTheory.FourTermSumSwap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumHadamardPosDefPosSemidef
section
namespace GlobalTheory

open Matrix in

theorem sum_hadamard_posDef_posSemidef :
    ∀ {r : ℕ} (S G : Matrix (Fin r) (Fin r) ℝ), S.PosDef → G.PosSemidef →
      0 ≤ ∑ i, ∑ j, S i j * G i j ∧ (G ≠ 0 → 0 < ∑ i, ∑ j, S i j * G i j) := by
  intro r S G hS hG
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hG
  have key : ∑ i, ∑ j, S i j * (∑ k, vecMulVec (v k) (star (v k))) i j
      = ∑ k, star (v k) ⬝ᵥ (S *ᵥ v k) := by
    simp only [Matrix.sum_apply, Finset.sum_apply, vecMulVec_apply, Pi.star_apply, star_trivial, dotProduct,
      mulVec, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have term : ∀ k, 0 ≤ star (v k) ⬝ᵥ (S *ᵥ v k) := fun k =>
    hS.posSemidef.dotProduct_mulVec_nonneg _
  rw [key]
  refine ⟨Finset.sum_nonneg fun k _ => term k, fun hne => ?_⟩
  have : ∃ k, v k ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne
    simp [h]
  obtain ⟨k, hk⟩ := this
  exact Finset.sum_pos' (fun k _ => term k) ⟨k, Finset.mem_univ _, hS.dotProduct_mulVec_pos hk⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumInnerMulInnerProj
section
noncomputable section

open scoped InnerProductSpace

namespace GlobalTheory.Pc3

section
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (L : Submodule ℂ U)
  [FiniteDimensional ℂ L]

theorem sum_inner_mul_inner_proj [L.HasOrthogonalProjection] (a c : U) :
    ∑ j, ⟪a, (stdOrthonormalBasis ℂ L j : U)⟫_ℂ * ⟪(stdOrthonormalBasis ℂ L j : U), c⟫_ℂ =
      ⟪a, c⟫_ℂ - ⟪a - L.starProjection a, c - L.starProjection c⟫_ℂ := by
  set e := stdOrthonormalBasis ℂ L
  have h1 : ∀ j, ⟪a, (e j : U)⟫_ℂ = ⟪(⟨L.starProjection a, L.starProjection_apply_mem a⟩ : L), e j⟫_ℂ := by
    intro j
    rw [Submodule.coe_inner]
    have := L.inner_starProjection_left_eq_right a (e j : U)
    rw [this, L.starProjection_eq_self_iff.2 (e j).2]
  have h2 : ∀ j, ⟪(e j : U), c⟫_ℂ = ⟪e j, (⟨L.starProjection c, L.starProjection_apply_mem c⟩ : L)⟫_ℂ := by
    intro j
    rw [Submodule.coe_inner]
    have := L.inner_starProjection_left_eq_right (e j : U) c
    rw [← this, L.starProjection_eq_self_iff.2 (e j).2]
  simp_rw [h1, h2]
  rw [e.sum_inner_mul_inner, Submodule.coe_inner]
  simp only
  have ha := L.sub_starProjection_mem_orthogonal a
  have hc := L.sub_starProjection_mem_orthogonal c
  have o1 : ⟪L.starProjection a, c - L.starProjection c⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (L.starProjection_apply_mem a) hc
  have o2 : ⟪a - L.starProjection a, L.starProjection c⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (L.starProjection_apply_mem c) ha
  have e1 : ⟪a, c⟫_ℂ = ⟪L.starProjection a + (a - L.starProjection a),
      L.starProjection c + (c - L.starProjection c)⟫_ℂ := by simp
  rw [e1, inner_add_left, inner_add_right, inner_add_right, o1, o2]
  ring

end

theorem conjDeriv : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (L : Submodule ℂ U) [FiniteDimensional ℂ L] (x y : ℝ → U →L[ℂ] U) (A : U →L[ℂ] U), x 0 = 1 → (∀ t v w, inner ℂ (x t v) (x t w) = inner ℂ v w) → (∀ t v w, inner ℂ v (y t w) = inner ℂ (x t v) w) → (∀ v ∈ L, ∃ w, HasDerivAt (fun t => x t v) w 0) → (∀ u, A u ∈ L) → (∀ u, ContinuousLinearMap.adjoint A u ∈ L) → HasDerivAt (fun t => ∑ j, inner ℂ (stdOrthonormalBasis ℂ L j : U) (x t (A (y t (stdOrthonormalBasis ℂ L j : U))))) 0 0 := by
  intro U _ _ _ L _ x y A hx0 hxi hy hxd hA hAd
  set e := stdOrthonormalBasis ℂ L
  set E : Fin (Module.finrank ℂ L) → U := fun j => (e j : U)
  set b : Fin (Module.finrank ℂ L) → U := fun k => ContinuousLinearMap.adjoint A (E k)

  have hexp : ∀ u, A u = ∑ k, ⟪E k, A u⟫_ℂ • E k := by
    intro u
    have := e.sum_repr' (⟨A u, hA u⟩ : L)
    have h := congrArg (fun z : L => (z : U)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    exact h.symm
  have hterm : ∀ t, (∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) =
      ∑ k, (⟪x t (b k), x t (E k)⟫_ℂ - ⟪x t (b k) - L.starProjection (x t (b k)),
        x t (E k) - L.starProjection (x t (E k))⟫_ℂ) := by
    intro t
    have h1 : ∀ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ = ∑ k, ⟪x t (b k), E j⟫_ℂ * ⟪E j, x t (E k)⟫_ℂ := by
      intro j
      rw [hexp (y t (E j)), map_sum, inner_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, inner_smul_right, ← ContinuousLinearMap.adjoint_inner_left, hy]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact sum_inner_mul_inner_proj L _ _
  have hconst : ∀ t k, ⟪x t (b k), x t (E k)⟫_ℂ = ⟪b k, E k⟫_ℂ := fun t k => hxi t _ _
  simp_rw [hconst] at hterm
  have hfun : (fun t => ∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) = fun t =>
      (∑ k, ⟪b k, E k⟫_ℂ) - ∑ k, ⟪x t (b k) - L.starProjection (x t (b k)),
        x t (E k) - L.starProjection (x t (E k))⟫_ℂ := by
    funext t; rw [hterm t, Finset.sum_sub_distrib]
  show HasDerivAt (fun t => ∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) 0 0
  rw [hfun]
  have hbL : ∀ k, b k ∈ L := fun k => hAd _
  have hEL : ∀ k, E k ∈ L := fun k => (e k).2
  have hd : ∀ v ∈ L, ∃ w, HasDerivAt (fun t => x t v - L.starProjection (x t v)) w 0 ∧
      x 0 v - L.starProjection (x 0 v) = 0 := by
    intro v hv
    obtain ⟨w, hw⟩ := hxd v hv
    have hP : HasDerivAt (fun t => L.starProjection (x t v)) (L.starProjection w) 0 :=
      (L.starProjection.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hw
    refine ⟨w - L.starProjection w, hw.sub hP, ?_⟩
    rw [hx0, ContinuousLinearMap.one_apply, L.starProjection_eq_self_iff.2 hv, sub_self]
  have hsum : HasDerivAt (fun t => ∑ k, ⟪x t (b k) - L.starProjection (x t (b k)),
      x t (E k) - L.starProjection (x t (E k))⟫_ℂ) 0 0 := by
    have : (0 : ℂ) = ∑ _k : Fin (Module.finrank ℂ L), (0 : ℂ) := by simp
    rw [this]
    refine HasDerivAt.fun_sum fun k _ => ?_
    obtain ⟨w1, h1, z1⟩ := hd _ (hbL k)
    obtain ⟨w2, h2, z2⟩ := hd _ (hEL k)
    have := h1.inner ℂ h2
    rw [z1, z2, inner_zero_left, inner_zero_right, add_zero] at this
    exact this
  have := hsum.const_sub (∑ k, ⟪b k, E k⟫_ℂ)
  rwa [neg_zero] at this

end GlobalTheory.Pc3
end
end

