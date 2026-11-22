import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0004
import Development.EtaleCohomology.EtaleSheaves.Bundle0012
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.BothToSecondRelation
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0007
import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0012
import Development.AutomorphicArithmetic.CommutativeAlgebra.BconeDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0405

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.FiniteKernelPowClassesOfPrimitiveRoot
section
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private lemma mem_range_of_fixed {K K' : Type} [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K']
    (q : ℕ) (hq : (q : K) ≠ 0) (σ₀ : K' →ₐ[K] AlgebraicClosure K) (c : K') (d : K) (hd : d ≠ 0)
    (hc : c ^ q = algebraMap K K' d)
    (hfix : ∀ σ : K' →ₐ[K] AlgebraicClosure K, σ c = σ₀ c) : c ∈ (algebraMap K K').range := by
  have hsep : (minpoly K c).Separable := by
    refine (Polynomial.separable_X_pow_sub_C d hq hd).of_dvd (minpoly.dvd K c ?_)
    simp [hc]
  have hsplit : ((minpoly K c).map (algebraMap K (AlgebraicClosure K))).Splits := IsAlgClosed.splits _
  have hroot : (minpoly K c).rootSet (AlgebraicClosure K) = {σ₀ c} := by
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly]
    ext y
    constructor
    · rintro ⟨σ, rfl⟩
      exact hfix σ
    · rintro rfl
      exact ⟨σ₀, rfl⟩
  have hcard := Polynomial.card_rootSet_eq_natDegree hsep hsplit
  rw [← minpoly.natDegree_eq_one_iff, ← hcard, Fintype.card_eq_one_iff]
  refine ⟨⟨σ₀ c, by rw [hroot]; rfl⟩, fun y => Subtype.ext ?_⟩
  have hy : (y : AlgebraicClosure K) ∈ ({σ₀ c} : Set (AlgebraicClosure K)) := hroot ▸ y.2
  exact hy

theorem UpperTheory.finite_kernel_powClasses_of_primitive_root :
    ∀ (K K' : Type) [Field K] [Field K'] [Algebra K K'] [FiniteDimensional K K'] (q : ℕ) [NeZero q], (∃ ζ : K, IsPrimitiveRoot ζ q) → FinCls q {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q} := by
  intro K K' _ _ _ _ q _ ⟨ζ, hζ⟩
  classical
  haveI := hζ.neZero'
  have hq : ((q : ℕ) : K) ≠ 0 := NeZero.ne _
  have hq0 : q ≠ 0 := NeZero.ne q
  let σ₀ : K' →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let S : Set Kˣ := {a : Kˣ | ∃ b : K', algebraMap K K' (a : K) = b ^ q}
  let bb : Kˣ → K' := fun a => if h : ∃ b : K', algebraMap K K' (a : K) = b ^ q then h.choose else 1
  have hbb : ∀ a ∈ S, algebraMap K K' (a : K) = bb a ^ q := by
    intro a ha
    have ha' : ∃ b : K', algebraMap K K' (a : K) = b ^ q := ha
    simp only [bb, dif_pos ha']
    exact ha'.choose_spec
  have hbb0 : ∀ a ∈ S, bb a ≠ 0 := by
    intro a ha h0
    have h := hbb a ha
    rw [h0, zero_pow hq0] at h
    exact a.ne_zero ((algebraMap K K').injective (by rw [h, map_zero]))
  let sig : Kˣ → (K' →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K := fun a σ => σ (bb a) / σ₀ (bb a)
  have hsig : ∀ a ∈ S, ∀ σ, sig a σ ∈ Polynomial.nthRootsFinset q (1 : AlgebraicClosure K) := by
    intro a ha σ
    rw [Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hq0)]
    have h1 : σ (bb a) ^ q = σ₀ (bb a) ^ q := by
      rw [← map_pow, ← map_pow, ← hbb a ha, AlgHom.commutes, AlgHom.commutes]
    have h2 : σ₀ (bb a) ≠ 0 := (map_ne_zero σ₀).mpr (hbb0 a ha)
    simp only [sig, div_pow, h1, div_self (pow_ne_zero _ h2)]
  have hfin : (sig '' S).Finite := by
    refine (Set.Finite.pi (t := fun _ => (Polynomial.nthRootsFinset q (1 : AlgebraicClosure K) : Set _))
      (fun _ => Finset.finite_toSet _)).subset ?_
    rintro _ ⟨a, ha, rfl⟩
    exact Set.mem_univ_pi.mpr (fun σ => hsig a ha σ)
  let rep : ((K' →ₐ[K] AlgebraicClosure K) → AlgebraicClosure K) → Kˣ :=
    fun f => if h : ∃ a ∈ S, sig a = f then h.choose else 1
  refine ⟨hfin.toFinset.image rep, ?_⟩
  intro a ha
  have hex : ∃ a' ∈ S, sig a' = sig a := ⟨a, ha, rfl⟩
  have htS : rep (sig a) ∈ S ∧ sig (rep (sig a)) = sig a := by
    simp only [rep, dif_pos hex]
    exact hex.choose_spec
  refine ⟨rep (sig a), Finset.mem_image.mpr ⟨sig a, hfin.mem_toFinset.mpr ⟨a, ha, rfl⟩, rfl⟩, ?_⟩
  set t := rep (sig a) with ht
  have hat := hbb0 a ha
  have htt := hbb0 t htS.1
  let c : K' := bb a / bb t
  have hc : c ^ q = algebraMap K K' ((a : K) / (t : K)) := by
    rw [map_div₀, hbb a ha, hbb t htS.1, div_pow]
  have hd : (a : K) / (t : K) ≠ 0 := div_ne_zero a.ne_zero t.ne_zero
  have hfix : ∀ σ : K' →ₐ[K] AlgebraicClosure K, σ c = σ₀ c := by
    intro σ
    have e := congrFun htS.2 σ
    simp only [sig] at e
    have h1 : σ (bb t) ≠ 0 := (map_ne_zero σ).mpr htt
    have h2 : σ₀ (bb t) ≠ 0 := (map_ne_zero σ₀).mpr htt
    have h3 : σ₀ (bb a) ≠ 0 := (map_ne_zero σ₀).mpr hat
    simp only [c, map_div₀]
    rw [div_eq_div_iff h1 h2]
    rw [div_eq_div_iff h2 h3] at e
    linear_combination -e
  obtain ⟨e, he⟩ := mem_range_of_fixed q hq σ₀ c _ hd hc hfix
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [map_zero] at he
    exact div_ne_zero hat htt he.symm
  refine ⟨Units.mk0 e he0, ?_⟩
  ext
  apply (algebraMap K K').injective
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, he, hc, map_div₀]
  have : algebraMap K K' (t : K) ≠ 0 := (map_ne_zero _).mpr t.ne_zero
  field_simp
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.FinitePicTorsionOfFiniteKummerSelmer
section
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

private theorem finite_bad_places (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
    [Algebra.FiniteType k B] [IsFunctionField k (FractionRing B)] :
    {v : Place k (FractionRing B) | ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring}.Finite := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k B).FG)
  refine (Set.Finite.biUnion s.finite_toSet (fun g _ =>
    Place.finite_ord_ne_zero (k := k) (algebraMap B (FractionRing B) g))).subset ?_
  intro v hv
  by_contra hcon
  apply hv
  simp only [Set.mem_iUnion, not_exists] at hcon
  have hmem : ∀ g ∈ s, algebraMap B (FractionRing B) g ∈ v.ring := by
    intro g hg
    by_cases g0 : algebraMap B (FractionRing B) g = 0
    · rw [g0]; exact zero_mem _
    · have h0 : v.ord (algebraMap B (FractionRing B) g) = 0 := by
        by_contra hne
        exact hcon g hg hne
      exact (v.ord_nonneg_iff g0).1 h0.ge
  intro b
  have hb : b ∈ Algebra.adjoin k (s : Set B) := hs ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hmem x hx
  | algebraMap r =>
    rw [← IsScalarTower.algebraMap_apply k B (FractionRing B)]
    exact v.algebraMap_mem r
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

private theorem dvd_ord_of_mem_sel (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
    [IsFunctionField k (FractionRing B)] (q : ℕ) (v : Place k (FractionRing B))
    (hv : ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring) (f : (FractionRing B)ˣ)
    (hf : f ∈ LateralTheory.E.LeafPicCut.sel B q) : (q : ℤ) ∣ v.ord (f : FractionRing B) := by
  have hk : ∀ c : k, algebraMap k (FractionRing B) c ∈ (algebraMap B (FractionRing B)).range :=
    fun c => ⟨algebraMap k B c, (IsScalarTower.algebraMap_apply k B (FractionRing B) c).symm⟩
  obtain ⟨I, hI⟩ := hf
  have hvP := Place.ofHeightOneSpectrum_center B hk v hv
  have hval := Place.valuation_ofHeightOneSpectrum B hk (Place.center B v hv)
  rw [hvP] at hval
  have h1 := v.valuation_eq_exp_neg_ord f.ne_zero
  rw [hval, GlobalTheory.Idele.valuation_eq_exp_neg_count _ f.ne_zero, WithZero.exp_inj, neg_inj] at h1
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors B) (f : FractionRing B) =
      ((I : FractionalIdeal (nonZeroDivisors B) (FractionRing B))) ^ q := by
    have := congrArg (fun J : (FractionalIdeal (nonZeroDivisors B) (FractionRing B))ˣ =>
      (J : FractionalIdeal (nonZeroDivisors B) (FractionRing B))) hI
    simpa using this.symm
  rw [hspan, FractionalIdeal.count_pow] at h1
  exact ⟨_, h1.symm⟩

theorem UpperTheory.finite_pic_torsion_of_finite_kummerSelmer :
    LateralTheory.E.LeafPicCut.LeafSelPic → ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] [IsFunctionField k (FractionRing B)] (q : ℕ) [NeZero q], FinCls q (SelAll k (FractionRing B) q) → Finite {c : CommRing.Pic B // c ^ q = 1} := by
  intro hS k B _ _ _ _ _ _ q _ hT
  have hfin : Finite (LateralTheory.E.LeafPicCut.selQ B q) := by
    have : Finite {v : Place k (FractionRing B) |
        ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} := (finite_bad_places k B).to_subtype
    let φ : LateralTheory.E.LeafPicCut.sel B q →
        ({v : Place k (FractionRing B) | ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} → ZMod q) :=
      fun f v => ((v.1.ord ((f.1 : (FractionRing B)ˣ) : FractionRing B) : ℤ) : ZMod q)
    let r := Function.invFun φ
    have hall : ∀ f : LateralTheory.E.LeafPicCut.sel B q,
        (f.1 / (r (φ f)).1 : (FractionRing B)ˣ) ∈ SelAll k (FractionRing B) q := by
      intro f v
      have hdiv : v.ord (((f.1 / (r (φ f)).1 : (FractionRing B)ˣ)) : FractionRing B) =
          v.ord (f.1 : FractionRing B) - v.ord ((r (φ f)).1 : FractionRing B) := by
        rw [Units.val_div_eq_div_val, v.ord_div f.1.ne_zero (r (φ f)).1.ne_zero]
      rw [hdiv]
      by_cases hv : ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring
      · exact dvd_sub (dvd_ord_of_mem_sel k B q v hv _ f.2) (dvd_ord_of_mem_sel k B q v hv _ (r (φ f)).2)
      · have h := congrFun (Function.invFun_eq (f := φ) ⟨f, rfl⟩) ⟨v, hv⟩
        exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
    obtain ⟨T, hT⟩ := hT
    choose t ht u hu using fun f => hT _ (hall f)
    refine Finite.of_injective (β := ({v : Place k (FractionRing B) |
        ¬ ∀ b : B, algebraMap B (FractionRing B) b ∈ v.ring} → ZMod q) × T)
      (fun x => (φ x.out, ⟨t x.out, ht x.out⟩)) ?_
    intro x y hxy
    have h1 : φ x.out = φ y.out := congrArg Prod.fst hxy
    have h2 : t x.out = t y.out := congrArg (fun p => (p.2 : T).1) hxy
    have hx := hu x.out
    have hy := hu y.out
    rw [div_eq_iff_eq_mul'] at hx hy
    rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' y, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨(u x.out)⁻¹ * u y.out, ?_⟩
    simp only [powMonoidHom_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hx, hy, h1, h2, mul_pow, inv_pow]
    group
  have key : Finite {c : ClassGroup B // c ^ q = 1} := hS B q hfin
  exact Finite.of_equiv _ (@Equiv.subtypeEquiv _ _ (fun c : ClassGroup B => c ^ q = 1) (fun c : CommRing.Pic B => c ^ q = 1)
    (ClassGroup.equivPic B).toEquiv (fun c => by
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_pow, MulEquiv.map_eq_one_iff]))
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.InclusionConnectedTwist
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut UpperTheory.Aff

noncomputable section

namespace UpperTheory.SimplicialRelationHom

variable (D : Type) [CommRing D]

private def Rg : RF where
  obj A _ := D →+* A
  map f x := f.comp x
  map_id _ := rfl
  map_comp _ _ _ := rfl
  rel x y := x = y
  map_rel _ _ _ h := by rw [h]

private def forget (N : ℕ) : (Vec D N).Hom (Rg D) where
  app _ _ x := x.1.1
  nat _ _ := rfl

private theorem forget_rel (N : ℕ) : (forget D N).Rel := fun h => h.1

variable {D}

private theorem rel_iff {N : ℕ} {A : Type} [CommRing A] {x y : (Vec D N).obj A} :
    (Vec D N).rel x y ↔ x.1.1 = y.1.1 ∧ ∃ u : Aˣ, x.1.2 = fun j => (u : A) * y.1.2 j := Iff.rfl

private theorem unit_unique {A : Type} [CommRing A] {N : ℕ} {w : Fin N → A} (hw : Ideal.span (Set.range w) = ⊤)
    {u u' : A} (h : ∀ j, u * w j = u' * w j) : u = u' := by
  have key : ∀ a ∈ Ideal.span (Set.range w), u * a = u' * a := by
    intro a ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨j, rfl⟩
      exact h j
    · simp
    · intro a b _ _ h1 h2
      rw [mul_add, mul_add, h1, h2]
    · intro c a _ h1
      simp only [smul_eq_mul]
      rw [mul_left_comm, h1, mul_left_comm]
  simpa using key 1 (by rw [hw]; trivial)

private theorem um_hom_ext {A : Type} [CommRing A] {N : ℕ} {v w : Um N A} (p q : v ⟶ w) (h : p.1.1 = q.1.1) : p = q := by
  refine Subtype.ext (Prod.ext h (Units.ext ?_))
  refine unit_unique w.2 fun j => ?_
  have h1 := congrFun p.2 j
  have h2 := congrFun q.2 j
  rw [h] at h1
  simpa using h1.symm.trans h2

private def toUm {N : ℕ} {A : Type} [CommRing A] (x : (Vec D N).obj A) : Um N A := ⟨x.1.2, x.2⟩

private def relHom {N : ℕ} {A : Type} [CommRing A] {x y : (Vec D N).obj A} (h : (Vec D N).rel x y) :
    toUm x ⟶ toUm y :=
  ⟨(1, (rel_iff.1 h).2.choose), by
    have := (rel_iff.1 h).2.choose_spec
    funext j
    simpa [toUm] using congrFun this j⟩

private def tFun {n N : ℕ} {A : Type} [CommRing A] (x : Fin (n + 1) → (Vec D N).obj A)
    (hx : ∀ i j, (Vec D N).rel (x i) (x j)) : Fin (n + 1) ⥤ Um N A where
  obj i := toUm (x i)
  map {i j} _ := relHom (hx i j)
  map_id i := um_hom_ext _ _ rfl
  map_comp _ _ := um_hom_ext _ _ (mul_one _).symm

private theorem tFun_base {n N : ℕ} {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (x : Fin (n + 1) → (Vec D N).obj A) (hx : ∀ i j, (Vec D N).rel (x i) (x j)) :
    tFun (fun i => (Vec D N).map f (x i)) (fun i j => (Vec D N).map_rel f (hx i j)) = tFun x hx ⋙ Um.map N f :=
  CategoryTheory.Functor.hext (fun _ => rfl) fun i j p => heq_of_eq (um_hom_ext _ _ (map_one (Matrix.GeneralLinearGroup.map f)).symm)

private theorem tFun_pre {m n N : ℕ} {A : Type} [CommRing A] (g : Fin (m + 1) →o Fin (n + 1))
    (x : Fin (n + 1) → (Vec D N).obj A) (hx : ∀ i j, (Vec D N).rel (x i) (x j)) :
    tFun (fun i => x (g i)) (fun i j => hx _ _) = g.monotone.functor ⋙ tFun x hx :=
  CategoryTheory.Functor.hext (fun _ => rfl) fun i j p => heq_of_eq (um_hom_ext _ _ rfl)

private def tMap (D : Type) [CommRing D] (N : ℕ) : CN (Vec D N) ⟶ PGL N where
  app n :=
    { app := fun U => TypeCat.ofHom fun x =>
        (show Fin (n.unop.len + 1) ⥤ Um N Γ(U.unop, ⊤) from tFun x.1 x.2)
      naturality := fun U V f => by
        ext x
        exact tFun_base f.unop.appTop.hom x.1 x.2 }
  naturality n m θ := by
    ext U x
    exact tFun_pre θ.unop.toOrderHom x.1 x.2

private def trivF (n N : ℕ) (A : Type) [CommRing A] : Fin (n + 1) ⥤ SingleObj (GL (Fin N) A) :=
  (Functor.const _).obj (SingleObj.star _)

private def triv (E : Spc) (N : ℕ) : E ⟶ ofCat (glCat N) where
  app n :=
    { app := fun U => TypeCat.ofHom fun _ =>
        (show Fin (n.unop.len + 1) ⥤ SingleObj (GL (Fin N) Γ(U.unop, ⊤)) from trivF _ N _)
      naturality := fun U V f => by
        ext x
        refine CategoryTheory.Functor.hext (fun _ => rfl) fun i j p => heq_of_eq ?_
        exact (map_one (Matrix.GeneralLinearGroup.map f.unop.appTop.hom)).symm }
  naturality n m θ := by
    ext U x
    rfl

private theorem singleObj_map_eq {C : Type} [Category C] {M : Type} [Monoid M] {F G : C ⥤ SingleObj M} (h : F = G)
    {i j : C} (p : i ⟶ j) : (show M from F.map p) = (show M from G.map p) := by
  subst h
  rfl

variable (D) in

private theorem sq (N : ℕ) :
    IsPullback (CN.map (forget D N) (forget_rel D N)) (tMap D N) (triv (CN (Rg D)) N) (PGL.pr N) := by
  refine IsPullback.of_forall_isPullback_app fun n => IsPullback.of_forall_isPullback_app fun U =>
    (Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩
  · ext x
    refine (CategoryTheory.Functor.hext (fun _ => rfl) fun i j p => heq_of_eq rfl :
      (trivF _ N _ : Fin (n.unop.len + 1) ⥤ SingleObj (GL (Fin N) Γ(U.unop, ⊤))) = tFun x.1 x.2 ⋙ Um.toGL N _)
  · rintro x y ⟨h1, h2⟩
    refine Subtype.ext (funext fun i => Subtype.ext (Prod.ext ?_ ?_))
    · exact congrFun (congrArg Subtype.val h1) i
    · have h3 : tFun x.1 x.2 = tFun y.1 y.2 := h2
      exact congrArg Subtype.val (congrArg (fun F => F.obj i) h3)
  · intro r F h
    have h' : (trivF _ N _ : Fin (n.unop.len + 1) ⥤ SingleObj (GL (Fin N) Γ(U.unop, ⊤))) =
      (show Fin (n.unop.len + 1) ⥤ Um N Γ(U.unop, ⊤) from F) ⋙ Um.toGL N _ := h
    obtain ⟨F', rfl⟩ : ∃ F' : Fin (n.unop.len + 1) ⥤ Um N Γ(U.unop, ⊤), F' = F := ⟨F, rfl⟩
    have ha : ∀ {i j : Fin (n.unop.len + 1)} (p : i ⟶ j), (F'.map p).1.1 = 1 := fun p =>
      (singleObj_map_eq h' p).symm
    have hle : ∀ {i j : Fin (n.unop.len + 1)}, i ≤ j → ∃ u : Γ(U.unop, ⊤)ˣ, (F'.obj i).1 = fun k => (u : Γ(U.unop, ⊤)) * (F'.obj j).1 k := by
      intro i j hij
      refine ⟨(F'.map (homOfLE hij)).1.2, funext fun k => ?_⟩
      have h2 := congrFun (F'.map (homOfLE hij)).2 k
      rw [ha] at h2
      simpa using h2
    let x : Fin (n.unop.len + 1) → (Vec D N).obj Γ(U.unop, ⊤) := fun i => ⟨((r.1 i : D →+* Γ(U.unop, ⊤)), (F'.obj i).1), (F'.obj i).2⟩
    have hx : ∀ i j, (Vec D N).rel (x i) (x j) := by
      intro i j
      refine rel_iff.2 ⟨r.2 i j, ?_⟩
      rcases le_total i j with hij | hij
      · exact hle hij
      · obtain ⟨u, hu⟩ := hle hij
        refine ⟨u⁻¹, funext fun k => ?_⟩
        change (F'.obj i).1 k = ((u⁻¹ : Γ(U.unop, ⊤)ˣ) : Γ(U.unop, ⊤)) * (F'.obj j).1 k
        rw [hu]
        simp
    refine ⟨⟨x, hx⟩, rfl, ?_⟩
    exact CategoryTheory.Functor.hext (fun _ => rfl) fun i j p => heq_of_eq (um_hom_ext _ _ (ha p).symm)

private theorem pr_incl (d : ℕ) : CN.map (incl D d) (incl_rel D d) ≫ CN.map (forget D (d + 1)) (forget_rel D (d + 1)) =
    CN.map (forget D d) (forget_rel D d) := rfl

private theorem eqv_iso {R : Type} [CommRing R] (F : Shv R) {E E' : Spc} (e : E ≅ E') : Eqv R e.hom F :=
  eqv_section F e.hom e.inv e.hom_inv_id fun n => by
    refine (Function.bijective_iff_has_inverse).2 ⟨pull R e.hom F n, fun x => ?_, fun x => ?_⟩
    · rw [← pull_comp, e.hom_inv_id, pull_id]
    · rw [← pull_comp, e.inv_hom_id, pull_id]

private theorem invertible_nerve (q : ℕ) (hq : IsUnit (q : D)) : Inv q (CN (Rg D)) := by
  rintro U ⟨x⟩
  have h1 := hq.map (show D →+* Γ(U, ⊤) from x.1 0)
  rwa [map_natCast] at h1

private theorem line_incl (d : ℕ) : CN.map (incl D d) (incl_rel D d) ≫ tMap D (d + 1) ≫ PGL.line (d + 1) =
    tMap D d ≫ PGL.line d := by
  ext n U x
  refine (CategoryTheory.Functor.hext (fun _ => rfl) fun i j p => heq_of_eq ?_ :
    (tFun (fun i => (incl D d).app _ (x.1 i)) (fun i j => incl_rel D d (x.2 i j)) ⋙ Um.toLine (d + 1) _ :
      Fin (n.unop.len + 1) ⥤ SingleObj (GL (Fin 1) Γ(U.unop, ⊤))) = tFun x.1 x.2 ⋙ Um.toLine d _)
  refine congrArg (Matrix.GeneralLinearGroup.scalar (Fin 1)) (Units.ext (unit_unique (x.1 j).2 fun k => ?_))
  have h1 := congrFun (rel_iff.1 (incl_rel D d (x.2 i j))).2.choose_spec k.castSucc
  have h2 := congrFun (rel_iff.1 (x.2 i j)).2.choose_spec k
  have e : ∀ y : (Vec D d).obj Γ(U.unop, ⊤), ((incl D d).app _ y).1.2 k.castSucc = y.1.2 k := fun y => by
    change Fin.snoc (α := fun _ => Γ(U.unop, ⊤)) y.1.2 0 k.castSucc = _
    simp
  simp only [e] at h1
  exact h1.symm.trans h2

end UpperTheory.SimplicialRelationHom

open UpperTheory.SimplicialRelationHom in
theorem UpperTheory.inclusion_connected_twist :
    LeafProj → A1 → A5 → A7 → A9 → A10 → D1 → ∀ (q : ℕ) [NeZero q] (i : ℤ) (d : ℕ) (D : Type) [CommRing D], IsUnit (q : D) → Conn _ (tw q i) (2 * d) (CN.map (incl D d) (incl_rel D d)) := by
  intro hP a1 a5 a7 a9 a10 d1 q _ i d D _ hq
  let e0 := (sq D d).isoPullback
  let e1 := (sq D (d + 1)).isoPullback
  have hs := hP a1 a5 a7 a9 a10 d1 q i (E := CN (Rg D)) (N := d) (triv _ d) (triv _ (d + 1)) (invertible_nerve q hq)
    (e0.inv ≫ CN.map (incl D d) (incl_rel D d) ≫ e1.hom) ?_ ?_
  · refine (conn_sq _ _ _ _ e0.hom e1.hom ?_ (eqv_iso _ e0) (eqv_iso _ e1)).2 hs
    simp
  · simp only [Category.assoc]
    rw [(sq D (d + 1)).isoPullback_hom_fst, pr_incl]
    exact (sq D d).isoPullback_inv_fst
  · simp only [Category.assoc]
    rw [IsPullback.isoPullback_hom_snd_assoc, line_incl]
    rw [← Category.assoc, (sq D d).isoPullback_inv_snd]

end
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldFractionRingOfDedekindFiniteType
section
open GroundTheory.FunctionField UpperTheory.Et.Sel
open scoped TensorProduct

theorem UpperTheory.isFunctionField_fractionRing_of_dedekind_finiteType :
    ∀ (k B : Type) [Field k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B → IsFunctionField k (FractionRing B) := by
  intro k B _ _ _ _ _ hB
  have hdim : ringKrullDim B = 1 := by
    apply eq_of_le_of_not_lt ?_ fun h' ↦ hB ?_
    · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
      infer_instance
    · have h'' : ringKrullDim B ≤ 0 := Order.le_of_lt_succ h'
      rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
      exact Ring.KrullDimLE.isField_of_isDomain
  exact GroundTheory.Arith.SchemeCoh.isFunctionField_of_ringKrullDim_eq_one k B (FractionRing B) hdim
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductMapOfBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

private noncomputable def invFn {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) : Ob b A ⥤ Ob a A where
  obj y := ⟨(Equiv.ofBijective _ h1).symm y.pt⟩
  map {x y} f := ⟨(Equiv.ofBijective _ h2).symm f.1, h1.1 (by
    have e1 : φ.d.app A ((Equiv.ofBijective _ h1).symm x.pt) = x.pt := (Equiv.ofBijective _ h1).apply_symm_apply _
    have e2 : φ.d.app A ((Equiv.ofBijective _ h1).symm y.pt) = y.pt := (Equiv.ofBijective _ h1).apply_symm_apply _
    have e3 : φ.g.app A ((Equiv.ofBijective _ h2).symm f.1) = f.1 := (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.d.app A _ = φ.d.app A _
    rw [φ.eq, e1, e2, e3]
    exact f.2)⟩
  map_id x := Subtype.ext (h2.1 (by
    have e3 : φ.g.app A ((Equiv.ofBijective _ h2).symm 1) = 1 := (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.g.app A _ = φ.g.app A 1
    rw [map_one (φ.g.app A).hom]
    exact e3))
  map_comp {x y z} f g := Subtype.ext (h2.1 (by
    have e : ∀ u : b.G.obj A, φ.g.app A ((Equiv.ofBijective _ h2).symm u) = u := fun u =>
      (Equiv.ofBijective _ h2).apply_symm_apply _
    show φ.g.app A _ = φ.g.app A (_ * _)
    rw [map_mul (φ.g.app A).hom, e, e, e]
    rfl))

private theorem fn_inv {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) :
    φ.fn A ⋙ invFn φ A h1 h2 = 𝟭 _ := by
  have ho : ∀ x : Ob a A, (φ.fn A ⋙ invFn φ A h1 h2).obj x = (𝟭 _ : Ob a A ⥤ Ob a A).obj x := fun x =>
    congrArg Ob.mk ((Equiv.ofBijective _ h1).symm_apply_apply x.pt)
  refine CategoryTheory.Functor.hext ho (fun x y f => Ob.hom_heq (ho x) (ho y) _ _ ?_)
  exact (Equiv.ofBijective _ h2).symm_apply_apply f.1

private theorem inv_fn {a b : Act} (φ : Act.Hom a b) (A : CommRingCat.{0})
    (h1 : Function.Bijective (fun x : a.D.obj A => φ.d.app A x))
    (h2 : Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) :
    invFn φ A h1 h2 ⋙ φ.fn A = 𝟭 _ := by
  have ho : ∀ x : Ob b A, (invFn φ A h1 h2 ⋙ φ.fn A).obj x = (𝟭 _ : Ob b A ⥤ Ob b A).obj x := fun x =>
    congrArg Ob.mk ((Equiv.ofBijective _ h1).apply_symm_apply x.pt)
  refine CategoryTheory.Functor.hext ho (fun x y f => Ob.hom_heq (ho x) (ho y) _ _ ?_)
  exact (Equiv.ofBijective _ h2).apply_symm_apply f.1

private theorem comp_bij {C D : Type} [SmallCategory C] [SmallCategory D] (F : C ⥤ D) (G : D ⥤ C)
    (h : F ⋙ G = 𝟭 _) (h' : G ⋙ F = 𝟭 _) (k : ℕ) :
    Function.Bijective (fun s : ComposableArrows C k => s ⋙ F) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun t => t ⋙ G, fun s => ?_, fun t => ?_⟩
  · show (s ⋙ F) ⋙ G = s
    rw [Functor.assoc, h, Functor.comp_id]
  · show (t ⋙ G) ⋙ F = t
    rw [Functor.assoc, h', Functor.comp_id]

theorem UpperTheory.isIso_stackProductMap_of_bijective :
    ∀ (E : Spc) {a b : Act} (φ : Act.Hom a b), (∀ A, Function.Bijective (fun x : a.D.obj A => φ.d.app A x)) →
        (∀ A, Function.Bijective (fun g : a.G.obj A => φ.g.app A g)) → IsIso (Sp.map E φ) := by
  intro E a b φ h1 h2
  apply isIso_of_bijective_on_simplices
  intro k T
  have hb := (Function.bijective_id (α := Sx E k T)).prodMap
    (comp_bij (C := Ob a (Scheme.Γ.obj (op T))) (D := Ob b (Scheme.Γ.obj (op T)))
      (φ.fn _) (invFn φ _ (h1 _) (h2 _)) (fn_inv φ _ (h1 _) (h2 _)) (inv_fn φ _ (h1 _) (h2 _)) k)
  exact hb
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.SubsingletonHypercohomologyFreeOfSubsingletonCoh
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Bc

theorem UpperTheory.subsingleton_hypercohomology_free_of_subsingleton_cohomology :
    ∀ (F : Shv ℤ) (P : PSh) (n : ℤ), Subsingleton (H ℤ (disc.obj P) F n) → Subsingleton (HK ℤ (sgl ((free ℤ).obj P)) F n) := by
  intro F P n hs
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf ℤ
  haveI : (res ℤ F).IsKInjective := (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties ℤ F).1
  haveI : QuasiIso (e P).hom := (e P).quasiIso_hom
  have hb := GlobalTheory.T.hypercohomologyPullback_bijective_of_quasiIso ℤ (e P).hom (res ℤ F) n
  exact hb.2.subsingleton
end

