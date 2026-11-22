import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0491
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0502
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0703
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormPrimNeZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.Diag MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DeRham.MultGrp

section Log

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {s : X ⟶ Sp R}

theorem exp_add (T : Thick κ s) {a b : T.B} (ha : a ∈ T.J) (hb : b ∈ T.J) :
    dpExp T.δ (a + b) = dpExp T.δ a * dpExp T.δ b :=
  (GlobalTheory.Cris.dpExp_add_and_natural T.B T.B T.J T.J T.δ T.δ T.nil).1 a ha b hb

theorem map_exp {T T' : Thick κ s} (φ : T ⟶ T') {a : T.B} (ha : a ∈ T.J) :
    φ.φ (dpExp T.δ a) = dpExp T'.δ (φ.φ a) :=
  (GlobalTheory.Cris.dpExp_add_and_natural T.B T'.B T.J T'.J T.δ T'.δ T.nil).2 _ φ.dp a ha

theorem exists_exp (T : Thick κ s) {u : T.B} (hu : T.π u = 1) : ∃ a ∈ T.J, dpExp T.δ a = u :=
  (GlobalTheory.Cris.ExpBij.dpExp_bijOn T.B T.J T.δ T.nil).surjOn ((T.ker _).1 (by rw [map_sub, hu, map_one, sub_self]))

theorem isUnit_of_π (T : Thick κ s) {u : T.B} (hu : IsUnit (T.π u)) : IsUnit u := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨v, rfl⟩ := T.surj v
  obtain ⟨a, ha, e⟩ := exists_exp T ((map_mul _ _ _).trans hv)
  refine IsUnit.of_mul_eq_one (v * dpExp T.δ (-a)) ?_
  rw [← _root_.mul_assoc, ← e, ← exp_add T ha (neg_mem ha), add_neg_cancel, dpExp_zero]

theorem exists_log (T : Thick κ s) {u v : T.B} (hu : IsUnit (T.π u)) (h : T.π u = T.π v) :
    ∃ a, a ∈ T.J ∧ dpExp T.δ a * u = v := by
  obtain ⟨w, hw⟩ := (isUnit_of_π T hu).exists_right_inv
  obtain ⟨a, ha, e⟩ := exists_exp T (u := v * w) (by rw [map_mul, ← h, ← map_mul, hw, map_one])
  exact ⟨a, ha, by rw [e]; linear_combination v * hw⟩

theorem log_unique (T : Thick κ s) {u a b : T.B} (hu : IsUnit (T.π u)) (ha : a ∈ T.J) (hb : b ∈ T.J)
    (h : dpExp T.δ a * u = dpExp T.δ b * u) : a = b :=
  (GlobalTheory.Cris.ExpBij.dpExp_bijOn T.B T.J T.δ T.nil).injOn ha hb ((isUnit_of_π T hu).mul_right_cancel h)

end Log

section Coord

variable {S : Scheme.{0}} {A A' : Type} [CommRing A] [CommRing A']

def coordVal (x : Sp A ⟶ (Gm S).left) : A :=
  charVal (Over.homMk x rfl : Over.mk (x ≫ (Gm S).hom) ⟶ Gm S) (ULift.up 1)

theorem coordVal_left {g : Sp A ⟶ S} (w : Over.mk g ⟶ Gm S) :
    coordVal w.left = charVal w (ULift.up 1) := rfl

theorem isUnit_coordVal (x : Sp A ⟶ (Gm S).left) : IsUnit (coordVal x) :=
  IsUnit.of_mul_eq_one _ (by
    rw [coordVal, ← charVal_add, add_neg_cancel, charVal_zero])

theorem coordVal_map (φ : A →+* A') (x : Sp A ⟶ (Gm S).left) :
    coordVal (spMap φ ≫ x) = φ (coordVal x) :=
  (left_eq_iff φ (Category.assoc _ _ _) _ _).1 rfl _

theorem coordVal_mul {Y : Over S} (t : Sp A ⟶ Y.left) (f g : Y ⟶ Gm S) :
    coordVal (t ≫ (f * g).left) = coordVal (t ≫ f.left) * coordVal (t ≫ g.left) := by
  let j : Over.mk (t ≫ Y.hom) ⟶ Y := Over.homMk t rfl
  have := charVal_mul (j ≫ f) (j ≫ g) (ULift.up 1)
  rw [← MonObj.comp_mul] at this
  exact this

end Coord

variable {R : Type} [CommRing R]

abbrev gmStr (R : Type) [CommRing R] : (Gm (Sp R)).left ⟶ Sp R := (Gm (Sp R)).hom ≫ 𝟙 _

def unitLift (T : Thick (dp0 R) (gmStr R)) : T.B := (T.surj (coordVal T.x)).choose

theorem π_unitLift (T : Thick (dp0 R) (gmStr R)) : T.π (unitLift T) = coordVal T.x :=
  (T.surj _).choose_spec

theorem π_map_unitLift {T T' : Thick (dp0 R) (gmStr R)} (φ : T ⟶ T') :
    T'.π (φ.φ (unitLift T)) = coordVal T'.x := by
  rw [← φ.comm, π_unitLift, ← φ.pt, coordVal_map]

theorem exists_dlog {T T' : Thick (dp0 R) (gmStr R)} (φ : T ⟶ T') :
    ∃ a, a ∈ T'.J ∧ dpExp T'.δ a * φ.φ (unitLift T) = unitLift T' :=
  exists_log T' (π_map_unitLift φ ▸ isUnit_coordVal _) ((π_map_unitLift φ).trans (π_unitLift T').symm)

def dlogVal {T T' : Thick (dp0 R) (gmStr R)} (φ : T ⟶ T') : T'.B := (exists_dlog φ).choose

theorem dlogVal_mem {T T' : Thick (dp0 R) (gmStr R)} (φ : T ⟶ T') : dlogVal φ ∈ T'.J :=
  (exists_dlog φ).choose_spec.1

theorem exp_dlogVal {T T' : Thick (dp0 R) (gmStr R)} (φ : T ⟶ T') :
    dpExp T'.δ (dlogVal φ) * φ.φ (unitLift T) = unitLift T' :=
  (exists_dlog φ).choose_spec.2

def dlog (R : Type) [CommRing R] : Form (gmStr R) :=
  ⟨⟨fun _ _ φ ↦ dlogVal φ, fun T T' T'' φ ψ ↦ by
    change (dlogVal (φ ≫ ψ) : T''.B) = ψ.φ (dlogVal φ) + dlogVal ψ
    have h1 := ψ.mem (dlogVal_mem φ)
    refine log_unique T'' (π_map_unitLift (φ ≫ ψ) ▸ isUnit_coordVal _) (dlogVal_mem _)
      (add_mem h1 (dlogVal_mem ψ)) ?_
    rw [exp_dlogVal, exp_add _ h1 (dlogVal_mem ψ), ← map_exp ψ (dlogVal_mem φ), ← exp_dlogVal ψ,
      ← exp_dlogVal φ, map_mul, Thick.comp_φ]
    ring⟩, fun T T' φ _ h ↦ by
    have := dlogVal_mem φ
    rwa [h, Ideal.mem_bot] at this⟩

theorem cl_dlog_mem : Form.cl _ (dlog R) ∈ primDR (Gm (Sp R)) := by
  intro Y f g
  have m : ∀ f : Y ⟶ Gm (Sp R), IsMor (dp0 R) (gmStr R) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) f.left :=
    fun f ↦ IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  let u : (Y ⟶ Gm (Sp R)) → ∀ T : Thick (dp0 R) (Y.hom ≫ 𝟙 _), T.B := fun f T ↦ unitLift ((m f).obj T)
  let a : (Y ⟶ Gm (Sp R)) → ∀ {T T' : Thick (dp0 R) (Y.hom ≫ 𝟙 _)}, (T ⟶ T') → T'.B :=
    fun f _ _ φ ↦ dlogVal ((m f).functor.map φ)
  have hu : ∀ (f : Y ⟶ Gm (Sp R)) (T : Thick (dp0 R) (Y.hom ≫ 𝟙 _)), T.π (u f T) = coordVal (T.x ≫ f.left) := fun f T ↦ π_unitLift ((m f).obj T)
  have ha : ∀ (f : Y ⟶ Gm (Sp R)) {T T' : Thick (dp0 R) (Y.hom ≫ 𝟙 _)} (φ : T ⟶ T'), a f φ ∈ T'.J :=
    fun f _ _ φ ↦ dlogVal_mem ((m f).functor.map φ)
  have hb : ∀ (f : Y ⟶ Gm (Sp R)) {T T' : Thick (dp0 R) (Y.hom ≫ 𝟙 _)} (φ : T ⟶ T'),
      dpExp T'.δ (a f φ) * φ.φ (u f T) = u f T' :=
    fun f _ _ φ ↦ exp_dlogVal ((m f).functor.map φ)
  have hun : ∀ T : Thick (dp0 R) (Y.hom ≫ 𝟙 _), IsUnit (T.π (u f T * u g T)) := fun T ↦ by
    rw [map_mul, hu, hu]; exact (isUnit_coordVal _).mul (isUnit_coordVal _)
  choose c hc hc' using fun T ↦ exists_log T (hun T) (v := u (f * g) T)
    (by rw [map_mul, hu, hu, hu, coordVal_mul])
  have key : H1.mk _ ((m (f * g)).coef.pullbackOneCocycle (dlog R).1) =
      H1.mk _ ((m f).coef.pullbackOneCocycle (dlog R).1 + (m g).coef.pullbackOneCocycle (dlog R).1) := by
    refine H1.mk_eq_mk.2 ⟨c, ?_⟩
    funext T T' φ
    change (c T' - φ.φ (c T) : T'.B) = a (f * g) φ - (a f φ + a g φ)
    have h1 := φ.mem (hc T)
    have := log_unique T' (u := φ.φ (u f T * u g T)) (by rw [← φ.comm]; exact (hun T).map _)
      (add_mem (hc T') (add_mem (ha f φ) (ha g φ))) (add_mem (ha (f * g) φ) h1) (by
        rw [exp_add _ (hc T') (add_mem (ha f φ) (ha g φ)), exp_add _ (ha f φ) (ha g φ),
          exp_add _ (ha (f * g) φ) h1, ← map_exp φ (hc T), _root_.mul_assoc (dpExp _ (a (f * g) φ)),
          ← map_mul, hc', hb, ← hc', ← hb f φ, ← hb g φ, map_mul]
        ring)
    linear_combination this
  rw [map_add] at key
  exact key

open AddMonoidAlgebra TrivSqZeroExt in

def eulerSec (R : Type) [CommRing R] : AddMonoidAlgebra R (ULift.{0} ℤ) →ₐ[R]
    TrivSqZeroExt (AddMonoidAlgebra R (ULift.{0} ℤ)) (AddMonoidAlgebra R (ULift.{0} ℤ)) :=
  AddMonoidAlgebra.lift R _ _
    { toFun := fun x ↦ inl (single x.toAdd 1) + inr (single x.toAdd (x.toAdd.down : R))
      map_one' := by ext1 <;> simp [AddMonoidAlgebra.one_def]
      map_mul' := fun x y ↦ by
        ext1 <;> simp [single_mul_single, add_comm, single_add] }

theorem eulerSec_single (x : ULift.{0} ℤ) (r : R) :
    (eulerSec R (AddMonoidAlgebra.single x r)).fst = AddMonoidAlgebra.single x r ∧
      (eulerSec R (AddMonoidAlgebra.single x r)).snd = AddMonoidAlgebra.single x (r * x.down) := by
  simp [eulerSec]

theorem eulerSec_spec (b : AddMonoidAlgebra R (ULift.{0} ℤ)) :
    (eulerSec R b).fst = b ∧ (eulerSec R b).snd.coeff 0 = 0 := by
  induction b using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single x r =>
    rw [(eulerSec_single x r).1, (eulerSec_single x r).2]
    refine ⟨rfl, ?_⟩
    by_cases h : x = 0
    · subst h; simp
    · simp [h]

theorem cl_dlog_ne_zero [Nontrivial R] : Form.cl _ (dlog R) ≠ 0 := by
  intro h
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 h
  let B := AddMonoidAlgebra R (ULift.{0} ℤ)
  let w : Over.mk (spMap (algebraMap R B)) ⟶ Gm (Sp R) := ofVal _ (AddMonoidAlgebra.of R _)
  have hx : w.left ≫ gmStr R = spMap (algebraMap R B) := pt_w w
  let t : B := AddMonoidAlgebra.single (ULift.up 1) 1
  have ht : coordVal w.left = t := charVal_ofVal _ _
  let E := SqExt.ofModule R B B
  have hπ : ∀ b, E.π (eulerSec R b) = b := fun b ↦ (eulerSec_spec b).1
  have c0 : unitLift (Thick.triv B _ hx) = t := (π_unitLift (Thick.triv B _ hx)).trans ht
  have e1 := congrFun (congrFun (congrFun hg _) _) (E.secHom hx E.i E.π_i)
  have e2 := congrFun (congrFun (congrFun hg _) _) (E.secHom hx (eulerSec R) hπ)
  have m1 := dlogVal_mem (E.secHom hx E.i E.π_i)
  have m2 := dlogVal_mem (E.secHom hx (eulerSec R) hπ)
  have k1 := exp_dlogVal (E.secHom hx E.i E.π_i)
  have k2 := exp_dlogVal (E.secHom hx (eulerSec R) hπ)
  rw [c0] at k1 k2
  have key : ∀ (G a₁ a₂ v : TrivSqZeroExt B B) (p : B), a₁.fst = 0 → a₂.fst = 0 →
      G - TrivSqZeroExt.inl p = a₁ → G - eulerSec R p = a₂ → (1 + a₁) * TrivSqZeroExt.inl t = v →
      (1 + a₂) * eulerSec R t = v → (eulerSec R p).snd = 1 := by
    intro G a₁ a₂ v p m1 m2 e1 e2 k1 k2
    have f1 := congrArg TrivSqZeroExt.snd e1
    have f2 := congrArg TrivSqZeroExt.snd e2
    have f3 := congrArg TrivSqZeroExt.snd (k1.trans k2.symm)
    have s1 : (eulerSec R t).fst = t := (eulerSec_spec t).1
    have s2 : (eulerSec R t).snd = t := by simpa using (eulerSec_single (ULift.up 1) (1 : R)).2
    simp [m1, m2, s1, s2] at f1 f2 f3
    refine (ht ▸ isUnit_coordVal w.left).mul_right_cancel ?_
    linear_combination t * f1 - t * f2 + f3
  have f3 := key _ _ _ _ _ m1 m2 e1 e2 ((dpExp_sqDP E.sq m1).symm ▸ k1) ((dpExp_sqDP E.sq m2).symm ▸ k2)
  have := (eulerSec_spec (g (Thick.triv B _ hx))).2
  rw [f3] at this
  simp [AddMonoidAlgebra.one_def] at this

end GlobalTheory.DeRham.MultGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSet
section
noncomputable section

namespace GlobalTheory.GoodSetOfChars

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem eS_eq_chiIdem {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G) (s : T.S) :
    Formalism.MainNotions.PrimeDegreeVariant.eS T s = chiIdem fun g => LinearMap.trace K (T.W s) (T.tau s g) := by
  unfold Formalism.MainNotions.PrimeDegreeVariant.eS chiIdem
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [LinearMap.trace_one]

theorem exists_goodSet (K : Type) [Field K] [CharZero K] (G : Type) [Group G] [Fintype G] (X : Finset (G → K))
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P0 : Formalism.MainNotions.PrimeDegreeVariant.Pair K G) [Fintype P0.H]
    (h1 : ∀ χ ∈ X, ∑ h : P0.H, χ (h : G) * (((P0.chi h)⁻¹ : Kˣ) : K) = (Fintype.card P0.H : K)) :
    ∃ T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G,
      (∀ χ, χ ∈ X ↔ ∃ s, χ = fun g => LinearMap.trace K (T.W s) (T.tau s g)) ∧
        Formalism.MainNotions.PrimeDegreeVariant.M1 T P0 ∧ Formalism.MainNotions.PrimeDegreeVariant.eG T = idemOf X := by
  classical
  have key : ∀ s : X, ∃ (n : ℕ) (τ : Representation K G (Fin n → K)), 0 < n ∧
      Function.Surjective τ.asAlgebraHom ∧ ∀ g, LinearMap.trace K (Fin n → K) (τ g) = (s : G → K) g :=
    fun s => GlobalTheory.T.exists_rep_realising_char_of_multiplicity_one K G s (hX s s.2) P0.H P0.chi (h1 s s.2)
  choose n τ hn hs ht using key
  have ht' : ∀ s : X, (fun g => LinearMap.trace K (Fin (n s) → K) (τ s g)) = (s : G → K) := fun s => funext (ht s)
  let T : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G :=
    { S := X
      W := fun s => Fin (n s) → K
      ntW := fun s => by
        have : Nonempty (Fin (n s)) := ⟨⟨0, hn s⟩⟩
        infer_instance
      tau := τ
      irr := hs
      inj := fun a b hab => Subtype.ext (by rw [← ht' a, ← ht' b]; exact hab) }
  refine ⟨T, fun χ => ⟨fun h => ⟨⟨χ, h⟩, (ht' ⟨χ, h⟩).symm⟩, ?_⟩, fun s => ?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact (ht' s).symm ▸ s.2
  · have h2 := (GlobalTheory.CuspidalIdempotentCharacters.finrank_eq_one_iff (τ s) P0.H P0.chi).2 (by
      simp_rw [ht s]
      rw [h1 _ s.2, Nat.card_eq_fintype_card])
    rw [← GlobalTheory.CuspidalIdempotentCharacters.eps_eq_lvlIdem] at h2
    exact h2
  · unfold Formalism.MainNotions.PrimeDegreeVariant.eG idemOf
    rw [← Finset.sum_coe_sort X]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [eS_eq_chiIdem]
    exact congrArg chiIdem (ht' s)

end GlobalTheory.GoodSetOfChars
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerBoundaryEtaleCohomology
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem hk_pull_ext : ∀ (R : Type) [CommRing R] {K L : Cx R} (f : L ⟶ K) {F G : Shv R} {n : ℤ} (z : Cocycle (res R F) (res R G) n) (m k : ℤ) (h : m + n = k) (x : HK R K F m),
  HK.pull R f G k (HK.ext R K z m k h x) = HK.ext R L z m k h (HK.pull R f F m x) := by
  intro R _ K L f F G n z m k h x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem kummer_boundary : ∀ (q : ℕ) [NeZero q], ∃ κ : (restr (Int.castRingHom (ZMod q))).obj (tw q 1) ⟶ Gm, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) U from twGen 1 ζ) = unitSec u) ∧ ∃ bd : ∀ (E : Spc) (n : ℤ), H ℤ E Gm n →+ Ht q E (n + 1) 1, (∀ {E E' : Spc} (f : E ⟶ E'), Inv q E' → ∀ (n : ℤ) x, pull _ f _ _ (bd E' n x) = bd E n (pull _ f _ _ x)) ∧ (∀ (E : Spc), Inv q E → ∀ n : ℤ, Function.Exact (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) n) (bd E n) ∧ Function.Exact (bd E n) (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) ∧ Function.Exact (fun c => HK.post ℤ ((chains ℤ).obj E) κ (n + 1) (restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) c)) (HK.post ℤ ((chains ℤ).obj E) ((q : ℤ) • 𝟙 Gm) (n + 1))) ∧ (∃ s : ℤˣ, ∀ (X : Scheme.{0}) (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → bd (sch.obj X) 0 (secClass Gm (unitSec u)) = s • kum q u) ∧ ∃ s : ℤˣ, ∀ (E : Spc) (L : E ⟶ ofCat (glCat 1)), Inv q E → bd E 1 (picClass L) = s • c1 q L := by
  intro q _
  obtain ⟨κ, hmono, h0, hgen, hker, hloc⟩ := GlobalTheory.T.kummer_sequence_etale_tateTwist q
  refine ⟨κ, hgen, ?_⟩
  let S : ShortComplex (Shv ℤ) := ShortComplex.mk κ (cokernel.π κ) (cokernel.condition κ)
  have hS : S.ShortExact :=
    { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel κ), mono_f := hmono, epi_g := (inferInstance : Epi (cokernel.π κ)) }
  obtain ⟨z, hex, s, hchar⟩ := GlobalTheory.T.exists_connecting_cocycle_hypercohomology_les ℤ S hS
  set qb := cokernel.desc κ ((q : ℤ) • 𝟙 Gm) h0 with hqb
  have hπq : cokernel.π κ ≫ qb = (q : ℤ) • 𝟙 Gm := cokernel.π_desc _ _ _
  have hbij := GlobalTheory.T.kummer_cokernel_to_multiplicativeGroup_bijective q κ h0 hker hloc
  have hP : ∀ E, Inv q E → ∀ n, Function.Bijective (HK.post ℤ ((chains ℤ).obj E) qb n) := fun E hE n =>
    GlobalTheory.T.etaleCohomology_bijective_of_support_bijective ℤ E qb (fun U hU => hbij U (hE U hU)) n
  have hR : ∀ E n, Function.Bijective (restrH (Int.castRingHom (ZMod q)) E (tw q 1) n) := fun E n =>
    GlobalTheory.T.etaleCohomology_coefficientRing_invariance ℤ (ZMod q) _ E (tw q 1) n
  have hpostc : ∀ (K : Cx ℤ) n x, HK.post ℤ K ((q : ℤ) • 𝟙 Gm) n x = HK.post ℤ K qb n (HK.post ℤ K (cokernel.π κ) n x) := by
    intro K n x
    rw [← hπq]
    exact (GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ K n).2.1 _ _ x
  let Pe : ∀ E, Inv q E → ∀ n, H ℤ E (cokernel κ) n ≃+ H ℤ E Gm n := fun E hE n =>
    AddEquiv.ofBijective (HK.post ℤ _ qb n) (hP E hE n)
  let Re : ∀ E n, Ht q E n 1 ≃+ H ℤ E ((restr (Int.castRingHom (ZMod q))).obj (tw q 1)) n := fun E n =>
    AddEquiv.ofBijective (restrH _ E (tw q 1) n) (hR E n)
  have hPe : ∀ E hE n x, Pe E hE n x = HK.post ℤ _ qb n x := fun _ _ _ _ => rfl
  have hRe : ∀ E n x, Re E n x = restrH _ E (tw q 1) n x := fun _ _ _ => rfl
  classical
  let bd : ∀ (E : Spc) (n : ℤ), H ℤ E Gm n →+ Ht q E (n + 1) 1 := fun E n =>
    if hE : Inv q E then
      (Re E (n + 1)).symm.toAddMonoidHom.comp ((HK.ext ℤ _ z n (n + 1) rfl).comp (Pe E hE n).symm.toAddMonoidHom)
    else 0
  have hbd : ∀ E (hE : Inv q E) n x, bd E n x = (Re E (n + 1)).symm (HK.ext ℤ _ z n (n + 1) rfl ((Pe E hE n).symm x)) := by
    intro E hE n x
    simp only [bd, dif_pos hE]
    rfl
  refine ⟨bd, ?_, ?_, ?_, ?_⟩
  · intro E E' f hE' n x
    have hE : Inv q E := fun U ⟨y⟩ => hE' U ⟨(f.app _).app _ y⟩
    rw [hbd E hE, hbd E' hE']
    apply (Re E (n + 1)).injective
    rw [AddEquiv.apply_symm_apply, hRe]
    have h1 : restrH (Int.castRingHom (ZMod q)) E (tw q 1) (n + 1) (pull _ f _ _ ((Re E' (n + 1)).symm
        (HK.ext ℤ _ z n (n + 1) rfl ((Pe E' hE' n).symm x)))) =
        pull _ f _ _ (restrH (Int.castRingHom (ZMod q)) E' (tw q 1) (n + 1) ((Re E' (n + 1)).symm
        (HK.ext ℤ _ z n (n + 1) rfl ((Pe E' hE' n).symm x)))) :=
      ((restrMap (Int.castRingHom (ZMod q)) (tw q 1)).op.nat f (n + 1) _).symm
    rw [h1, ← hRe, AddEquiv.apply_symm_apply]
    have h2 : HK.pull ℤ ((chains ℤ).map f) (cokernel κ) n ((Pe E' hE' n).symm x) = (Pe E hE n).symm (pull _ f _ _ x) := by
      apply (Pe E hE n).injective
      rw [AddEquiv.apply_symm_apply, hPe E hE n]
      change HK.post ℤ _ qb n (HK.pull ℤ ((chains ℤ).map f) _ n _) = HK.pull ℤ ((chains ℤ).map f) _ n x
      rw [← (GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ _ n).2.2.2.2 ((chains ℤ).map f) qb, ← hPe E' hE', AddEquiv.apply_symm_apply]
    change HK.pull ℤ _ _ _ (HK.ext ℤ _ z n (n + 1) rfl _) = _
    rw [hk_pull_ext, h2]
  · intro E hE n
    obtain ⟨e1, e2, e3⟩ := hex ((chains ℤ).obj E) n
    obtain ⟨e1', -, -⟩ := hex ((chains ℤ).obj E) (n + 1)
    refine ⟨fun y => ?_, fun c => ?_, fun y => ?_⟩
    · rw [hbd E hE, AddEquivClass.map_eq_zero_iff, e2]
      constructor
      · rintro ⟨w, hw⟩
        refine ⟨w, ?_⟩
        rw [hpostc, ← hPe E hE, hw]
        exact AddEquiv.apply_symm_apply _ _
      · rintro ⟨w, rfl⟩
        refine ⟨w, ?_⟩
        change _ = (Pe E hE n).symm _
        rw [hpostc, ← hPe E hE, AddEquiv.symm_apply_apply]
    · change HK.post ℤ _ κ (n + 1) (restrH _ E (tw q 1) (n + 1) c) = 0 ↔ _
      rw [show HK.post ℤ _ κ (n + 1) = HK.post ℤ _ S.f (n + 1) from rfl, e3]
      constructor
      · rintro ⟨w, hw⟩
        refine ⟨(Pe E hE n) w, ?_⟩
        rw [hbd E hE, AddEquiv.symm_apply_apply]
        apply (Re E (n + 1)).injective
        rw [AddEquiv.apply_symm_apply, hw, hRe]
      · rintro ⟨w, rfl⟩
        refine ⟨(Pe E hE n).symm w, ?_⟩
        rw [hbd E hE, ← hRe, AddEquiv.apply_symm_apply]
    · rw [hpostc]
      have : HK.post ℤ _ qb (n + 1) (HK.post ℤ _ (cokernel.π κ) (n + 1) y) = 0 ↔ HK.post ℤ _ (cokernel.π κ) (n + 1) y = 0 := by
        rw [← hPe E hE]; exact (Pe E hE (n + 1)).map_eq_zero_iff
      rw [this, show HK.post ℤ _ (cokernel.π κ) (n + 1) = HK.post ℤ _ S.g (n + 1) from rfl, e1']
      constructor
      · rintro ⟨w, rfl⟩
        refine ⟨(Re E (n + 1)).symm w, ?_⟩
        change HK.post ℤ _ κ (n + 1) (Re E (n + 1) _) = _
        rw [AddEquiv.apply_symm_apply]
      · rintro ⟨c, rfl⟩
        exact ⟨_, rfl⟩
  · refine ⟨s, fun X u hu => ?_⟩
    have hE : Inv q (sch.obj X) := by
      rintro U ⟨x⟩
      have := hu.map x.appTop.hom
      rw [map_natCast] at this
      exact this
    obtain ⟨c, hc⟩ := (hbij X hu).2 (unitSec u)
    have hpre : (Pe _ hE 0).symm (secClass Gm (unitSec u)) = secClass (cokernel κ) c := by
      apply (Pe _ hE 0).injective
      rw [AddEquiv.apply_symm_apply, hPe _ hE 0, (GlobalTheory.T.degreeZeroSectionClass_properties ℤ (cokernel κ) X).2.2.2.2 qb c, hc]
    rw [hbd _ hE, hpre, GlobalTheory.T.kummerConnecting_unitClass_eq_kummerClass q κ h0 hmono hgen hker hloc hbij z s hchar X u c hu hc, Units.smul_def, Units.smul_def,
      map_zsmul, ← hRe, AddEquiv.symm_apply_apply]
  · refine ⟨s, fun E L hE => ?_⟩
    have hy : HK.post ℤ _ qb 1 ((Pe E hE 1).symm (picClass L)) = picClass L := by
      rw [← hPe E hE, AddEquiv.apply_symm_apply]
    rw [hbd E hE, GlobalTheory.T.kummerBoundary_lineBundle_firstChernClass q κ h0 hmono hgen hker hloc hbij z s hchar E L hE _ hy, Units.smul_def, Units.smul_def,
      map_zsmul, ← hRe, AddEquiv.symm_apply_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulEqRegularValueBasicOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_mul_eq_regularValue_basicOpen : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (U : A.left.Opens), IsAffineOpen U → ∀ (r : Γ(A.left, U)) (k : (Fin g → ℂ) → ℂ), IsReg u.ex (A.left.basicOpen r) k → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ b : Γ(A.left, U), ∀ z ∈ pre u.ex (A.left.basicOpen r), val u.ex U b z = val u.ex U r z ^ N * k z := by
  first | exact @GlobalTheory.ClearDen.exists_pow_mul_eq_val | exact GlobalTheory.ClearDen.exists_pow_mul_eq_val | (intros; apply GlobalTheory.ClearDen.exists_pow_mul_eq_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroMoveTensorHolomorphic
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroMove

theorem gen_hom {A C : Type} [CommRing A] [CommRing C] {g : ℕ} (ψ : A →+* C) (D : Fin g → A →+ A)
    (h1 : ∀ a, D a 1 = 0) (hL : ∀ a x y, D a (x * y) = x * D a y + y * D a x)
    (n : Fin g → C) (hn : ∀ a b, n a * n b = 0) :
    ∃ ψ' : A →+* C, ∀ x, ψ' x = ψ x + ∑ a, ψ (D a x) * n a := by
  have hsq : ∀ (u v : Fin g → C), (∑ a, u a * n a) * (∑ b, v b * n b) = 0 := by
    intro u v
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b _ => ?_))
    calc u a * n a * (v b * n b) = u a * v b * (n a * n b) := by ring
      _ = 0 := by rw [hn a b, mul_zero]
  refine ⟨{ toFun := fun x => ψ x + ∑ a, ψ (D a x) * n a,
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun x => rfl⟩
  · simp [h1]
  · intro x y
    have e := hsq (fun a => ψ (D a x)) (fun a => ψ (D a y))
    simp only [hL, map_add, map_mul, add_mul, Finset.sum_add_distrib]
    have ex : ∑ a, ψ x * ψ (D a y) * n a = ψ x * ∑ a, ψ (D a y) * n a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
    have ey : ∑ a, ψ y * ψ (D a x) * n a = ψ y * ∑ a, ψ (D a x) * n a := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [ex, ey]
    linear_combination (-1 : C) * e
  · simp
  · intro x y
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    ring

theorem lTensor_leibniz {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) (x y : R ⊗[ℂ] S) :
    LinearMap.lTensor R d.toLinearMap (x * y) =
      x * LinearMap.lTensor R d.toLinearMap y + y * LinearMap.lTensor R d.toLinearMap x := by
  first
  | exact @_root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz
  | exact _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz
  | (apply _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorLeibnizRule.lTensor_leibniz ..)

theorem lTensor_one {R S : Type} [CommRing R] [Algebra ℂ R] [CommRing S] [Algebra ℂ S]
    (d : Derivation ℂ S S) : LinearMap.lTensor R d.toLinearMap (1 : R ⊗[ℂ] S) = 0 := by
  rw [Algebra.TensorProduct.one_def, LinearMap.lTensor_tmul, Derivation.coeFn_coe, Derivation.map_one_eq_zero,
    TensorProduct.tmul_zero]

theorem sqZeroMove : ∀ {g : ℕ} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (ψ : R ⊗[ℂ] Hol W₀ →+* C) (n : Fin g → C), (∀ a b, n a * n b = 0) → ∃ ψ' : R ⊗[ℂ] Hol W₀ →+* C, ∀ x, ψ' x = ψ x + ∑ a, ψ (LinearMap.lTensor R (dw a).toLinearMap x) * n a := by
  intro g W₀ R _ _ C _ ψ n hn
  exact gen_hom ψ (fun a => (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap).toAddMonoidHom)
    (fun a => lTensor_one _) (fun a x y => lTensor_leibniz _ x y) n hn

end GlobalTheory.SqZeroMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselizationAtMaximalStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_strictHenselization_at_maximal : ∀ (B : Type) [CommRing B] (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∃ (O : Type) (_ : CommRing O) (_ : Algebra B O), SH O ∧ IndEt B O ∧ ∀ Q : Ideal O, Q.IsMaximal → Q.comap (algebraMap B O) = P ∧ ∀ o : O, ∃ b : B, o - algebraMap B O b ∈ Q := by
  first | (exact @GlobalTheory.HensMax.exists_strictHens_of_maximal) | (exact GlobalTheory.HensMax.exists_strictHens_of_maximal) | (intros; apply GlobalTheory.HensMax.exists_strictHens_of_maximal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionMatrixOfConjugateTransportStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_matrix_of_conjugateTransport : ∀ (K : Type) [Field K] [NumberField K] (ι : K →+* ℂ) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁ → ∀ (c₀ c₁ : ℂ) (τ₀ τ₁ : ℍ), IsTauOf Λ₀ c₀ τ₀ → IsTauOf Λ₁ c₁ τ₁ → ∀ (N : ℕ) [NeZero N], ∃ A : GL (Fin 2) (ZMod N), ∀ x, ∃ k k' : K, ι k = c₀ * tors N τ₀ x ∧ ι k' = c₁ * tors N τ₁ (vmul x A) ∧ Tr t k k' := by
  first | exact @GlobalTheory.WpFam.exists_torsion_matrix | exact GlobalTheory.WpFam.exists_torsion_matrix | (intros; apply GlobalTheory.WpFam.exists_torsion_matrix <;> assumption)
end

