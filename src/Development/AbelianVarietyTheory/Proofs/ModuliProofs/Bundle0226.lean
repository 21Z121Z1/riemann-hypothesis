import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0223
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0225
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0158
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0199
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0209

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleHeckeKernelListsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteEtale_heckeKernel_lists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s), admitted l 𝔓 p → ∃ (Y : Scheme.{0}) (a : Y ⟶ S) (oY : Ob D l (a ≫ s)) (m : ObjMap oY o a) (σ : Fin n → (𝟙_ (Over Y) ⟶ oY.t.G)) (K : Set oY.t.G.left), IsFinite a ∧ Etale a ∧ Lists (p ^ 2) σ K ∧ HeckeSet D oY.t 𝔓 p i K ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t : SAB H T) (mu : SABMap t o.t f) (τ : Fin n → (𝟙_ (Over T) ⟶ t.G)) (K' : Set t.G.left), Lists (p ^ 2) τ K' → HeckeSet D t 𝔓 p i K' → ∃! h : T ⟶ Y, h ≫ a = f ∧ ∀ j, h ≫ (σ j).left ≫ m.toSABMap.φ = (τ j).left ≫ mu.φ := by
  first | exact @GlobalTheory.exists_finiteEtale_heckeLists | exact GlobalTheory.exists_finiteEtale_heckeLists | (intros; apply GlobalTheory.exists_finiteEtale_heckeLists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenericObjectMinimalPrimeModuliChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.GenericObject

theorem isThetaPt_unit_mul {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S} {I : Type} (x : I → (T ⟶ P.A))
    (v v' : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (hc : IsUnit c) (hv : ∀ i, v' i = c * v i)
    (h : Out.IsThetaPt P k x v) : Out.IsThetaPt P k x v' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hp, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  have hc1 : IsUnit (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom c) := hc.map V.ι.appTop.hom
  obtain ⟨c', hc'⟩ := hc1
  refine ⟨V, hp, th, s1, α, τ, U, s2, w, c' * u, a1, a2, a3, a4, a5, a6, a7, fun i => ?_⟩
  have e1 : (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom (v' i)) =
      (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom c) * (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom (v i)) := by
    rw [hv i]
    exact map_mul V.ι.appTop.hom c (v i)
  have e2 : (show Γ((Out.overRes V).left, ⊤) from V.ι.appTop.hom (v i)) = u * w i := a8 i
  rw [← hc', e2, ← _root_.mul_assoc] at e1
  exact e1

theorem hasTh_unit_mul {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s) {R : Type} [CommRing R] (x : Sp R ⟶ S) (v v' : Ix g (N' ^ 2) → R) (c : R) (hc : IsUnit c)
    (hv : ∀ a, v' a = c * v a) (h : t.HasTh x v) : t.HasTh x v' := by
  refine isThetaPt_unit_mul _ _ _ _ _ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) (hc.map _) (fun a => ?_) h
  rw [hv a]
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c (v a)

theorem countable_of_finiteType (o : Type) [CommRing o] (h : Algebra.FiniteType ℤ o) : Countable o := by
  obtain ⟨m, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 h
  have : Countable (MvPolynomial (Fin m) ℤ) :=
    (MvPolynomial.basisMonomials (Fin m) ℤ).repr.injective.countable
  exact hf.countable

theorem exists_generic_object : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (Y : MMPre n (n ^ j) (thIdeal em C)) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g ((n ^ j) ^ 2) → R), IsOpenImmersion x → x ≫ Y.s = spMap β → SecCoord Y.de Y.th x v → ∀ q ∈ minimalPrimes R, ∃ (K : Type) (_ : Field K) (y : R →+* K) (e : K →+* ℂ) (t : TObj g ((n ^ j) ^ 2) J b (spMap y ≫ spMap β)) (tc : TObj g ((n ^ j) ^ 2) J b (spMap em)), RingHom.ker y = q ∧ e.comp (y.comp β) = em ∧ C tc ∧ TMap tc t (spMap e) ∧ t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => y (v a)) := by
  intro L1 L2 g J _ Mat κ n w w' hn hodd
  obtain ⟨j₀, hj₀⟩ := GlobalTheory.T.descend_to_thetaConstant_field L1 L2 g J Mat κ n w w' hn hodd
  refine ⟨max j₀ 1, fun j hj o _ b em C d har hC Y R _ β x v hx hxs hv q hq => ?_⟩
  have hj0 : j ≥ j₀ := le_trans (le_max_left _ _) hj
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hn3 : 3 ≤ n := by
    have h2 := hn.two_le
    obtain ⟨m, hm⟩ := hodd
    omega
  have hN3 : 3 ≤ n ^ j := le_trans hn3 (Nat.le_self_pow (by omega) n)
  have hNodd : Odd (n ^ j) := hodd.pow
  haveI hqp : q.IsPrime := hq.1.1
  let K := FractionRing (R ⧸ q)
  let y : R →+* K := (algebraMap (R ⧸ q) K).comp (Ideal.Quotient.mk q)
  have hy0 : ∀ r, y r = 0 ↔ r ∈ q := fun r => by
    simp only [y, RingHom.comp_apply]
    rw [map_eq_zero_iff _ (IsFractionRing.injective (R ⧸ q) K), Ideal.Quotient.eq_zero_iff_mem]
  have hker : RingHom.ker y = q := Ideal.ext fun r => by rw [RingHom.mem_ker, hy0]
  have hfrac : ∀ k : K, ∃ r r' : R, y r' ≠ 0 ∧ k * y r' = y r := by
    intro k
    obtain ⟨a, a', ha', rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ q) k
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective a'
    have h0 : algebraMap (R ⧸ q) K (Ideal.Quotient.mk q r') ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := K) ha'
    exact ⟨r, r', h0, div_mul_cancel₀ _ h0⟩
  obtain ⟨c₀, hc₀⟩ := (Y.loc R β x v hxs hv).2 q hqp 0
  set a₀ := (0 : Ix g ((n ^ j) ^ 2)) + (n ^ j / n) • c₀ with ha₀
  have hva : y (v a₀) ≠ 0 := fun h => hc₀ ((hy0 _).1 h)
  obtain ⟨hcl, hmin⟩ := GlobalTheory.CoordChart.residue_generic o g n (n ^ j) (thIdeal em C) Y R β x v K y a₀ (by omega) hx hxs hv hfrac hva
  have hmin' := hmin (by rw [hker]; exact hq)
  obtain ⟨-, hhom, -⟩ := GlobalTheory.T.thetaPointsVanishingIdeal_radical_homogeneous o g (n ^ j) J b em C har.2.2
  have hu : (fun a => y (v a) / y (v a₀)) a₀ = 1 := div_self hva
  have hP := GlobalTheory.ker_cone_mem_minimalPrimes o _ K (thIdeal em C) (y.comp β) (fun a => y (v a) / y (v a₀)) a₀ hhom hu hmin'
  obtain ⟨tc, wv, htc, hth, hkw⟩ := GlobalTheory.ZM.exists_object_at_minimalPrime o g (n ^ j) J b em C Mat κ w w' d L1 L2 hN3 hNodd
    (countable_of_finiteType o har.2.1) hC _ hP
  obtain ⟨e, c, hc, he, hec⟩ := GlobalTheory.T.exists_complex_embedding_scaling_of_ker_eval_eq o K _ (y.comp β) em (fun a => y (v a) / y (v a₀)) wv a₀
    (div_ne_zero hva hva) (by simpa only [div_self hva, div_one] using hcl) hkw.symm
  have heva : e (y (v a₀)) ≠ 0 := (map_ne_zero e).2 hva
  have hth' : tc.HasTh (𝟙 _) (fun a => e (y (v a))) := by
    refine hasTh_unit_mul tc _ wv _ (e (y (v a₀)) * c) (IsUnit.mk0 _ (mul_ne_zero heva hc)) (fun a => ?_) hth
    have := hec a
    simp only [map_div₀] at this
    rw [_root_.mul_assoc, ← this]
    field_simp
  have hs : spMap em = spMap e ≫ spMap (y.comp β) := by
    rw [← he]
    exact Spec.map_comp (CommRingCat.ofHom (y.comp β)) (CommRingCat.ofHom e)
  have hs' : spMap (y.comp β) = spMap y ≫ spMap β :=
    Spec.map_comp (CommRingCat.ofHom β) (CommRingCat.ofHom y)
  have key := hj₀ j hj0 o b K ℂ (y.comp β) e (spMap em) tc (fun a => y (v a)) hs (hC.shape tc htc).1 (hC.shape tc htc).2 hth'
  rw [hs'] at key
  obtain ⟨t, h1, h2, h3, h4⟩ := key
  exact ⟨K, inferInstance, y, e, t, tc, hker, he, htc, h1, h2, h3, h4⟩

end GlobalTheory.GenericObject
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoQuotientsSameKernelReducedBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_quotients_same_kernel_reduced_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o o₁ o₂ : Ob D l s) (ψ₁ : o.t.G ⟶ o₁.t.G) (ψ₂ : o.t.G ⟶ o₂.t.G) (K : Set o.t.G.left), p.Prime → ¬ p ∣ l.M' → IsIsog o o₁ p ψ₁ → IsIsog o o₂ p ψ₂ → KerSet ψ₁ K → KerSet ψ₂ K → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ o.t.G), Set.range z.left ⊆ K → z ^ p ^ 2 = 1) → ∃ m : ObjMap o₁ o₂ (𝟙 S), ψ₁.left ≫ m.toSABMap.φ = ψ₂.left := by
  first | exact @GlobalTheory.exists_objMap_of_isIsog_of_kerSet | exact GlobalTheory.exists_objMap_of_isIsog_of_kerSet | (intros; apply GlobalTheory.exists_objMap_of_isIsog_of_kerSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientTripleFamilyReducedNoetherianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_triple_family_reduced_noetherian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (t : SAB H (Sp R)) (g p : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : t.G ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R), Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = p ^ (2 * g) ∧ ∀ z : Over.mk x ⟶ t.G, z ≫ ψ = 1 → z ^ p ^ 2 = 1 ∧ ∀ a, (z ≫ t.act.act a) ≫ ψ = 1) → LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) → ∃ (t' : SAB H (Sp R)) (ψ' : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsIsogT t t' p ψ' ∧ ∀ (T : Over (Sp R)) (z : T ⟶ t.G), z ≫ ψ' = 1 ↔ z ≫ ψ = 1 := by
  first | exact @GlobalTheory.HkFam.exists_quotient_triple_family | exact GlobalTheory.HkFam.exists_quotient_triple_family | (intros; apply GlobalTheory.HkFam.exists_quotient_triple_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GoodThetaClassOfLatticeFamilies
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem countable_addEquiv_of_free_finite (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] :
    Countable (La ≃+ La) := by
  let bas := Module.Free.chooseBasis ℤ La
  haveI : Countable La := bas.equivFun.injective.countable
  have hinj : Function.Injective (fun (gm : La ≃+ La) (i : Module.Free.ChooseBasisIndex ℤ La) => gm (bas i)) := by
    intro gm gm' h
    have h2 : gm.toAddMonoidHom.toIntLinearMap = gm'.toAddMonoidHom.toIntLinearMap :=
      bas.ext (fun i => congrFun h i)
    ext x
    exact LinearMap.congr_fun h2 x
  exact hinj.countable

theorem goodClass_of_lattice_families : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (o : Type) [CommRing o] (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) (d r : ℕ) (La : Fin r → Type) [∀ i, AddCommGroup (La i)] (EF : ∀ i, LinearMap.BilinForm ℤ (La i)) (lam : ∀ i, Fin (2 * g) → La i) (ac : ∀ i, J → La i → La i) (B : Fin r → Set (Fin d → ℂ)) (Q : ∀ i, (Fin d → ℂ) → (La i →+ (Fin g → ℂ))) (Hm : Fin r → (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ t t', C t → TMap t' t (𝟙 _) → C t') → (∀ t, C t → t.Prim w w') → (∀ i, Function.Bijective (EF i) ∧ IsOpen (B i) ∧ IsPreconnected (B i) ∧ (∀ x, DifferentiableOn ℂ (fun bb => Q i bb x) (B i)) ∧ (∀ x, ac i w x + ac i w' x = x) ∧ (∀ x y, EF i (ac i w x) y = EF i x (ac i w' y)) ∧ (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF i (lam i i₁) (lam i i₂) : ℂ) / ((N' ^ 2 : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) ∧ (∀ j₁ i₁, ∃ y, ac i j₁ (lam i i₁) = ∑ i', Mat j₁ i' i₁ • lam i i' + (N' ^ 2) • y) ∧ (∀ bb ∈ B i, (Function.Injective (Q i bb) ∧ DiscreteTopology ((Q i bb)).range ∧ Submodule.span ℝ (Set.range (Q i bb)) = ⊤ ∧ ((Hm i bb)).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (Hm i bb) z z).re) ∧ ∀ x y, (hermForm (Hm i bb) ((Q i bb) x) ((Q i bb) y)).im = EF i x y) ∧ ∀ j₁, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q i bb x) = Q i bb (ac i j₁ x)) ∧ ∀ y, y ≠ 0 → (hermForm (Hm i bb) (F y) (F y)).re < κ * (hermForm (Hm i bb) y y).re) ∧ (∀ bb ∈ B i, ∀ z' ∈ B i, (∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ x, Q i z' x = h (Q i bb x)) → bb = z') ∧ ∀ bb ∈ B i, ∀ t : TObj g (N' ^ 2) J b (spMap em), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH (Hm i bb) χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ ((Q i bb)).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = (Q i bb) x → χ' l = (-1) ^ EF i x (ac i w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • (Q i bb) (lam i i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F ((Q i bb) x) = (Q i bb) (ac i j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.Prim w w' → C t) → (∀ t, C t → ∃ i, ∃ bb ∈ B i, (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH (Hm i bb) χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ ((Q i bb)).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = (Q i bb) x → χ' l = (-1) ^ EF i x (ac i w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • (Q i bb) (lam i i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F ((Q i bb) x) = (Q i bb) (ac i j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀)) → GoodClass em C Mat κ w w' d := by
  intro h1 h2 h3 h4 g J _ Mat κ n w w' hn hodd
  obtain ⟨j₀, hqt⟩ := GlobalTheory.T.thetaPoint_determines_shape_complex h1 h2 g J Mat κ n hn hodd
  refine ⟨max j₀ 1, ?_⟩
  intro j hj N' hN' o _ b em C d r La _ EF lam ac B Q Hm hiso hprim hfam hcov
  subst hN'
  have hj0 : j ≥ j₀ := le_trans (le_max_left _ _) hj
  have hj1 : j ≠ 0 := by have := le_trans (le_max_right _ _) hj; omega
  have hth := fun i => GlobalTheory.T.exists_holomorphic_thetaConstants_polarisedLattices h1 h2 h3 h4 o g (n ^ j) J b em w w' (La i) (EF i) (lam i) (ac i) d (B i) (Q i) (Hm i)
    hodd.pow (hfam i).1 (hfam i).2.1 (hfam i).2.2.2.1
    (fun bb hbb => ⟨((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).1,
      (((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).2 w).imp fun F hF => hF.1⟩)
    (hfam i).2.2.2.2.1 (hfam i).2.2.2.2.2.1
  choose θ hθd hθ using hth
  have hsh := fun i bb (hbb : bb ∈ B i) t ht => GlobalTheory.T.shape_of_uniformised_theta_object h1 h2 h3 h4 o g ((n ^ j) ^ 2) J b em w w' t (La i) (EF i)
    (lam i) (ac i) (Q i bb) (Hm i bb) Mat κ ht (hfam i).2.2.2.2.2.2.2.1 ((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).2
  have hbuild := fun i bb (hbb : bb ∈ B i) => GlobalTheory.T.exists_thetaObject_of_polarisedLattice h1 h2 h3 h4 o g ((n ^ j) ^ 2) J b em w w' (La i) (EF i)
    (lam i) (ac i) (Q i bb) (Hm i bb) (hfam i).1 ((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).1
    (fun j₁ => (((hfam i).2.2.2.2.2.2.2.2.1 bb hbb).2 j₁).imp fun F hF => hF.1)
    (hfam i).2.2.2.2.1 (hfam i).2.2.2.2.2.1 (hfam i).2.2.2.2.2.2.1
  refine ⟨hiso, fun t ht => ⟨?_, hprim t ht⟩, r, B, θ, fun i => ⟨(hfam i).2.1, (hfam i).2.2.1, hθd i, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · obtain ⟨i, bb, hbb, hu⟩ := hcov t ht
    exact hsh i bb hbb t hu
  · obtain ⟨t, htp, hu⟩ := hbuild i z hz
    exact ⟨t, (hfam i).2.2.2.2.2.2.2.2.2.2 z hz t hu htp, hθ i z hz t hu⟩
  · obtain ⟨hfree, hfin, -⟩ := unimodular_symplectic_coordinates_and_lattice_rank.2 (La i) (EF i) g (Q i z) (Hm i z)
      ((hfam i).2.2.2.2.2.2.2.2.1 z hz).1
    haveI := countable_addEquiv_of_free_finite (La i)
    have hc : (⋃ gm : La i ≃+ La i, {z' ∈ B i | ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ),
        ∀ x, h (Q i z' x) = Q i z (gm x)}).Countable := by
      refine Set.countable_iUnion fun gm => Set.Subsingleton.countable ?_
      rintro z₁ ⟨hz₁, k₁, hk₁⟩ z₂ ⟨hz₂, k₂, hk₂⟩
      refine (hfam i).2.2.2.2.2.2.2.2.2.1 z₁ hz₁ z₂ hz₂ ⟨k₁.trans k₂.symm, fun x => ?_⟩
      rw [LinearEquiv.trans_apply, hk₁, ← hk₂, LinearEquiv.symm_apply_apply]
    refine hc.mono ?_
    rintro z' ⟨hz', c, hcz⟩
    obtain ⟨t, -, hu⟩ := hbuild i z hz
    obtain ⟨t', -, hu'⟩ := hbuild i z' hz'
    have ht' := hθ i z' hz' t' hu'
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨a, ha⟩ := GlobalTheory.T.thetaCosetNonvanishing_of_hasTh h1 h2 o g (n ^ j) J b _ _ t' n ℂ (𝟙 _) (θ i z') ⊥ hn.two_le
        (dvd_pow_self n hj1) ht' Ideal.isPrime_bot 0
      apply ha
      rw [hcz]
      simp
    rw [hcz] at ht'
    have hm := hqt j hj0 o b em t t' (θ i z) c hc0 (hsh i z hz t hu) (hsh i z' hz' t' hu') (hθ i z hz t hu) ht'
    obtain ⟨gm, h, hgm⟩ := GlobalTheory.T.exists_lattice_aut_of_isomorphic_theta_objects o g ((n ^ j) ^ 2) J b em w w' t t' (La i) (EF i) (lam i) (ac i) (Q i z) (Q i z')
      (Hm i z) (Hm i z') ((hfam i).2.2.2.2.2.2.2.2.1 z hz).1.1 ((hfam i).2.2.2.2.2.2.2.2.1 z' hz').1.1 hu hu' hm
    exact Set.mem_iUnion.2 ⟨gm, hz', h, hgm⟩
  · intro t ht
    obtain ⟨i, bb, hbb, hu⟩ := hcov t ht
    exact ⟨i, bb, hbb, hθ i bb hbb t hu⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeKernelSchemeGeometricPointsEqKernelsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeKernelScheme_geometric_points_eq_kernels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo 𝔓 p i), admitted l 𝔓 p → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X) (C : Subgroup (Over.mk y ⟶ Xo.univ.t.G)), Xo.univ.t.HeckeKer (Over.mk y) D 𝔓 p i C → ∃! z : Sp k ⟶ Z.Hk, Z.Carries z y C) ∧ (i ≤ D.p + D.q → Surjective Z.π₁) := by
  first | exact @GlobalTheory.kerScheme_points | exact GlobalTheory.kerScheme_points | (intros; apply GlobalTheory.kerScheme_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors

theorem torsionIso_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso :=
  GlobalTheory.UT.torsionIso_of_pelUnif GlobalTheory.firstFiveLaws
    GlobalTheory.twistBaseChange_and_valuation_statements.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.2.2

end GlobalTheory.FlatTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.VeryDenseClosedPointObjectsOfMinimalPrimes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory
namespace ClosedPts

theorem spMap_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]
  rfl

theorem jacobson_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_bot]
    by_contra h0
    have h1 := Ideal.mem_jacobson_bot.1 hx x
    have h2 : 0 < x * x := mul_self_pos.2 h0
    rcases Int.isUnit_iff.1 h1 with h3 | h3 <;> omega
  · have := Ring.DimensionLEOne.maximalOfPrime h hP
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem exists_maximal_notMem {R : Type} [CommRing R] [IsJacobsonRing R] (q : Ideal R) (f : R) (hq : q.IsPrime)
    (hf : f ∉ q) : ∃ m : Ideal R, m.IsMaximal ∧ q ≤ m ∧ f ∉ m := by
  by_contra hc
  push Not at hc
  apply hf
  rw [← IsJacobsonRing.out inferInstance hq.isRadical, Ideal.jacobson, Ideal.mem_sInf]
  rintro m ⟨h1, h2⟩
  exact hc m h2 h1

theorem charZero_quotient {o R : Type} [CommRing o] [IsDomain o] [CharZero o] [CommRing R] [Algebra o R]
    [Module.Flat o R] {q : Ideal R} (hq : q ∈ minimalPrimes R) : CharZero (R ⧸ q) := by
  have hp : q.IsPrime := hq.1.1
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra h0
  have h1 : (n : o) ∈ nonZeroDivisors o := mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast h0)
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := R) h1
  have h2 : (n : R) ∈ q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hn
  refine Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hq) h2 ?_
  refine mem_nonZeroDivisors_iff_left.2 fun x hx => hreg ?_
  simpa [Algebra.smul_def] using hx

theorem finiteType_int_of_surjective {A B : Type} [CommRing A] [CommRing B] [Algebra.FiniteType ℤ A] (f : A →+* B)
    (hf : Function.Surjective f) : Algebra.FiniteType ℤ B :=
  Algebra.FiniteType.of_surjective f.toIntAlgHom hf

theorem range_spMap_fraction (V K : Type) [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K] :
    Set.range (spMap (algebraMap V K)) = {genericPoint (Sp V)} := by
  rw [genericPoint_eq_bot_of_affine]
  have key : ∀ y : Sp K, spMap (algebraMap V K) y = (⊥ : PrimeSpectrum V) := fun y => by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap V K) y.asIdeal = ⊥
    have hy : y.asIdeal = (⊥ : Ideal K) := Ideal.eq_bot_of_prime (K := K) y.asIdeal (h := y.isPrime)
    rw [hy]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V K)
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact key y
  · rintro rfl
    exact ⟨(⊥ : PrimeSpectrum K), key _⟩

theorem exists_pull (h2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) {A B : Type} [CommRing A] [CommRing B] (e : A →+* B)
    {s : Sp A ⟶ Sp o} (s' : Sp B ⟶ Sp o) (hs : spMap e ≫ s = s') (t : TObj g (N' ^ 2) J b s)
    (v : Ix g (N' ^ 2) → A) (hsh : t.Shape Mat κ) (hv : t.HasTh (𝟙 _) v) :
    ∃ t' : TObj g (N' ^ 2) J b s', t'.Shape Mat κ ∧ t'.HasTh (𝟙 _) (fun a => e (v a)) ∧
      ∀ w w' : J, t.Prim w w' → t'.Prim w w' := by
  obtain ⟨t', ht'⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g _ J b _ _ s s' (spMap e) t hs
  refine ⟨t', ?_, ?_, fun w w' => (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w w' _ _ s s' _ t t' ht').2.1⟩
  · intro j
    exact (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ j j _ _ s s' _ t t' ht').1 hsh j
  · rw [GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b _ s t _ s' t' _ B (𝟙 _) _ ht', Category.id_comp]
    have := GlobalTheory.T.hasThetaConstants_ring_baseChange h2 o g N' J b _ s t A B e (𝟙 _) v hv
    rwa [Category.comp_id] at this

end ClosedPts

open ClosedPts in

theorem veryDense_objPrimes_of_minimalPrimes : Out.Laws → Out.Laws2 → (∀ (g n : ℕ) (J : Type) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Finite (IsLocalRing.ResidueField V)] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (β : o →+* V) (t : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V K) ≫ spMap β)) (v : Ix g ((n ^ j) ^ 2) → V), t.Prim w w' → t.HasTh (𝟙 _) (fun a => algebraMap V K (v a)) → Coset n (n ^ j) v (IsLocalRing.maximalIdeal V) → ∃ (V' K' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : Field K') (_ : Algebra V' K') (_ : IsFractionRing V' K') (φ : V →+* V') (ψ : K →+* K') (t' : TObj g ((n ^ j) ^ 2) J b (spMap φ ≫ spMap β)) (tK : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap V' K') ≫ spMap φ ≫ spMap β)), IsLocalHom φ ∧ ψ.comp (algebraMap V K) = (algebraMap V' K').comp φ ∧ TMap tK t (spMap ψ) ∧ TMap tK t' (spMap (algebraMap V' K')) ∧ t'.HasTh (𝟙 _) (fun a => φ (v a))) → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ) (w w' : J), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (C : TObj g ((n ^ j) ^ 2) J b (spMap em) → Prop) (d : ℕ), ArBase em → GoodClass em C Mat κ w w' d → ∀ (R : Type) [CommRing R] [Algebra o R] (v : Ix g ((n ^ j) ^ 2) → R), Algebra.FiniteType o R → IsReduced R → Module.Flat o R → InMM n (n ^ j) (thIdeal em C) (algebraMap o R) v → (∀ q ∈ minimalPrimes R, ∃ (K : Type) (_ : Field K) (x : R →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap (algebraMap o R))), RingHom.ker x = q ∧ t.Shape Mat κ ∧ t.Prim w w' ∧ t.HasTh (𝟙 _) (fun a => x (v a))) → VeryDense (objPrimes b Mat κ (algebraMap o R) v) := by
  intro h1 h2 crit g J _ Mat κ n w w' hn hodd
  obtain ⟨j₁, crit⟩ := crit g n J w w' hn hodd
  obtain ⟨j₂, desc⟩ := GlobalTheory.T.descend_to_thetaConstant_field h1 h2 g J Mat κ n w w' hn hodd
  refine ⟨max j₁ j₂, fun j hj o _ b em C d har _ R _ _ v hft _ hflat hMM hmin q f hq hf => ?_⟩
  obtain ⟨hded, hfo, hinj⟩ := har
  have : CharZero o := em.charZero
  have : Algebra.FiniteType ℤ R := Algebra.FiniteType.trans hfo hft
  have := jacobson_int
  have : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ)
  obtain ⟨m, hm, hqm, hfm⟩ := exists_maximal_notMem q f hq hf
  refine ⟨m, ?_, hm.isPrime, hqm, hfm⟩
  have := hm.isPrime
  obtain ⟨q₀, hq₀, hq₀m⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal R)) (J := m) bot_le
  have hp₀ : q₀.IsPrime := hq₀.1.1
  have : CharZero (R ⧸ q₀) := charZero_quotient (o := o) hq₀
  have := finiteType_int_of_surjective (Ideal.Quotient.mk q₀) Ideal.Quotient.mk_surjective
  obtain ⟨K, _, x, t, hx, hsh, hpr, hth⟩ := hmin q₀ hq₀

  let Ω := AlgebraicClosure K
  obtain ⟨tΩ, hshΩ, hthΩ, hprΩ⟩ := exists_pull h2 Mat κ (algebraMap K Ω) _ rfl t _ hsh hth

  let R₀ := R ⧸ q₀
  let K₀ := FractionRing R₀
  let π : R →+* R₀ := Ideal.Quotient.mk q₀
  let x₀ : R₀ →+* Ω := Ideal.Quotient.lift q₀ ((algebraMap K Ω).comp x) fun a ha => by
    rw [← hx, RingHom.mem_ker] at ha
    simp [ha]
  have hx₀ : Function.Injective x₀ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : algebraMap K Ω (x a) = 0 := ha
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hx, RingHom.mem_ker]
    exact (map_eq_zero _).1 this
  let e : K₀ →+* Ω := IsFractionRing.lift hx₀
  have he : ∀ a : R, e (algebraMap R₀ K₀ (π a)) = algebraMap K Ω (x a) := fun a => by
    simp only [e, IsFractionRing.lift_algebraMap]
    rfl
  let β₀ : o →+* R₀ := π.comp (algebraMap o R)
  obtain ⟨t₀, -, hsh₀, hpr₀, hth₀⟩ := desc j (le_of_max_le_right hj) o b K₀ Ω ((algebraMap R₀ K₀).comp β₀) e _ tΩ
    (fun a => algebraMap R₀ K₀ (π (v a))) (by
      simp only [spMap_spMap]
      congr 1
      ext a
      exact (he _).symm) hshΩ (hprΩ w w' hpr) (by simpa only [he] using hthΩ)
  obtain ⟨t₁, hsh₁, hth₁, hpr₁⟩ := exists_pull h2 Mat κ (RingHom.id K₀) (spMap (algebraMap R₀ K₀) ≫ spMap β₀)
    (by simp only [spMap_spMap, RingHom.id_comp]) t₀ _ hsh₀ hth₀

  have hker : RingHom.ker π ≤ m := by rwa [Ideal.mk_ker]
  have hm₀ : (m.map π).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective π Ideal.Quotient.mk_surjective hm).resolve_left fun h => by
      have := Ideal.comap_map_of_surjective' π Ideal.Quotient.mk_surjective m
      rw [h, Ideal.comap_top, sup_eq_left.2 hker] at this
      exact hm.ne_top this.symm
  have hcm : (m.map π).comap π = m := by
    rw [Ideal.comap_map_of_surjective' π Ideal.Quotient.mk_surjective m, sup_eq_left.2 hker]
  obtain ⟨V, F, _, _, _, _, _, _, _, _, _, y, tF, hy, hshF, hprF, hthF⟩ :=
    GlobalTheory.T.exists_thetaObject_over_complete_dvr_specialisation h1 h2 o g (n ^ j) J b Mat κ w w' R₀ K₀ β₀ (fun a => π (v a)) t₁ (m.map π) hm₀ hth₁ hsh₁ (hpr₁ w w' hpr₀)
  have hmem : ∀ a : R, y (π a) ∈ IsLocalRing.maximalIdeal V ↔ a ∈ m := fun a => by
    rw [← Ideal.mem_comap, hy, ← Ideal.mem_comap, hcm]
  have hcos : Coset n (n ^ j) (fun a => y (π (v a))) (IsLocalRing.maximalIdeal V) := fun a => by
    obtain ⟨c, hc⟩ := hMM.2 m hm.isPrime a
    exact ⟨c, fun h => hc ((hmem _).1 h)⟩

  obtain ⟨V', K', _, _, _, _, _, _, φ, ψ, t', tK, hφ, -, hK, hK', hth'⟩ :=
    crit j (le_of_max_le_left hj) o b V F (y.comp β₀) tF _ hprF hthF hcos
  have hshK : tK.Shape Mat κ :=
    (GlobalTheory.T.thetaLevel_shape_primitivity_pullback_descent o g _ J b Mat κ w w' _ _ _ _ _ tF tK hK).1 hshF
  have hsh' : t'.Shape Mat κ :=
    GlobalTheory.T.thetaLevelShape_of_generic_point h1 h2 o g _ J b Mat κ (Sp V') _ t' K' _ _ tK (range_spMap_fraction V' K') hK' hshK

  let k := AlgebraicClosure (IsLocalRing.ResidueField V')
  let r : V' →+* k := (algebraMap (IsLocalRing.ResidueField V') k).comp (IsLocalRing.residue V')
  let z : R →+* k := r.comp (φ.comp (y.comp π))
  obtain ⟨tk, hshk, hthk, -⟩ := exists_pull h2 Mat κ r (spMap z ≫ spMap (algebraMap o R))
    (by simp only [spMap_spMap]) t' _ hsh' hth'
  refine ⟨k, inferInstance, inferInstance, z, tk, ?_, hshk, hthk⟩
  ext a
  rw [RingHom.mem_ker, ← hmem]
  change algebraMap (IsLocalRing.ResidueField V') k (IsLocalRing.residue V' (φ (y (π a)))) = 0 ↔ _
  rw [map_eq_zero, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

end GlobalTheory
end

