import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0670
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0679
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseChangeCompatibleGlobalOneFormsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBaseChange_compatibleGlobalOneForms : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (T : C) (e : Glob1 F →ₗ[R] Ω[F.obj T⁄R]), (∀ w, e w = w.1 T) → IsBaseChange (F.obj T) e := by
  first | exact @GlobalTheory.AbCoh.isBaseChange_glob1 | exact GlobalTheory.AbCoh.isBaseChange_glob1 | (intros; apply GlobalTheory.AbCoh.isBaseChange_glob1 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCechOneCocyclePosetOneCochainToCechCochainStatement
section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCechOneCocycle_posetOneCochainToCechCochain : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ f : GlobalTheory.CatCoh.C1 (capF s U hU hinf), f ∈ Z1 (capF s U hU hinf) → IsCoc U (toCech s U hU hinf f) := by
  first | exact @GlobalTheory.CechCmp.isCoc_toCech | exact GlobalTheory.CechCmp.isCoc_toCech | (intros; apply GlobalTheory.CechCmp.isCoc_toCech <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCocommOfSurjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup.KerGrp

set_option autoImplicit false in
open CategoryTheory TensorProduct Coalgebra Bialgebra in

theorem _root_.GlobalTheory.PDivGroup.KerGrp.isCocomm_of_surjective {k A B : Type} [CommRing k] [CommRing A] [CommRing B]
    [Bialgebra k A] [Bialgebra k B] [IsCocomm k A] (f : A →ₐc[k] B)
    (hf : Function.Surjective f) : IsCocomm k B := by
  constructor
  ext b
  obtain ⟨a, rfl⟩ := hf b
  have hcomm : ∀ y : A ⊗[k] A, TensorProduct.comm k B B (TensorProduct.map (f : A →ₗ[k] B)
      (f : A →ₗ[k] B) y) = TensorProduct.map (f : A →ₗ[k] B) (f : A →ₗ[k] B)
      (TensorProduct.comm k A A y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  have hA : TensorProduct.comm k A A (comul a) = comul a :=
    LinearMap.congr_fun (Coalgebra.comm_comp_comul (R := k) (A := A)) a
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← CoalgHomClass.map_comp_comul_apply, hcomm, hA]

set_option autoImplicit false in
open CategoryTheory TensorProduct Coalgebra Bialgebra in

theorem _root_.GlobalTheory.PDivGroup.KerGrp.map_res_kerIdeal {p : ℕ} {k : Type} [CommRing k] {G H : _root_.GlobalTheory.PDivGroup p k} (u : G ⟶ H)
    (n : ℕ) : Ideal.map (G.res n : G.A (n + 1) →ₐ[k] G.A n) (_root_.GlobalTheory.PDiv.kerIdeal (u.app (n + 1))) =
      _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := by
  have hc := congrArg (fun g : H.A (n + 1) →ₐc[k] G.A n =>
    ((g : H.A (n + 1) →ₐ[k] G.A n) :
      H.A (n + 1) →+* G.A n))
    (_root_.GlobalTheory.PDivGroup.Hom.comm u n)
  have hres : Ideal.map (H.res n : H.A (n + 1) →ₐ[k]
      H.A n) (_root_.GlobalTheory.PDiv.augIdeal k (H.A (n + 1))) =
      _root_.GlobalTheory.PDiv.augIdeal k (H.A n) :=
    _root_.GlobalTheory.PDiv.kerIdeal_of_surjective (H.10 n)
  unfold _root_.GlobalTheory.PDiv.kerIdeal
  change Ideal.map ((G.res n : G.A (n + 1) →ₐ[k]
      G.A n) : G.A (n + 1) →+* G.A n)
      (Ideal.map ((u.app (n + 1) : H.A (n + 1) →ₐ[k]
        G.A (n + 1)) : H.A (n + 1) →+* G.A (n + 1))
        (_root_.GlobalTheory.PDiv.augIdeal k (H.A (n + 1)))) =
    Ideal.map ((u.app n : H.A n →ₐ[k] G.A n) :
      H.A n →+* G.A n)
      (_root_.GlobalTheory.PDiv.augIdeal k (H.A n))
  rw [Ideal.map_map]

  rw [show ((G.res n : G.A (n + 1) →ₐ[k] G.A n) :
      G.A (n + 1) →+* G.A n).comp
      ((u.app (n + 1) : H.A (n + 1) →ₐ[k] G.A (n + 1)) :
        H.A (n + 1) →+* G.A (n + 1)) =
      ((u.app n : H.A n →ₐ[k] G.A n) :
        H.A n →+* G.A n).comp
      ((H.res n : H.A (n + 1) →ₐ[k] H.A n) :
        H.A (n + 1) →+* H.A n) from hc, ← Ideal.map_map]
  rw [← hres]
  rfl

theorem exists_of_family {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k)
    (u : G ⟶ G) (h₀ : ℕ) (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, HopfAlgebra k (B n)]
    (π : ∀ n, G.A n →ₐc[k] B n) (hπ : ∀ n, Function.Surjective (π n))
    (hk : ∀ n, RingHom.ker (π n) = kerIdeal (u.app n))
    (h : ∀ n : ℕ, Module.finrank k (B n) = p ^ (n * h₀)) :
    ∃ (K : PDivGroup p k) (i : K ⟶ G), ∀ n : ℕ, Function.Surjective (i.app n) ∧
      RingHom.ker (i.app n) = kerIdeal (u.app n) := by
  haveI : ∀ n, IsCocomm k (B n) := fun n => isCocomm_of_surjective (π n) (hπ n)
  have hle : ∀ n, RingHom.ker (π (n + 1)) ≤ RingHom.ker ((π n).comp (G.res n)) := fun n a ha => by
    have : G.res n a ∈ RingHom.ker (π n) := by
      rw [hk, ← map_res_kerIdeal]
      rw [hk] at ha
      exact Ideal.mem_map_of_mem (G.res n : G.A (n + 1) →ₐ[k] G.A n) ha
    exact this
  let r := fun n => liftSurj (π (n + 1)) (hπ (n + 1)) ((π n).comp (G.res n)) (hle n)
  have hr : ∀ n a, r n (π (n + 1) a) = π n (G.res n a) := fun n a => liftSurj_apply ..
  let K : PDivGroup p k :=
    { height := h₀
      A := B
      finite := fun n => Module.Finite.of_surjective (π n : G.A n →ₗ[k] B n) (hπ n)
      rank_eq := fun n q => by rw [Module.rankAtStalk_eq_finrank_of_free, h]; rfl
      res := r
      res_surjective := fun n b => by
        obtain ⟨c, rfl⟩ := hπ n b
        obtain ⟨a, rfl⟩ := G.res_surjective n c
        exact ⟨_, hr n a⟩
      ker_res := fun n => by
        rw [← map_torsionIdeal (hπ (n + 1)), ← G.ker_res]
        refine le_antisymm (fun b hb => ?_) (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
        · obtain ⟨a, rfl⟩ := hπ _ b
          have h1 : G.res n a ∈ RingHom.ker (π n) := (hr n a).symm.trans hb
          rw [hk, ← map_res_kerIdeal] at h1
          obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective
            (G.res n : G.A (n + 1) →ₐ[k] G.A n) (G.res_surjective n)).1 h1
          rw [← hk] at hc
          have hc' : π (n + 1) c = 0 := hc
          have e' : G.res n c = G.res n a := e
          have h2 : a - c ∈ RingHom.ker (G.res n) := by
            rw [RingHom.mem_ker, map_sub, e', sub_self]
          have h3 : π (n + 1) a = π (n + 1) (a - c) := by rw [map_sub, hc', sub_zero]
          rw [h3]
          exact Ideal.mem_map_of_mem (π (n + 1) : G.A (n + 1) →ₐ[k] B (n + 1)) h2
        · have ha' : G.res n a = 0 := ha
          change r n (π (n + 1) a) = 0
          rw [hr, ha', map_zero] }
  exact ⟨K, ⟨π, fun n => BialgHom.ext fun a => hr n a⟩, fun n => ⟨hπ n, hk n⟩⟩

set_option autoImplicit false in
open CategoryTheory TensorProduct Coalgebra Bialgebra in

theorem _root_.GlobalTheory.PDivGroup.KerGrp.exists_kernel (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : _root_.GlobalTheory.PDivGroup p k)
    (u : G ⟶ G) (h₀ : ℕ)
    (h : ∀ n : ℕ, Module.finrank k (G.A n ⧸ _root_.GlobalTheory.PDiv.kerIdeal (u.app n)) = p ^ (n * h₀)) :
    ∃ (K : _root_.GlobalTheory.PDivGroup p k) (i : K ⟶ G), ∀ n : ℕ, Function.Surjective (i.app n) ∧
      RingHom.ker (i.app n) = _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := by
  classical
  obtain ⟨I, hIdef⟩ : ∃ I : ∀ n, Ideal (G.A n),
      ∀ n, I n = _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := ⟨_, fun n => rfl⟩
  haveI hH : ∀ n, (I n).IsHopfIdeal k := fun n => by
    rw [hIdef]
    exact _root_.GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom k _ _ (u.app n)
  have hq : ∀ n, Function.Surjective (Bialgebra.Quotient.mkBialgHom (R := k) (I n)) := by
    intro n x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, by simp⟩
  haveI hcoc : ∀ n, IsCocomm k (G.A n ⧸ I n) := fun n =>
    _root_.GlobalTheory.PDivGroup.KerGrp.isCocomm_of_surjective _ (hq n)
  have hmapI : ∀ n, Ideal.map (G.res n : G.A (n + 1) →ₐ[k]
      G.A n) (I (n + 1)) = I n := by
    intro n
    rw [hIdef, hIdef]
    exact _root_.GlobalTheory.PDivGroup.KerGrp.map_res_kerIdeal u n
  have hle : ∀ n, I (n + 1) ≤ (I n).comap (G.res n :
      G.A (n + 1) →ₐ[k] G.A n) := fun n =>
    Ideal.map_le_iff_le_comap.1 (hmapI n).le
  let φ : ∀ n, (G.A (n + 1) ⧸ I (n + 1)) →ₐ[k] (G.A n ⧸ I n) :=
    fun n => Ideal.quotientMapₐ (I n) (G.res n :
      G.A (n + 1) →ₐ[k] G.A n) (hle n)
  have hφ : ∀ n a, φ n (Ideal.Quotient.mk (I (n + 1)) a) =
      Ideal.Quotient.mk (I n) (G.res n a) := fun n a => rfl
  have hcounit : ∀ n, (Bialgebra.counitAlgHom k _).comp (φ n) =
      Bialgebra.counitAlgHom k (G.A (n + 1) ⧸ I (n + 1)) := by
    intro n
    refine AlgHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change CoalgebraStruct.counit (R := k) (Ideal.Quotient.mk (I n) (G.res n a)) =
      CoalgebraStruct.counit (R := k) (Ideal.Quotient.mk (I (n + 1)) a)
    rw [← Bialgebra.Quotient.mkBialgHom_apply (R := k), ← Bialgebra.Quotient.mkBialgHom_apply (R := k),
      CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply,
      CoalgHomClass.counit_comp_apply]
  have hcomul : ∀ n, (Algebra.TensorProduct.map (φ n) (φ n)).comp (Bialgebra.comulAlgHom k _) =
      (Bialgebra.comulAlgHom k _).comp (φ n) := by
    intro n
    refine AlgHom.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Algebra.TensorProduct.map (φ n) (φ n)
        (CoalgebraStruct.comul (R := k) (Ideal.Quotient.mk (I (n + 1)) a)) =
      CoalgebraStruct.comul (R := k) (Ideal.Quotient.mk (I n) (G.res n a))
    rw [← Bialgebra.Quotient.mkBialgHom_apply (R := k) (I (n + 1)),
      ← Bialgebra.Quotient.mkBialgHom_apply (R := k) (I n),
      ← CoalgHomClass.map_comp_comul_apply (Bialgebra.Quotient.mkBialgHom (R := k) (I (n + 1))),
      ← CoalgHomClass.map_comp_comul_apply (Bialgebra.Quotient.mkBialgHom (R := k) (I n)),
      ← CoalgHomClass.map_comp_comul_apply (G.res n)]
    generalize CoalgebraStruct.comul (R := k) a = y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hφ]
    | add x y hx hy => simp only [map_add, hx, hy]
  let r : ∀ n, (G.A (n + 1) ⧸ I (n + 1)) →ₐc[k] (G.A n ⧸ I n) :=
    fun n => BialgHom.ofAlgHom (φ n) (hcounit n) (hcomul n)
  have hr : ∀ n a, r n (Ideal.Quotient.mk (I (n + 1)) a) =
      Ideal.Quotient.mk (I n) (G.res n a) := fun n a => rfl
  have hrs : ∀ n, Function.Surjective (r n) := by
    intro n x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := G.10 n a
    exact ⟨Ideal.Quotient.mk _ b, hr n b⟩
  have hker : ∀ n, RingHom.ker (r n) =
      _root_.GlobalTheory.PDiv.torsionIdeal k (G.A (n + 1) ⧸ I (n + 1)) (p ^ n) := by
    intro n
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, hr, Ideal.Quotient.eq_zero_iff_mem,
      ← _root_.GlobalTheory.PDiv.map_torsionIdeal (hq (n + 1))]
    change _ ↔ Ideal.Quotient.mk (I (n + 1)) a ∈ Ideal.map (Ideal.Quotient.mk (I (n + 1))) _
    rw [Ideal.mem_quotient_iff_mem_sup, ← G.ker_res n]
    change a ∈ Ideal.comap (G.res n : G.A (n + 1) →ₐ[k]
      G.A n) (I n) ↔ _
    rw [← hmapI n, Ideal.comap_map_of_surjective (G.res n :
      G.A (n + 1) →ₐ[k] G.A n) (G.10 n),
      ← RingHom.ker_eq_comap_bot, sup_comm]
    all_goals rfl
  have hkq : ∀ n, RingHom.ker (Bialgebra.Quotient.mkBialgHom (R := k) (I n)) =
      _root_.GlobalTheory.PDiv.kerIdeal (u.app n) := by
    intro n
    rw [← hIdef]
    ext x
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨_root_.GlobalTheory.PDivGroup.mk h₀ (fun n => G.A n ⧸ I n)
    (commRing := fun n => inferInstance) (hopf := fun n => inferInstance) (cocomm := hcoc)
    (finite := fun n => Module.Finite.of_surjective (Ideal.Quotient.mkₐ k (I n)).toLinearMap
      Ideal.Quotient.mk_surjective)
    (projective := fun n => inferInstance) (fun n q => ?_) r hrs hker,
    _root_.GlobalTheory.PDivGroup.Hom.mk (fun n => Bialgebra.Quotient.mkBialgHom (R := k) (I n))
      (fun n => ?_), fun n => ⟨hq n, ?_⟩⟩
  · rw [Module.rankAtStalk_eq_finrank_of_free]
    have hn := h n
    rw [← hIdef] at hn
    simpa using hn
  · exact DFunLike.ext _ _ fun a => rfl
  · exact hkq n

end GlobalTheory.PDivGroup.KerGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCommFormalGroupLawMapNatMultipleStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCommFormalGroupLaw_map_natMultiple : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (S : Type) [CommRing S] (r : R →+* S), IsLaw (fun i => map r (μ i)) ∧ ∀ n i, constantCoeff (nmul μ n i) = 0 ∧ map r (nmul μ n i) = nmul (fun i => map r (μ i)) n i := by
  first | exact @GlobalTheory.isLaw_map_nmul | exact GlobalTheory.isLaw_map_nmul | (intros; apply GlobalTheory.isLaw_map_nmul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevIffIsEtLevOverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtLev_iff_isEtLevOver' : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S T : Scheme.{0}) (s : S ⟶ Sp R) (t : T ⟶ S) (s₁ : T ⟶ Sp R) (o : Obj b N s) (o₁ : Obj b N s₁) (m : ObjMap o₁ o t) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (l : D.La → (𝟙_ (Over T) ⟶ o₁.A)), IsEtLev o₁ w0 r l ↔ IsEtLevOver o w0 r (T := Over.mk t) (fun y => ptOf m (l y)) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.isEtLev_iff_isEtLevOver) | (exact GlobalTheory.UPel.HT.EtLev.isEtLev_iff_isEtLevOver) | (intros; apply GlobalTheory.UPel.HT.EtLev.isEtLev_iff_isEtLevOver  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesSectionQuotientsStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCoordinates_section_quotients : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (B : La) (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (U : Set Y), A.IsSec B t0 → (∀ j, A.IsSec B (t j)) → IsOpen U → (∀ y ∈ U, t0 (A.pick y) y ≠ 0 ∧ A.IsCoordAt t0 t y) → Etale A U (A.zmap t0 t) := by
  first | exact @GlobalTheory.OTY.etale_zmap_main | exact GlobalTheory.OTY.etale_zmap_main | (intros; apply GlobalTheory.OTY.etale_zmap_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHausdorffOfProjective
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CEval

theorem eq_zero_of_projective {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    [Module.Projective O M] (p : ℕ) [IsHausdorff (Ideal.span {(p : O)}) O] (y : M)
    (h : ∀ m : ℕ, ∃ z : M, y = ((p : O) ^ m) • z) : y = 0 := by
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O M)
  have h0 : s y = 0 := by
    ext i
    refine eq_of_forall_dvd p fun m => ?_
    obtain ⟨z, hz⟩ := h m
    rw [hz, map_smul, Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply, sub_zero]
    exact dvd_mul_right _ _
  have := LinearMap.congr_fun hs y
  rw [LinearMap.comp_apply, h0, map_zero, LinearMap.id_apply] at this
  exact this.symm

theorem isHausdorff_of_projective {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    [Module.Projective O A] (p : ℕ) [IsHausdorff (Ideal.span {(p : O)}) O] :
    IsHausdorff (Ideal.span {(p : A)}) A := by
  refine ⟨fun y hy => eq_zero_of_projective (O := O) p y fun m => ?_⟩
  have := dvd_of_smodEq p m (hy m)
  rw [sub_zero] at this
  obtain ⟨z, hz⟩ := this
  refine ⟨z, ?_⟩
  rw [hz, Algebra.smul_def, map_pow, map_natCast]

theorem isEval_comp {σ R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A]
    [Algebra R A'] (p : ℕ) {x : σ → A} {E : MvPowerSeries σ R →ₐ[R] A} (h : IsEval p x E)
    (g : A →ₐ[R] A') : IsEval p (fun i => g (x i)) (g.comp E) := by
  refine ⟨fun i => by rw [AlgHom.comp_apply, h.1], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd g (hN f hf)
  rwa [map_pow, map_natCast] at this

theorem eval_subst {σ τ R A : Type} [Fintype σ] [Fintype τ] [CommRing R] [CommRing A]
    [Algebra R A] (p : ℕ) [IsHausdorff (Ideal.span {(p : A)}) A] {x : σ → A}
    {E : MvPowerSeries σ R →ₐ[R] A} (hE : IsEval p x E) (u : τ → MvPowerSeries σ R)
    (E' : MvPowerSeries τ R →ₐ[R] A) (hu : ∀ j, constantCoeff (u j) = 0)
    (hE' : IsEval p (fun j => E (u j)) E') (f : MvPowerSeries τ R) : E (subst u f) = E' f := by
  have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
  rw [← coe_substAlgHom hs]
  exact ext_of_cont p ((E.comp (substAlgHom hs)).toRingHom) E'.toRingHom
    (fun c => by
      show E (substAlgHom hs (C c)) = E' (C c)
      rw [c_eq_algebraMap, AlgHom.commutes, AlgHom.commutes, AlgHom.commutes])
    (fun j => by
      show E (substAlgHom hs (X j)) = E' (X j)
      rw [substAlgHom_X, hE'.1])
    (fun m => by
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      show (p : A) ^ m ∣ E (substAlgHom hs f)
      rw [coe_substAlgHom]
      refine hN _ fun α hα => coeff_of_lt_order ?_
      have h1 : (1 : ℕ∞) ≤ ⨅ j, (u j).order :=
        le_iInf fun j => one_le_order_iff_constCoeff_eq_zero.2 (hu j)
      have h2 : (N : ℕ∞) ≤ f.order := nat_le_order hf
      calc (α.degree : ℕ∞) < N := by exact_mod_cast hα
        _ = 1 * N := (one_mul _).symm
        _ ≤ (⨅ j, (u j).order) * f.order := mul_le_mul' h1 h2
        _ ≤ (subst u f).order := le_order_subst hs f)
    hE'.2 f

end GlobalTheory.CEval

namespace GlobalTheory.QLog.Chart

open GlobalTheory.CEval

variable {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
  {G : PDivGroup p O} {d : ℕ} (c : Chart G d)

omit c in
theorem isHausdorff₂ (G : PDivGroup p O) (n : ℕ) :
    IsHausdorff (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
  isHausdorff_of_projective (O := O) p

theorem ev₂_subst_μ (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (subst c.μ s) = Coalgebra.comul (R := O) (c.ev n s) := by
  haveI := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Bialgebra.comulAlgHom O (G.A n))
  rw [eval_subst p (c.isEval₂ n) c.μ ((Bialgebra.comulAlgHom O (G.A n)).comp (c.ev n))
    c.isLaw.const ?_ s]
  · rfl
  convert h using 2 with j
  rw [c.comul n j]
  rfl

theorem ev₂_inL (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inL s) = c.ev n s ⊗ₜ[O] (1 : G.A n) := by
  haveI := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Algebra.TensorProduct.includeLeft (R := O) (S := O)
    (A := G.A n) (B := G.A n))
  rw [inL, eval_subst p (c.isEval₂ n) (fun i => X (Sum.inl i))
    ((Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)).comp (c.ev n))
    (fun _ => constantCoeff_X _) ?_ s]
  · rfl
  exact ⟨fun j => (h.1 j).trans ((c.isEval₂ n).1 (Sum.inl j)).symm, h.2⟩

theorem ev₂_inR (n : ℕ) (s : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inR s) = (1 : G.A n) ⊗ₜ[O] c.ev n s := by
  haveI := isHausdorff₂ G n
  have h := isEval_comp p (c.isEval n) (Algebra.TensorProduct.includeRight (R := O)
    (A := G.A n) (B := G.A n))
  rw [inR, eval_subst p (c.isEval₂ n) (fun i => X (Sum.inr i))
    ((Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)).comp (c.ev n))
    (fun _ => constantCoeff_X _) ?_ s]
  · rfl
  convert h using 2 with j
  rw [(c.isEval₂ n).1]
  rfl

end GlobalTheory.QLog.Chart

namespace GlobalTheory.QLog.Chart

theorem comul_ev : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), Coalgebra.comul (R := O) (c.ev n s) = c.ev n s ⊗ₜ[O] (1 : G.A n) + (1 : G.A n) ⊗ₜ[O] c.ev n s + c.ev₂ n (cob1 c.μ s) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n s
  rw [cob1, map_sub, map_sub, c.ev₂_subst_μ, c.ev₂_inL, c.ev₂_inR]
  abel

end GlobalTheory.QLog.Chart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionDifferenceStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_weierstrassP_torsion_difference : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ → ∀ x y : Fin 2 → ZMod N, x ≠ 0 → y ≠ 0 → IsIntegral ℤ ((N : ℂ) ^ 2 * (wp N x τ - wp N y τ) / ω ^ 2) := by
  first | exact @GlobalTheory.WpFam.isIntegral_sq_mul_wp_sub_div | exact GlobalTheory.WpFam.isIntegral_sq_mul_wp_sub_div | (intros; apply GlobalTheory.WpFam.isIntegral_sq_mul_wp_sub_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionIntegralJStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_weierstrassP_torsion_integral_j : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ → ∀ x : Fin 2 → ZMod N, IsIntegral ℤ (12 * (N : ℂ) ^ 2 * wp N x τ / ω ^ 2) ∧ IsIntegral ℤ ((N : ℂ) ^ 3 * wpd N x τ / ω ^ 3) := by
  first | exact @GlobalTheory.WpInt.main | exact GlobalTheory.WpInt.main | (intros; apply GlobalTheory.WpInt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentBlockFrobeniusXiAinfOfFrameBlockP
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem isNil_V_blk_frob_xi :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), (∀ i j, F.τ ∣ U i j - F.a (V i j)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → IsNil (WittVector.fontaineTheta O p) WittVector.frobenius (V * blk d k (WittVector.frobenius (xi ε)) 1) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k U V hUV hnil
  haveI : IsLocalRing O := ReciprocityTheory.PGsh.Ainf.O_local O hv
  apply isNil_of_map F.a (WittVector.fontaineTheta O p) F.θ WittVector.frobenius F.σ F.θ_a F.σ_a
  refine isNil_of_theta_eq p F.θ F.σ (Fact.out) F.σ_pow _ _ ?_ hnil
  intro i j
  have hU : F.θ (U i j) = F.θ (F.a (V i j)) := by
    obtain ⟨c, hc⟩ := hUV i j
    have h := congrArg F.θ hc
    rw [map_sub, map_mul, theta_tau F hv hε, zero_mul, sub_eq_zero] at h
    exact h
  simp only [blk, Matrix.mul_diagonal, Matrix.map_apply]
  rcases j with j | j
  · simp only [Sum.elim_inl, map_mul, map_natCast, hU, F.θ_a, theta_frob_xi hv hε]
  · simp only [Sum.elim_inr, map_mul, map_one, mul_one, hU]

end GlobalTheory.WinLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentDualFrobeniusOfBlockStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_dualFrobenius_of_block : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O) (σ : B →+* B) (p : ℕ) (m : Ideal O), θ (p : B) ∈ m → m ≠ ⊤ → (∀ b, ∃ c, σ b - b ^ p = p * c) → ∀ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) B) (c : Fin d → Fin d → B), (∀ a j, ∃ b, c a j - U⁻¹ (Sum.inl j) (Sum.inl a) = p * b) → (∃ N : ℕ, ∀ w : Fin d → O ⧸ m, (fun w : Fin d → O ⧸ m => fun a => ∑ j, Ideal.Quotient.mk m (θ (c a j)) * w j ^ p)^[N] w = 0) → IsNil θ σ (U.transpose⁻¹ * blk d k 1 (p : B)) := by
  first | exact @GlobalTheory.DualFrobNilMat.isNil_of_block | exact GlobalTheory.DualFrobNilMat.isNil_of_block | (intros; apply GlobalTheory.DualFrobNilMat.isNil_of_block <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenAtlasSectionNonvanishingSetAndMemIffStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_atlasSectionNonvanishingSet_and_mem_iff : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → IsOpen (nz A τ) ∧ ∀ i y, y ∈ (A.chart i).source → (y ∈ nz A τ ↔ τ i y ≠ 0) := by
  first | exact @GlobalTheory.OTY.isOpen_nz_and_mem_nz_iff | exact GlobalTheory.OTY.isOpen_nz_and_mem_nz_iff | (intros; apply GlobalTheory.OTY.isOpen_nz_and_mem_nz_iff <;> assumption)
end

