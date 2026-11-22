import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0063
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0076
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.Bundle0018
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.MulGenNegRight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0077
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HilbertSchurUnitaryIrreducibleScalar
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.LocalRingCardinality.DataLevel

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveBcrisToBdR
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_injective_lift_field {R S K : Type} [CommRing R] [CommRing S] [CommRing K] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (hK : IsField K) (g : R →+* K) (hg : Function.Injective g)
    (hM : ∀ y ∈ M, y ≠ 0) :
    ∃ ι : S →+* K, (∀ x : R, ι (algebraMap R S x) = g x) ∧ Function.Injective ι := by
  have hu : ∀ y : M, IsUnit (g y) := by
    intro y
    have h : g y ≠ 0 := fun h => hM y y.2 (hg (by rw [h, map_zero]))
    obtain ⟨b, hb⟩ := hK.mul_inv_cancel h
    exact IsUnit.of_mul_eq_one b hb
  refine ⟨IsLocalization.lift hu, fun x => IsLocalization.lift_eq hu x, ?_⟩
  rw [IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    rw [← IsLocalization.lift_eq (S := S) hu x, h, IsLocalization.lift_eq]
  · intro h
    rw [hg h]

theorem algebraMap_ainf_acris_eq {l : ℕ} [Fact l.Prime] (x : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) x =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) :=
  GlobalTheory.RingIface.tower l x

theorem algebraMap_ainf_acris_ne_zero_pt {l : ℕ} [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l)
    (hj : IsCrisP j) (x : Per.Ainf l) (hx0 : x ≠ 0) : algebraMap (Per.Ainf l) (Per.Acris l) x ≠ 0 := by
  obtain ⟨hd, -, hi⟩ := GlobalTheory.T.usage l
  intro h'
  apply hx0
  have h1 := hj.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)
  rw [← algebraMap_ainf_acris_eq] at h1
  rw [h', map_zero] at h1
  have h2 : ((algebraMap (Per.Ainf l) (Per.Acris0 l) x : Per.Acris0 l) : Per.AinfP l) = 0 :=
    GlobalTheory.T.algebraMap_ainfInvPrime_bdRPlus_injective l (by rw [map_zero]; exact h1.symm)
  exact hi (by rw [map_zero]; exact h2)

theorem pow_root_ne_zero {l : ℕ} [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l) (hj : IsCrisP j)
    (e : Per.Fl l) (hne : e ≠ 1) (n : ℕ) :
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1) ^ n ≠ 0 := by
  obtain ⟨hd, -, -⟩ := GlobalTheory.T.usage l
  rw [← map_pow]
  refine algebraMap_ainf_acris_ne_zero_pt j hj _ (pow_ne_zero n fun h => ?_)
  exact GlobalTheory.CrisLoc.constantCoeff_root_ne_zero l e hne (by rw [h, map_zero])

theorem exists_iota_cris_dR : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j →
    ∃ ι : Per.Bcris l →+* Per.BdR l, (∀ x : Per.Acris l, ι (algebraMap (Per.Acris l) (Per.Bcris l) x) =
      algebraMap (Per.BdRp l) (Per.BdR l) (j x)) ∧ Function.Injective ι := by
  intro l _ j hj
  obtain ⟨-, hi, hK, -⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  haveI := GlobalTheory.CrisLoc.bcris_away l e he hne
  refine exists_injective_lift_field
    (Submonoid.powers (algebraMap (Per.Ainf l) (Per.Acris l) (Per.tm e - 1))) hK
    ((algebraMap (Per.BdRp l) (Per.BdR l)).comp j) (hi.comp (GlobalTheory.T.acrisToBdRPlus_injective l j hj)) ?_
  rintro _ ⟨n, rfl⟩
  exact pow_root_ne_zero j hj e hne n

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsJointHighestWeightLeadingMinorProductStatement
section
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jointHighestWeight_leadingMinorProduct : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → ∃ Δ : MvPolynomial (Fin N × Fin n) ℂ, Δ ≠ 0 ∧ (∀ h g, ReciprocityTheory.PGsh.IsUpperUnitri h → ReciprocityTheory.PGsh.IsUpperUnitri g → subst2 h g Δ = Δ) ∧ ∀ (d : Fin N → ℂ) (e : Fin n → ℂ), subst2 (Matrix.diagonal d) (Matrix.diagonal e) Δ = ((∏ b, d b ^ ν b) * ∏ a, e a ^ ν (Fin.castLE hn a)) • Δ := by
  first | exact @GlobalTheory.CompactHowe.Minors.exists_highestWeight | exact GlobalTheory.CompactHowe.Minors.exists_highestWeight | (intros; apply GlobalTheory.CompactHowe.Minors.exists_highestWeight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLaws
section
noncomputable section

namespace GlobalTheory.LamBiext

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

section Nest

variable {X W Y Z : Scheme.{0}} (L : LB X) {I K : Type} [Fintype I] [Fintype K]
  (φ : I → (W ⟶ X)) (δ : I → ℤ) (ψ : K → (Y ⟶ W)) (ε : K → ℤ)

abbrev flatφ : K × I → (Y ⟶ X) := fun p => ψ p.1 ≫ φ p.2

abbrev flatε : K × I → ℤ := fun p => ε p.1 * δ p.2

theorem nest_le (j : K → I → L.ι) :
    LB.wchart (LB.LinComb L φ δ) ψ j ≤ LB.wchart L (flatφ φ ψ) (fun p => j p.1 p.2) :=
  fun _ hy => Set.mem_iInter.2 fun p => Set.mem_iInter.1 (Set.mem_iInter.1 hy p.1) p.2

def nest (t : LB.Gen (LB.LinComb L (flatφ φ ψ) (flatε δ ε))) :
    LB.Gen (LB.LinComb (LB.LinComb L φ δ) ψ ε) :=
  ⟨fun j => res (nest_le L φ δ ψ j) (t.s fun p => j p.1 p.2)⟩

theorem trF_flat (r : Z ⟶ Y) (z : Z) (j j' : K → I → L.ι) :
    trF (L := L) (flatφ φ ψ) (flatε δ ε) r z (fun p => j p.1 p.2) (fun p => j' p.1 p.2) =
      ∏ k, trF (L := L) φ δ (r ≫ ψ k) z (j k) (j' k) ^ ε k := by
  rw [trF, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [trF, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  show gm (r ≫ ψ k ≫ φ i) z _ (L.g (j k i) (j' k i)) ^ (ε k * δ i) = _
  rw [mul_comm (ε k), zpow_mul, Category.assoc]

variable {L φ δ ψ ε}

theorem nest_isGen {t : LB.Gen (LB.LinComb L (flatφ φ ψ) (flatε δ ε))} (ht : t.IsGen) :
    (nest L φ δ ψ ε t).IsGen := fun j j' => unit_ext fun y hy => by
  have hj : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart (LB.LinComb L φ δ) ψ j := hy.1
  have hj' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart (LB.LinComb L φ δ) ψ j' := hy.2
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hj _).trans ?_)
  refine (gen_trans ht (𝟙 Y) y (nest_le L φ δ ψ j hj) (nest_le L φ δ ψ j' hj')).trans ?_
  refine Eq.trans ?_ (map_mul _ _ _).symm
  refine congrArg₂ (· * ·) ?_ ((gm_res _ y _ hj' _).symm.trans (gm_res _ y _ hy _).symm)
  refine (trF_flat L φ δ ψ ε (𝟙 Y) y j j').trans (Eq.symm ?_)
  refine (gm_linComb _ ψ ε (𝟙 Y) y j j' hj hj').trans (Finset.prod_congr rfl fun k _ => ?_)
  exact congrArg (· ^ ε k) (gm_linComb L φ δ (𝟙 Y ≫ ψ k) y (j k) (j' k) (Set.mem_iInter.1 hj k)
    (Set.mem_iInter.1 hj' k))

def adj (φ : I → (W ⟶ X)) (δ : I → ℤ) (z : Z) (JP : (Z ⟶ W) → I → L.ι) (J : (Z ⟶ X) → L.ι) (χ : Z ⟶ W) :
    (Z.presheaf.stalk z)ˣ :=
  trF (L := L) φ δ χ z (JP χ) (fun i => J (χ ≫ φ i))

theorem val_nest {t : LB.Gen (LB.LinComb L (flatφ φ ψ) (flatε δ ε))} (ht : t.IsGen) (r : Z ⟶ Y) {z : Z}
    {JP : (Z ⟶ W) → I → L.ι} (hJP : Good (LB.LinComb L φ δ) z JP) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (L := LB.LinComb L φ δ) (nest L φ δ ψ ε t) r z JP =
      (∏ k, adj φ δ z JP J (r ≫ ψ k) ^ ε k) * val (L := L) t r z J := by
  have hm := hJP.mem ψ r
  have e₁ : val (L := LB.LinComb L φ δ) (nest L φ δ ψ ε t) r z JP =
      gm r z (LB.wchart L (flatφ φ ψ) fun p => JP (r ≫ ψ p.1) p.2) (t.s fun p => JP (r ≫ ψ p.1) p.2) :=
    gm_res r z _ hm _
  have e₂ := val_of t r z J (fun p => J ((r ≫ ψ p.1) ≫ φ p.2)) (fun p => by rw [Category.assoc])
  have m₂ : r z ∈ LB.wchart L (flatφ φ ψ) (fun p => J ((r ≫ ψ p.1) ≫ φ p.2)) := by
    have := hJ.mem (flatφ φ ψ) r
    simpa only [Category.assoc] using this
  rw [e₂]
  refine e₁.trans ((gen_trans ht r z (nest_le L φ δ ψ _ hm) m₂).trans ?_)
  exact congrArg (· * _) (trF_flat L φ δ ψ ε r z (fun k => JP (r ≫ ψ k)) (fun k i => J ((r ≫ ψ k) ≫ φ i)))

end Nest

section Group

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

variable (G) in

abbrev lamφ : ULift.{0} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) := fun I => (psum G (x2 G) I.down).left

abbrev lamε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem prod_lam {T : Over S} (x y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ I, h ((lift x y).left ≫ lamφ G I) ^ lamε I =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  have e : ∀ I : ULift.{0} (Finset (Fin 2)), (lift x y).left ≫ lamφ G I = (psum G ![x, y] I.down).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 G) I.down).trans
      (congrArg (fun q => psum G q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum G ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    (fun I => congrArg (fun q => h q ^ lamε I) (e I))).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₃ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [p₀, p₁, p₂, p₃]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem prod_law₁ {T : Over S} (a b c : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G2 G).left) → U) :
    ∏ k, h ((lift a (lift b c)).left ≫ law1φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (lift (a * b) c).left * (h (lift a c).left)⁻¹ * (h (lift b c).left)⁻¹ := by
  have r₀ : lift a (lift b c) ≫ x3 G 0 = a := by simp [x3]
  have r₁ : lift a (lift b c) ≫ x3 G 1 = b := by simp [x3]
  have r₂ : lift a (lift b c) ≫ x3 G 2 = c := by simp [x3]
  have s : lift a (lift b c) ≫ padd G (x3 G 0) (x3 G 1) = a * b := (MonObj.comp_mul _ _ _).trans (by rw [r₀, r₁])
  refine (Fintype.prod_equiv Equiv.ulift _ (fun i : Fin 3 => h ((lift a (lift b c)).left ≫
    law1φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift a (lift b c) ≫ lift (padd G (x3 G 0) (x3 G 1)) (x3 G 2)).left ^ (1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 G 1) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, s, r₀, r₁, r₂]
  simp only [zpow_neg, zpow_one]

theorem prod_law₂ {T : Over S} (a b c : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ (G2 G).left) → U) :
    ∏ k, h ((lift a (lift b c)).left ≫ law2φ G (x3 G 0) (x3 G 1) (x3 G 2) k) ^ lawε k =
      h (lift a (b * c)).left * (h (lift a b).left)⁻¹ * (h (lift a c).left)⁻¹ := by
  have r₀ : lift a (lift b c) ≫ x3 G 0 = a := by simp [x3]
  have r₁ : lift a (lift b c) ≫ x3 G 1 = b := by simp [x3]
  have r₂ : lift a (lift b c) ≫ x3 G 2 = c := by simp [x3]
  have s : lift a (lift b c) ≫ padd G (x3 G 1) (x3 G 2) = b * c := (MonObj.comp_mul _ _ _).trans (by rw [r₁, r₂])
  refine (Fintype.prod_equiv Equiv.ulift _ (fun i : Fin 3 => h ((lift a (lift b c)).left ≫
    law2φ G (x3 G 0) (x3 G 1) (x3 G 2) ⟨i⟩) ^ lawε ⟨i⟩) (fun _ => rfl)).trans ?_
  rw [Fin.prod_univ_three]
  show h (lift a (lift b c) ≫ lift (x3 G 0) (padd G (x3 G 1) (x3 G 2))).left ^ (1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 G 0) (x3 G 1)).left ^ (-1 : ℤ) *
    h (lift a (lift b c) ≫ lift (x3 G 0) (x3 G 2)).left ^ (-1 : ℤ) = _
  rw [comp_lift, comp_lift, comp_lift, s, r₀, r₁, r₂]
  simp only [zpow_neg, zpow_one]

theorem id₃ : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 (G3 G) := by
  ext <;> simp [x3]

theorem prod_flat {Y W X : Scheme.{0}} {K I : Type} [Fintype K] [Fintype I] (ψ : K → (Y ⟶ W)) (ε : K → ℤ)
    (φ : I → (W ⟶ X)) (δ : I → ℤ) {U : Type} [CommGroup U] (h : (Y ⟶ X) → U) :
    ∏ p, h (flatφ φ ψ p) ^ flatε δ ε p = ∏ k, (∏ i, h (ψ k ≫ φ i) ^ δ i) ^ ε k := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  show h (ψ k ≫ φ i) ^ (ε k * δ i) = _
  rw [mul_comm (ε k), zpow_mul]

theorem formEq₁ : FormEq (thφ G (x3 G)) thε
    (flatφ (lamφ G) (law1φ G (x3 G 0) (x3 G 1) (x3 G 2))) (flatε lamε lawε) := fun U _ h => by
  have a := prod_cub (x3 G 0) (x3 G 1) (x3 G 2) h
  rw [id₃] at a
  simp only [Over.id_left, Category.id_comp] at a
  have b := prod_law₁ (x3 G 0) (x3 G 1) (x3 G 2) (fun χ => ∏ i, h (χ ≫ lamφ G i) ^ lamε i)
  rw [id₃] at b
  simp only [Over.id_left, Category.id_comp, prod_lam] at b
  rw [a, prod_flat, b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem formEq₂ : FormEq (thφ G (x3 G)) thε
    (flatφ (lamφ G) (law2φ G (x3 G 0) (x3 G 1) (x3 G 2))) (flatε lamε lawε) := fun U _ h => by
  have a := prod_cub (x3 G 0) (x3 G 1) (x3 G 2) h
  rw [id₃] at a
  simp only [Over.id_left, Category.id_comp] at a
  have b := prod_law₂ (x3 G 0) (x3 G 1) (x3 G 2) (fun χ => ∏ i, h (χ ≫ lamφ G i) ^ lamε i)
  rw [id₃] at b
  simp only [Over.id_left, Category.id_comp, prod_lam] at b
  rw [a, prod_flat, b, _root_.mul_assoc (x3 G 0)]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

abbrev lamLB (L : RigLB G) : LB (G2 G).left := LB.LinComb L.L (lamφ G) lamε

theorem nest_isCube (L : RigLB G) (c : CubicalStr G L) (ψ : ULift.{0} (Fin 3) → ((G3 G).left ⟶ (G2 G).left))
    (t : LB.Gen (LB.LinComb L.L (flatφ (lamφ G) ψ) (flatε lamε lawε)))
    (v : LB.Gen.Corr L.L _ _ (thφ G (x3 G)) thε t c.t) :
    GlobalTheory.BiextSignTwist.LawIsCube G L c ψ (nest L.L (lamφ G) lamε ψ lawε t) := fun J j h₁ h₂ h₃ =>
  unit_ext fun y hy => by
    have e := v (fun p => J p.1 p.2) j (fun a b q => h₁ _ _ _ _ q) h₂ (fun a b q => h₃ _ _ _ q)
    have hm := nest_le L.L (lamφ G) lamε ψ J hy.1
    have hy' : (𝟙 _ : (G3 G).left ⟶ _) y ∈ LB.wchart L.L (flatφ (lamφ G) ψ) (fun p => J p.1 p.2) ⊓
        LB.wchart L.L (thφ G (x3 G)) j := ⟨hm, hy.2⟩
    refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans ?_)
    refine Eq.trans ?_ (gm_res _ y _ hy _).symm
    exact (gm_res _ y _ hy' _).symm.trans ((congrArg (gm _ y _) e).trans (gm_res _ y _ hy' _))

theorem exists_laws (L : RigLB G) (c : CubicalStr G L) :
    ∃ (l₁ : LB.Gen (LB.LinComb (lamLB L) (law1φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε))
      (l₂ : LB.Gen (LB.LinComb (lamLB L) (law2φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε)), l₁.IsGen ∧ l₂.IsGen ∧
      GlobalTheory.BiextSignTwist.LawIsCube G L c _ l₁ ∧ GlobalTheory.BiextSignTwist.LawIsCube G L c _ l₂ ∧
      ∀ {T : Over S} (y : T.left) (JP : (T.left ⟶ (G2 G).left) → ULift.{0} (Finset (Fin 2)) → L.L.ι)
        (_ : Good (lamLB L) y JP) (J : (T.left ⟶ G.left) → L.L.ι) (_ : Good L.L y J),
        (∀ a b d : T ⟶ G, val (L := lamLB L) l₁ (lift a (lift b d)).left y JP =
          adj (lamφ G) lamε y JP J (lift (a * b) d).left * (adj (lamφ G) lamε y JP J (lift a d).left)⁻¹ *
            (adj (lamφ G) lamε y JP J (lift b d).left)⁻¹ * cubV c y J a b d) ∧
        (∀ a b d : T ⟶ G, val (L := lamLB L) l₂ (lift a (lift b d)).left y JP =
          adj (lamφ G) lamε y JP J (lift a (b * d)).left * (adj (lamφ G) lamε y JP J (lift a b).left)⁻¹ *
            (adj (lamφ G) lamε y JP J (lift a d).left)⁻¹ * cubV c y J a b d) := by
  obtain ⟨t₁, g₁, v₁⟩ := exists_gen L.isLB (φ := thφ G (x3 G)) (ε := thε) formEq₁ c.t c.isGen
  obtain ⟨t₂, g₂, v₂⟩ := exists_gen L.isLB (φ := thφ G (x3 G)) (ε := thε) formEq₂ c.t c.isGen
  refine ⟨nest L.L _ _ _ _ t₁, nest L.L _ _ _ _ t₂, nest_isGen g₁, nest_isGen g₂,
    nest_isCube L c _ t₁ (corr_of_val L.isLB fun y J hJ => v₁ _ _ y J hJ),
    nest_isCube L c _ t₂ (corr_of_val L.isLB fun y J hJ => v₂ _ _ y J hJ),
    fun y JP hJP J hJ => ⟨fun a b d => ?_, fun a b d => ?_⟩⟩
  · rw [val_nest g₁ _ hJP hJ, prod_law₁ a b d (adj (lamφ G) lamε y JP J), v₁ _ _ y J hJ]
    rfl
  · rw [val_nest g₂ _ hJP hJ, prod_law₂ a b d (adj (lamφ G) lamε y JP J), v₂ _ _ y J hJ]
    rfl

end Group

end GlobalTheory.LamBiext
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseRestrictStableSubmoduleMatrixReStatement
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_leftInverse_restrict_stable_submodule_matrixRep : ∀ {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (V : Submodule L (Fin a → L)), IsInv τ V → ∃ (b : ℕ) (E : Matrix (Fin a) (Fin b) L) (D : Matrix (Fin b) (Fin a) L) (σ : Γ →* GL (Fin b) L), D * E = 1 ∧ LinearMap.range E.mulVecLin = V ∧ ∀ g, ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) = D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E ∧ ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E = E * ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
  first | exact @GlobalTheory.StableSubMat.exists_restrict | exact GlobalTheory.StableSubMat.exists_restrict | (intros; apply GlobalTheory.StableSubMat.exists_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
section
namespace GlobalTheory

private theorem exists_real_scalar_of_selfAdjoint_commute_irreducible {G H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ g, Commute A (σ g)) :
    ∃ c : ℝ, A = algebraMap ℝ (H →L[ℂ] H) c := by
  have key : ∀ x ∈ spectrum ℝ A, ∀ y ∈ spectrum ℝ A, x < y → False := by
    intro x hx y hy hxy
    obtain ⟨m, hxm, hmy⟩ : ∃ m : ℝ, x < m ∧ m < y := ⟨(x + y) / 2, by linarith, by linarith⟩
    have hfc : ContinuousOn (fun t : ℝ => max (t - m) 0) (spectrum ℝ A) :=
      (by fun_prop : Continuous fun t : ℝ => max (t - m) 0).continuousOn
    have hkc : ContinuousOn (fun t : ℝ => max (m - t) 0) (spectrum ℝ A) :=
      (by fun_prop : Continuous fun t : ℝ => max (m - t) 0).continuousOn
    have hprod : cfc (fun t : ℝ => max (t - m) 0) A * cfc (fun t : ℝ => max (m - t) 0) A = 0 := by
      rw [← cfc_mul _ _ A hfc hkc]
      have h0 : (fun t : ℝ => max (t - m) 0 * max (m - t) 0) = (0 : ℝ → ℝ) := by
        funext t
        rcases le_total t m with h | h
        · rw [max_eq_right (by linarith), zero_mul, Pi.zero_apply]
        · rw [max_eq_right (by linarith : m - t ≤ 0), mul_zero, Pi.zero_apply]
      rw [h0, cfc_zero]
    have hk0 : cfc (fun t : ℝ => max (m - t) 0) A ≠ 0 := by
      intro h0
      rw [← cfc_zero ℝ A] at h0
      have h1 := eqOn_of_cfc_eq_cfc h0 hkc continuousOn_const hA hx
      simp only [Pi.zero_apply] at h1
      have h2 : m - x ≤ max (m - x) 0 := le_max_left _ _
      linarith
    obtain ⟨w, hw⟩ : ∃ w, cfc (fun t : ℝ => max (m - t) 0) A w ≠ 0 := by
      by_contra hnot
      simp only [not_exists, not_not] at hnot
      exact hk0 (ContinuousLinearMap.ext hnot)
    let F := cfc (fun t : ℝ => max (t - m) 0) A
    let S : Submodule ℂ H := LinearMap.ker (F : H →ₗ[ℂ] H)
    have hS : IsClosed (S : Set H) := F.isClosed_ker
    have hinv : ∀ g, ∀ v ∈ S, σ g v ∈ S := by
      intro g v hv
      have hv' : F v = 0 := hv
      have hcg : F * σ g = σ g * F := ((hc g).cfc_real _).eq
      change F (σ g v) = 0
      have := congrArg (fun L : H →L[ℂ] H => L v) hcg
      simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply] at this
      rw [this, hv', map_zero]
    have hmem : cfc (fun t : ℝ => max (m - t) 0) A w ∈ S := by
      change F (cfc (fun t : ℝ => max (m - t) 0) A w) = 0
      simpa [F] using congrArg (fun L : H →L[ℂ] H => L w) hprod
    rcases hirr S hS hinv with hbot | htop
    · rw [hbot, Submodule.mem_bot] at hmem
      exact hw hmem
    · have hF : F = 0 := by
        ext v
        have hv : v ∈ S := by rw [htop]; exact Submodule.mem_top
        exact hv
      rw [← cfc_zero ℝ A] at hF
      have h1 := eqOn_of_cfc_eq_cfc hF hfc continuousOn_const hA hy
      simp only [Pi.zero_apply] at h1
      have h2 : y - m ≤ max (y - m) 0 := le_max_left _ _
      linarith
  have hsub : ∃ c : ℝ, ∀ x ∈ spectrum ℝ A, x = c := by
    by_cases hne : (spectrum ℝ A).Nonempty
    · obtain ⟨c, hc'⟩ := hne
      refine ⟨c, fun x hx => ?_⟩
      rcases lt_trichotomy x c with h | h | h
      · exact (key x hx c hc' h).elim
      · exact h
      · exact (key c hc' x hx h).elim
    · exact ⟨0, fun x hx => (hne ⟨x, hx⟩).elim⟩
  obtain ⟨c, hc'⟩ := hsub
  refine ⟨c, ?_⟩
  calc A = cfc (id : ℝ → ℝ) A := (cfc_id ℝ A hA).symm
    _ = cfc (fun _ : ℝ => c) A := cfc_congr fun x hx => hc' x hx
    _ = algebraMap ℝ (H →L[ℂ] H) c := cfc_const c A hA

theorem hilbert_schur_of_adjoint_closed :
    ∀ (G H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G → (H →L[ℂ] H)), (∀ g, ∃ g', σ g' = ContinuousLinearMap.adjoint (σ g)) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤) → ∀ T : H →L[ℂ] H, (∀ g, T ∘L σ g = σ g ∘L T) → ∃ c : ℂ, T = c • (1 : H →L[ℂ] H) := by
  intro G H _ _ _ σ hadj hirr T hT
  have hcomm : ∀ g, Commute T (σ g) := fun g => hT g
  have hcomm' : ∀ g, Commute (star T) (σ g) := by
    intro g
    obtain ⟨g', hg'⟩ := hadj g
    have h1 := congrArg star (hcomm g').eq
    rw [star_mul, star_mul, hg', ← ContinuousLinearMap.star_eq_adjoint, star_star] at h1
    exact h1.symm
  obtain ⟨a, ha⟩ := exists_real_scalar_of_selfAdjoint_commute_irreducible σ hirr (realPart T : H →L[ℂ] H)
    (realPart T).prop fun g => by
      rw [realPart_apply_coe]
      exact ((hcomm g).add_left (hcomm' g)).smul_left _
  obtain ⟨b, hb⟩ := exists_real_scalar_of_selfAdjoint_commute_irreducible σ hirr (imaginaryPart T : H →L[ℂ] H)
    (imaginaryPart T).prop fun g => by
      rw [imaginaryPart_apply_coe]
      exact (((hcomm g).sub_left (hcomm' g)).smul_left _).smul_left _
  refine ⟨(a : ℂ) + Complex.I * b, ?_⟩
  calc T = (realPart T : H →L[ℂ] H) + Complex.I • (imaginaryPart T : H →L[ℂ] H) :=
        (realPart_add_I_smul_imaginaryPart T).symm
    _ = ((a : ℂ) + Complex.I * b) • (1 : H →L[ℂ] H) := by
        rw [ha, hb, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, add_smul,
          mul_smul, ← Complex.coe_smul, ← Complex.coe_smul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ImageFiniteMemSubringStatement
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_image_mem_subring : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (iq : FractionRing O →+* Qbar l), (∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) → ∃ T : Finset (Qbar l), ∀ R : Subring (Qbar l), (∀ z : ℤ_[l], algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) ∈ R) → (↑T ⊆ (R : Set (Qbar l))) → ∀ x : O, iq (algebraMap O (FractionRing O) x) ∈ R := by
  first | exact @GlobalTheory.image_finite_mem_subring | exact GlobalTheory.image_finite_mem_subring | (intros; apply GlobalTheory.image_finite_mem_subring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftRepOfEntriesInImageStatement
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_lift_of_entries_mem_range : ∀ {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {b : ℕ} (τ : Γ →* GL (Fin b) L), (∀ g i j, ∃ x, f x = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) i j) → ∃ σ : Γ →* GL (Fin b) k, mapRep f σ = τ := by
  first | exact @GlobalTheory.lift_rep_of_entries_in_image | exact GlobalTheory.lift_rep_of_entries_in_image | (intros; apply GlobalTheory.lift_rep_of_entries_in_image <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixSystemNonzeroSolutionDescendsStatement
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_intertwiner_of_map : ∀ {k L Γ : Type} [Field k] [Field L] (f : k →+* L) {a b c : ℕ} (A : Γ → Matrix (Fin a) (Fin a) k) (B : Γ → Matrix (Fin b) (Fin b) k) (Q : Matrix (Fin c) (Fin a) k) (C : Matrix (Fin a) (Fin b) L), C ≠ 0 → (∀ g, (A g).map f * C = C * (B g).map f) → Q.map f * C = 0 → ∃ X : Matrix (Fin a) (Fin b) k, X ≠ 0 ∧ (∀ g, A g * X = X * B g) ∧ Q * X = 0 := by
  first | exact @GlobalTheory.matrix_system_nonzero_solution_descends | exact GlobalTheory.matrix_system_nonzero_solution_descends | (intros; apply GlobalTheory.matrix_system_nonzero_solution_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplittingFstMemIntegers
section
open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory

theorem adicCompletion_mem_integers_of_isIntegral_int {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {y : v.adicCompletion F} (hy : IsIntegral ℤ y) :
    y ∈ v.adicCompletionIntegers F := by
  let O := v.adicCompletionIntegers F
  have hint : (Valued.v : Valuation (v.adicCompletion F) _).Integers O :=
    Valuation.integer.integers _
  have hy' : IsIntegral O y := hy.tower_top
  exact hint.mem_of_integral hy'

theorem splitting_fst_mem_integers : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
    (∀ a : v.adicCompletion F, spl ((1 : E) ⊗ₜ[F] a) = (a, a)) →
    ∀ z ∈ Formalism.BasicNotions.intV E v, (spl z).1 ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ v spl h1 z hz
  let φ : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F := (RingHom.fst _ _).comp spl.toRingHom
  let ψ : E →+* v.adicCompletion F := φ.comp Algebra.TensorProduct.includeLeftRingHom
  have key : Formalism.BasicNotions.intV E v ≤ (v.adicCompletionIntegers F).toSubring.comap φ := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro w (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨r, rfl⟩ := hx
      show ψ (algebraMap (𝓞 E) E r) ∈ v.adicCompletionIntegers F
      apply adicCompletion_mem_integers_of_isIntegral_int
      obtain ⟨p, hm, hp⟩ : IsIntegral ℤ (algebraMap (𝓞 E) E r) := RingOfIntegers.isIntegral_coe r
      refine ⟨p, hm, ?_⟩
      have h2 := congrArg ψ hp
      rw [Polynomial.hom_eval₂, map_zero] at h2
      rw [Polynomial.eval₂_eq_sum_range] at h2 ⊢
      simpa using h2
    · show (spl ((1 : E) ⊗ₜ[F] y)).1 ∈ v.adicCompletionIntegers F
      rw [h1]
      exact hy
  exact key hz

end GlobalTheory
end

