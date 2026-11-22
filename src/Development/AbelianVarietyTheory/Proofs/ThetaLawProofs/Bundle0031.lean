import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicCoordSimilitudeThetaProduct
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0012
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.BoxPowerBasic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.BoxPower

section Gen

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {J K : Type} [Fintype J] [Fintype K]

theorem mem_of_box {pr : J → (X' ⟶ X)} {φ' : K → (Y ⟶ X')} {φ : J → K → (Y₀ ⟶ X)} {ρ : J → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) {y : Y} {jN : K → J → M.ι}
    (hy : y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN) (i : J) :
    ρ i y ∈ LB.wchart M (φ i) (fun a => jN a i) :=
  Out.GeneratorPullback.pullAlong_le M (pr i) (ρ i) (φ i) φ' (hψ i) (fun a _ => jN a i) (Out.GeneratorPullback.box_le M pr φ' jN i hy)

theorem gm_box {pr : J → (X' ⟶ X)} {φ' : K → (Y ⟶ X')} {φ : J → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : J → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) {y : Y} {jN : K → J → M.ι}
    (hy : y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN) :
    gm (𝟙 Y) y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN)
      ((Out.GeneratorPullback.boxGen M pr φ' ε (fun i => Out.GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))).s jN) =
      ∏ i, gm (ρ i) y (LB.wchart M (φ i) (fun a => jN a i)) ((t i).s (fun a => jN a i)) := by
  refine (map_prod (gm (𝟙 Y) y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN))
    (fun i => res (Out.GeneratorPullback.box_le M pr φ' jN i)
      ((Out.GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i)).s (fun a _ => jN a i))) Finset.univ).trans
    (Finset.prod_congr rfl fun i _ => ?_)
  refine (gm_res (𝟙 Y) y (Out.GeneratorPullback.box_le M pr φ' jN i) hy _).trans ?_
  refine (gm_res (𝟙 Y) y (Out.GeneratorPullback.pullAlong_le M (pr i) (ρ i) (φ i) φ' (hψ i) (fun a _ => jN a i))
    (Out.GeneratorPullback.box_le M pr φ' jN i hy) _).trans ?_
  refine (gm_pull (𝟙 Y) (ρ i) y _ (mem_of_box hψ hy i) _).trans ?_
  rw [Category.id_comp]

theorem trF_box {pr : J → (X' ⟶ X)} {φ' : K → (Y ⟶ X')} {φ : J → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : J → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) {y : Y} {jN jN' : K → J → M.ι}
    (hy : y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN)
    (hy' : y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN') :
    trF (L := LB.LinComb M pr (fun _ => 1)) φ' ε (𝟙 Y) y jN jN' =
      ∏ i, trF (φ i) ε (ρ i) y (fun a => jN a i) (fun a => jN' a i) := by
  unfold trF
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_zpow]
  refine congrArg (· ^ ε a) ?_
  refine (gm_linComb M pr (fun _ => 1) (𝟙 Y ≫ φ' a) y (jN a) (jN' a) (Set.mem_iInter.1 hy a)
    (Set.mem_iInter.1 hy' a)).trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [zpow_one, Category.id_comp, hψ]

theorem box_isGen {pr : J → (X' ⟶ X)} {φ' : K → (Y ⟶ X')} {φ : J → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : J → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε)) (ht : ∀ i, (t i).IsGen) :
    (Out.GeneratorPullback.boxGen M pr φ' ε (fun i => Out.GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))).IsGen := by
  refine isGen_of_gm _ fun y jN jN' hy hy' => ?_
  refine (gm_box hψ t hy).trans (Eq.trans ?_ (congrArg₂ (· * ·) (trF_box hψ hy hy') (gm_box hψ t hy')).symm)
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => gen_trans (ht i) (ρ i) y (mem_of_box hψ hy i) (mem_of_box hψ hy' i)

end Gen

section Grp

variable {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}

theorem boxRig_isGen [IsCommMonObj G'] [IsCommMonObj G] (p : Out.IsPowGrp G' G j) (L : LB G.left)
    (r : LB.Gen (L.pull (eSec G))) (hr : r.IsGen) : (Out.boxRig p L r).IsGen :=
  box_isGen (M := L) (pr := fun i => (p.pr i).left) (φ' := fun _ : PUnit => eSec G') (φ := fun _ _ => eSec G)
    (ε := fun _ => 1) (ρ := fun _ => 𝟙 _)
    (fun i _ => letI := p.hom i; (CubeMap.ofHom (p.pr i)).e_comm) (fun _ => r) (fun _ => hr)

theorem sym_box (pr : Fin j → (G' ⟶ G)) [∀ i, IsMonHom (pr i)] (L : LB G.left) (hL : Out.Sym G L) :
    Out.Sym G' (Out.boxLB L pr) := by
  intro s
  obtain ⟨U, hU, t, ht⟩ := hL s
  have le : ∀ i, G'.hom ⁻¹ᵁ U ≤ (pr i).left ⁻¹ᵁ (G.hom ⁻¹ᵁ U) := fun i => by
    rw [← Scheme.Hom.comp_preimage, Over.w]
  have e : ∀ i, (G'.hom ⁻¹ᵁ U).ι ≫ (pr i).left = (pr i).left.resLE _ _ (le i) ≫ (G.hom ⁻¹ᵁ U).ι := fun i =>
    (Scheme.Hom.resLE_comp_ι _ _).symm
  refine ⟨U, hU, _, box_isGen (M := L) (pr := fun i => (pr i).left)
    (φ := fun _ => ![(G.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : G ⟶ G).left, (G.hom ⁻¹ᵁ U).ι])
    (ρ := fun i => (pr i).left.resLE _ _ (le i)) (fun i a => ?_) (fun _ => t) (fun _ => ht)⟩
  fin_cases a
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [← Category.assoc, ← e, Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
  · exact e i

end Grp

theorem boxPower_basic : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (j : ℕ), (Out.boxLB P.L (Out.powPr P.A (n := j))).IsLB ∧ Out.Sym (Out.powObj P.A j) (Out.boxLB P.L (Out.powPr P.A (n := j))) ∧ ∀ rig : LB.Gen (P.L.pull (eSec P.A)), rig.IsGen → (haveI := P.isAb.comm; (Out.boxRig (Out.powIsPowGrp P.A j) P.L rig).IsGen) := by
  intro R _ P j
  have := P.isAb.comm
  exact ⟨DVR.linComb_isLB _ P.isLB _ _, sym_box _ _ P.sym, fun rig h => boxRig_isGen _ _ rig h⟩

end GlobalTheory.BoxPower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicCoordSimilitudeThetaProductStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_coord_similitudeThetaProduct : ∀ (g m : ℕ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (Th : Fin (m ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ), charHalf g a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → LevBasis a b m Th → ∀ k n : Fin 4 → Fin g → ℤ, ∃ qa : (Fin g → Fin g → ℂ) → (Fin 4 → Fin (m ^ g)) → ℂ, (∀ I, DifferentiableOn ℂ (fun p => qa p I) (Key.phDom g)) ∧ ∀ p ∈ Key.phDom g, ∀ q : (Fin 4 → Fin (m ^ g)) → ℂ, (∀ y, simTheta (per p) a b al m k n y = ∑ I, q I * ∏ c, Th (I c) p (y c)) ↔ q = qa p := by
  first | exact @GlobalTheory.SimilTheta.exists_holomorphic_coord_simTheta | exact GlobalTheory.SimilTheta.exists_holomorphic_coord_simTheta | (intros; apply GlobalTheory.SimilTheta.exists_holomorphic_coord_simTheta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisedIsoPullbackMulByM
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa

theorem exists_zpowGen {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (n : ℤ) :
    ∃ t' : LB.Gen (LB.LinComb L φ (fun k => ε k * n)), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, val t' r z J = val t r z J ^ n := by
  refine ⟨⟨fun j => (show Γ(Y, LB.wchart L φ j)ˣ from t.s j) ^ n⟩, isGen_of_gm _ fun y j j' hj hj' => ?_,
    fun Z r z J => map_zpow _ _ _⟩
  refine (map_zpow _ _ _).trans (Eq.trans ?_ (congrArg _ (map_zpow _ _ _).symm))
  rw [gen_trans ht (𝟙 Y) y hj hj', mul_zpow]
  congr 1
  simp only [trF, zpow_mul, Finset.prod_zpow]

theorem exists_normalised_mulPull : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : KeyIn R) (m : ℕ), ∃ mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]), mu.IsGen ∧ ∀ (p : (𝟙_ (Over (Sp R))).left) J, Good x.P.L p J → val mu (eSec x.P.A) p J = val x.rig (𝟙 _) p J ^ (1 - (m : ℤ) ^ 2) := by
  intro laws R _ _ x m
  have hL := x.P.isLB
  obtain ⟨α, hα⟩ := laws.mulPull _ x.P m
  obtain ⟨ρ, hρ, hρv⟩ := exists_zpowGen (φ := fun _ : PUnit => eSec x.P.A) (ε := fun _ => 1) x.rig x.rig_gen
    (1 - (m : ℤ) ^ 2)
  have e₁ : eSec x.P.A ≫ (Out.mulA x.P.A m).left = eSec x.P.A := by
    have : η[x.P.A] ≫ Out.mulA x.P.A m = η[x.P.A] := by
      have h1 : η[x.P.A] = (1 : 𝟙_ (Over (Sp R)) ⟶ x.P.A) := by
        rw [Hom.one_def, toUnit_unit, Category.id_comp]
      rw [MonObj.comp_pow, Category.comp_id, h1, one_pow]
    exact congrArg (·.left) this
  have e₂ : eSec x.P.A ≫ (toUnit x.P.A).left = 𝟙 _ := by
    have : η[x.P.A] ≫ toUnit x.P.A = 𝟙 _ := toUnit_unique _ _
    exact congrArg (·.left) this
  obtain ⟨mu, hmu, hv⟩ := exists_gen hL (K' := Fin 2) (φ' := ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left])
    (ε' := ![1, -(m : ℤ) ^ 2]) (fun U _ f => by
      refine (Fintype.prod_sum_type _).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique,
        Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id, e₁]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen x.P.L _ _ _ _ (LB.invGen x.P.L _ _ α) (LB.pullGen x.P.L _ _
      (LB.mulGen x.P.L _ _ _ _ (LB.pullGen x.P.L _ _ α (eSec x.P.A)) ρ) (toUnit x.P.A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.invGen_isGen _ _ _ _ hα) (DVR.pullGen_isGen _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) hρ) _))
  refine ⟨mu, hmu, fun p J hJ => ?_⟩
  rw [hv _ _ p J hJ, val_mul hJ, val_inv, val_pull hJ, val_mul hJ, val_pull hJ, hρv, e₂, Category.id_comp,
    inv_mul_cancel_left]

end GlobalTheory.KeyKa
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInvariantFromIntersectionUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyInvariantFromIntersection_unique : Out.Laws → ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K) (n l l' : ℕ) (al : ℕ → Matrix (Fin 4) (Fin 4) ℤ) (s : Fin x.P.g → RR x n) (κ κ' : Kˣ), admitted x.P.g n l l' al → KaVal x n l l' al s κ → KaVal x n l l' al s κ' → κ = κ' := by
  first | exact @GlobalTheory.KaUnique.kaVal_unique | exact GlobalTheory.KaUnique.kaVal_unique | (intros; apply GlobalTheory.KaUnique.kaVal_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SimilitudeGeneratorEqExpInFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

noncomputable section
namespace GlobalTheory.SimilTheta

theorem span_single_block_eq_top {V : Type} [AddCommGroup V] [Module ℝ V] {Λ : Set V} (h : Submodule.span ℝ Λ = ⊤) :
    Submodule.span ℝ {s : Fin 4 → V | ∃ c, ∃ l ∈ Λ, s = Pi.single c l} = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  rw [← Finset.univ_sum_single y]
  refine Submodule.sum_mem _ fun c _ => ?_
  have hz : y c ∈ Submodule.span ℝ Λ := h ▸ Submodule.mem_top
  generalize y c = v at hz
  induction hz using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span ⟨c, v, hv, rfl⟩
  | zero => rw [Pi.single_zero]; exact Submodule.zero_mem _
  | add v v' _ _ hv hv' => rw [Pi.single_add]; exact Submodule.add_mem _ hv hv'
  | smul r v _ hv => rw [Pi.single_smul]; exact Submodule.smul_mem _ r hv

theorem ex_zsmul_eq_zpow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (s : ℤ) (z : Fin g → ℂ) :
    u.ex (s • z) = u.ex z ^ s :=
  map_zpow (MonoidHom.mk' (fun z : Multiplicative (Fin g → ℂ) => u.ex z.toAdd) fun _ _ => u.ex_add _ _)
    (Multiplicative.ofAdd z) s

theorem comp_alMap_ex {g : ℕ} (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (al : Matrix (Fin 4) (Fin 4) ℤ) (r : Fin 4)
    (t : Fin g → ℂ) (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4)
    (hpt : ∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) :
    pt ≫ alMap x al r (u.ex t) = u.ex (∑ c, al r c • y c + t) := by
  have e₀ : pt ≫ toUnit _ = 𝟙 _ := toUnit_unique _ _
  simp only [alMap, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, MonObj.comp_mul,
    GrpObj.comp_zpow, MonObj.comp_one, hpt, reassoc_of% e₀, Fin.sum_univ_succ, Fin.sum_univ_zero, u.ex_add, ex_zsmul_eq_zpow,
    GlobalTheory.PowUnif.ex_zero]

theorem simil_generator_eq_exp : ∀ (g m : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ), charHalf g a b → Wit x h u τ a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∀ (k n : Fin 4 → Fin g → ℤ) (ξ : Fin 4 → Pt x), (∀ r, ξ r = u.ex (tors τ al m k n r)) → ∀ w : LB.Gen (LB.LinComb x.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) (Sum.elim (fun _ => 1) (fun _ => -(m : ℤ)))), w.IsGen → ∃ C : ℂ, C ≠ 0 ∧ ∀ (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4), (∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) → ∀ j : Fin 4 ⊕ Fin 4 → x.P.L.ι, (∀ r, ⊤ ≤ (u.ex (∑ c, al r c • y c + tors τ al m k n r)).left ⁻¹ᵁ x.P.L.U (j (Sum.inl r))) → (∀ c, ⊤ ≤ (u.ex (y c)).left ⁻¹ᵁ x.P.L.U (j (Sum.inr c))) → valAt' pt.left (LB.wchart x.P.L (Sum.elim (fun r => (alMap x al r (ξ r)).left) (fun c => (Out.powPr x.P.A c).left)) j) (w.s j).val * Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c) = C * ((∏ r, u.fr (j (Sum.inl r)) (∑ c, al r c • y c + tors τ al m k n r)) * ∏ c, u.fr (j (Sum.inr c)) (y c) ^ (-(m : ℤ))) := by
  intro g m x h u τ a b al hab hW hm hal k n ξ hξ w hw
  obtain rfl : ξ = fun r => u.ex (tors τ al m k n r) := funext hξ
  let P : (Fin 4 → Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4) := fun y =>
    (Out.powIsLimit x.P.A 4).lift (Fan.mk _ fun c => u.ex (y c))
  have hP : ∀ y c, P y ≫ Out.powPr x.P.A c = u.ex (y c) := fun y c =>
    (Out.powIsLimit x.P.A 4).fac (Fan.mk _ fun c => u.ex (y c)) ⟨c⟩
  have hPu : ∀ (y : Fin 4 → Fin g → ℂ) (pt : 𝟙_ (Over (Sp ℂ)) ⟶ Out.powObj x.P.A 4),
      (∀ c, pt ≫ Out.powPr x.P.A c = u.ex (y c)) → pt = P y := fun y pt hpt =>
    (Out.powIsLimit x.P.A 4).hom_ext fun ⟨c⟩ => (hpt c).trans (hP y c).symm
  have hd : GlobalTheory.PowUnif.IsHolFamily (fun z => (u.ex z).left) := u.hol
  let z : Fin 4 ⊕ Fin 4 → (Fin 4 → Fin g → ℂ) → Fin g → ℂ :=
    Sum.elim (fun r y => ∑ c, al r c • y c + tors τ al m k n r) (fun c y => y c)
  obtain ⟨T, hT, hT0, hTv⟩ := GlobalTheory.T.exists_entire_ne_zero_val_eq_mul_prod_frames x.P.A x.P.L g u x.P.isLB _ _ _ _ w hw (Fin 4 → Fin g → ℂ)
    (fun y => (P y).left) z
    (GlobalTheory.PowUnif.isHolFamily_powObj _ 4 P fun c => by
      simp only [hP]
      exact hd.precomp (T := fun y : Fin 4 → Fin g → ℂ => y c) (by fun_prop))
    (by
      rintro (r | c)
      · change Differentiable ℂ fun y : Fin 4 → Fin g → ℂ => ∑ c, al r c • y c + tors τ al m k n r
        fun_prop
      · change Differentiable ℂ fun y : Fin 4 → Fin g → ℂ => y c
        fun_prop)
    (by
      rintro y (r | c)
      · exact congrArg (·.left) (comp_alMap_ex x u al r _ y (P y) (hP y))
      · exact congrArg (·.left) (hP y c))
  let ee : (Fin 4 → Fin g → ℂ) → ℂ := fun y =>
    Complex.exp (2 * Real.pi * Complex.I * ∑ c, (fun i => (n c i : ℂ)) ⬝ᵥ y c)
  have hee : Differentiable ℂ ee := by
    simp only [ee, dotProduct]
    fun_prop
  have hper : ∀ y, ∀ s ∈ {s : Fin 4 → Fin g → ℂ | ∃ c, ∃ l ∈ (u.Λ : Set (Fin g → ℂ)), s = Pi.single c l},
      T (y + s) * ee (y + s) = T y * ee y := by
    rintro y _ ⟨c, l, hl, rfl⟩
    obtain ⟨k₀, n₀, hl'⟩ := (hW.2.2.1 l).1 hl
    obtain rfl : l = lat τ k₀ n₀ := hl'
    have hlat : ∀ (k n : Fin g → ℤ) (v : Fin g → ℂ), u.ex (v + lat τ k n) = u.ex v := fun k n v => by
      rw [u.ex_add, (u.ker (lat τ k n)).2 ((hW.2.2.1 _).2 ⟨k, n, rfl⟩), _root_.mul_one]
    set y' := y + Pi.single c (lat τ k₀ n₀) with hy'
    have hz₁ : ∀ r, z (Sum.inl r) y' = z (Sum.inl r) y + lat τ (al r c • k₀) (al r c • n₀) := fun r => by
      simp only [z, Sum.elim_inl, hy', Pi.add_apply, smul_add, Finset.sum_add_distrib, lat_zsmul]
      rw [Finset.sum_eq_single c (f := fun c' => al r c' • (Pi.single c (lat τ k₀ n₀) : Fin 4 → Fin g → ℂ) c')
        (fun c' _ hc => by rw [Pi.single_eq_of_ne hc, smul_zero]) (by simp),
        Pi.single_eq_same]
      abel
    have hz₂ : y' c = y c + lat τ k₀ n₀ := by simp [hy']
    have hz₃ : ∀ c', c' ≠ c → y' c' = y c' := fun c' hc => by simp [hy', Pi.single_eq_of_ne hc]
    have hex : ∀ q, u.ex (z q y') = u.ex (z q y) := by
      rintro (r | c')
      · rw [hz₁, hlat]
      · change u.ex (y' c') = u.ex (y c')
        by_cases hc : c' = c
        · rw [hc, hz₂, hlat]
        · rw [hz₃ c' hc]
    have hPP : P y' = P y := hPu y _ fun c' => (hP y' c').trans (hex (Sum.inr c'))
    choose j hj using fun q => GlobalTheory.PowUnif.exists_chart x.P.isLB (u.ex (z q y)).left
    have hj' : ∀ q, ⊤ ≤ (u.ex (z q y')).left ⁻¹ᵁ x.P.L.U (j q) := fun q => by rw [hex]; exact hj q
    have e₁ := hTv y j hj
    have e₂ := hTv y' j hj'
    rw [hPP, e₁] at e₂
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_one] at e₂
    have f₁ : ∏ r, u.fr (j (Sum.inl r)) (z (Sum.inl r) y) =
        (∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) *
          ∏ r, u.fr (j (Sum.inl r)) (z (Sum.inl r) y') := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [hz₁]
      exact GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul g x h u τ a b hab hW _ _ _ _ (hj _)
    have f₂ : ∏ c', u.fr (j (Sum.inr c')) (z (Sum.inr c') y) ^ (-(m : ℤ)) =
        aut τ a b k₀ n₀ (y c) ^ (-(m : ℤ)) * ∏ c', u.fr (j (Sum.inr c')) (z (Sum.inr c') y') ^ (-(m : ℤ)) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c), ← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
        ← _root_.mul_assoc, ← mul_zpow]
      refine congrArg₂ (· * ·) (congrArg (· ^ _) ?_) (Finset.prod_congr rfl fun c' hc => ?_)
      · change u.fr _ (y c) = _ * u.fr _ (y' c)
        rw [hz₂]
        exact GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul g x h u τ a b hab hW _ _ _ _ (hj (Sum.inr c))
      · change u.fr _ (y c') ^ _ = u.fr _ (y' c') ^ _
        rw [hz₃ c' (Finset.ne_of_mem_erase hc)]
    have n₁ : ∏ r, u.fr (j (Sum.inl r)) (z (Sum.inl r) y') ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun r _ => u.fr_ne _ _ (hj' _)
    have n₂ : ∏ c', u.fr (j (Sum.inr c')) (z (Sum.inr c') y') ^ (-(m : ℤ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (u.fr_ne _ _ (hj' _))
    have e₃ : T y' = T y * (∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) *
        aut τ a b k₀ n₀ (y c) ^ (-(m : ℤ)) := by
      rw [f₁, f₂] at e₂
      refine mul_right_cancel₀ (mul_ne_zero n₁ n₂) (e₂.symm.trans ?_)
      ring
    have e₄ : ee y' = ee y * Complex.exp (2 * Real.pi * Complex.I * ((fun i => (n c i : ℂ)) ⬝ᵥ lat τ k₀ n₀)) := by
      simp only [ee, hy', Pi.add_apply, dotProduct_add, Finset.sum_add_distrib, mul_add, Complex.exp_add]
      rw [Finset.sum_eq_single c (f := fun c' => (fun i => (n c' i : ℂ)) ⬝ᵥ
          (Pi.single c (lat τ k₀ n₀) : Fin 4 → Fin g → ℂ) c')
        (fun c' _ hc => by rw [Pi.single_eq_of_ne hc, dotProduct_zero]) (by simp), Pi.single_eq_same]
    have e₅ : (∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) * _ = _ :=
      (aut_similitude_and_mul g m τ a b al hab hW.1 hm hal).1 k n y c k₀ n₀
    have n₃ := pow_ne_zero m (aut_ne_zero τ a b k₀ n₀ (y c))
    rw [e₃, e₄, zpow_neg, zpow_natCast]
    calc _ = T y * ee y * ((∏ r, aut τ a b (al r c • k₀) (al r c • n₀) (z (Sum.inl r) y)) *
          Complex.exp (2 * Real.pi * Complex.I * ((fun i => (n c i : ℂ)) ⬝ᵥ lat τ k₀ n₀))) *
          (aut τ a b k₀ n₀ (y c) ^ m)⁻¹ := by ring
      _ = _ := by rw [e₅, mul_inv_cancel_right₀ n₃]
  have hc := GlobalTheory.entire_apply_eq_of_periodic_of_span_real (F := fun y => T y * ee y) (hT.mul hee)
    (span_single_block_eq_top u.full) hper
  refine ⟨T 0 * ee 0, mul_ne_zero (hT0 0) (Complex.exp_ne_zero _), fun y pt hpt j hj₁ hj₂ => ?_⟩
  obtain rfl := hPu y pt hpt
  have e₁ := hTv y j (by rintro (r | c); exacts [hj₁ r, hj₂ c])
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_one, z] at e₁
  rw [← hc y 0]
  refine (congrArg (· * ee y) e₁).trans ?_
  ring

end GlobalTheory.SimilTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaGeneratorPullbackMulConstInFrames
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.SimilTheta

namespace GlobalTheory.SimilTheta

theorem ex_nsmul_eq_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (m : ℕ)
    (z : Fin g → ℂ) : u.ex ((m : ℤ) • z) = u.ex z ^ m := by
  rw [natCast_zsmul]
  induction m with
  | zero => simpa using GlobalTheory.CubeValues.ex_zero u
  | succ n ih => rw [succ_nsmul, u.ex_add, ih, pow_succ]

theorem ex_comp_id_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) (m : ℕ)
    (z : Fin g → ℂ) : u.ex z ≫ (𝟙 A) ^ m = u.ex ((m : ℤ) • z) := by
  rw [ex_nsmul_eq_pow, MonObj.comp_pow, Category.comp_id]

theorem generator_mul_const_in_frames : ∀ (g m : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ), charHalf g a b → Wit x h u τ a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∀ mu : LB.Gen (LB.LinComb x.P.L (K := Fin 2) ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2]), mu.IsGen → ∃ C : ℂ, C ≠ 0 ∧ ∀ (z : Fin g → ℂ) (j : Fin 2 → x.P.L.ι), ⊤ ≤ (u.ex ((m : ℤ) • z)).left ⁻¹ᵁ x.P.L.U (j 0) → ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U (j 1) → valAt' (u.ex z).left (LB.wchart x.P.L ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] j) (mu.s j).val = C * (u.fr (j 0) ((m : ℤ) • z) * u.fr (j 1) z ^ (-(m : ℤ) ^ 2)) := by
  intro g m x h u τ a b al hab hW hm hal mu hmu
  obtain ⟨T, hT, hT0, hTv⟩ := GlobalTheory.T.exists_entire_ne_zero_val_eq_mul_prod_frames x.P.A x.P.L g u x.P.isLB x.P.A.left (Fin 2)
    ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] ![1, -(m : ℤ) ^ 2] mu hmu (Fin g → ℂ) (fun z => (u.ex z).left)
    ![fun z => (m : ℤ) • z, fun z => z] u.hol
    (Fin.forall_fin_two.2 ⟨differentiable_id.const_smul (m : ℤ), differentiable_id⟩)
    (fun e => Fin.forall_fin_two.2 ⟨congrArg (fun q => q.left) (ex_comp_id_pow u m e), Category.comp_id _⟩)
  have hv : ∀ (z : Fin g → ℂ) (j : Fin 2 → x.P.L.ι), ⊤ ≤ (u.ex ((m : ℤ) • z)).left ⁻¹ᵁ x.P.L.U (j 0) →
      ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U (j 1) →
      valAt' (u.ex z).left (LB.wchart x.P.L ![((𝟙 x.P.A) ^ m).left, 𝟙 x.P.A.left] j) (mu.s j).val =
        T z * (u.fr (j 0) ((m : ℤ) • z) * u.fr (j 1) z ^ (-(m : ℤ) ^ 2)) := fun z j h0 h1 => by
    refine (hTv z j (Fin.forall_fin_two.2 ⟨h0, h1⟩)).trans ?_
    rw [Fin.prod_univ_two]
    exact congrArg (fun t => T z * (t * u.fr (j 1) z ^ (-(m : ℤ) ^ 2))) (zpow_one _)
  have hper : ∀ z, ∀ l ∈ (u.Λ : Set (Fin g → ℂ)), T (z + l) = T z := by
    intro z l hl
    obtain ⟨k, n, hkn⟩ := (hW.2.2.1 l).1 hl
    obtain rfl : l = lat τ k n := hkn
    obtain ⟨i0, h0⟩ := GlobalTheory.PowUnif.exists_chart x.P.isLB (u.ex ((m : ℤ) • z)).left
    obtain ⟨i1, h1⟩ := GlobalTheory.PowUnif.exists_chart x.P.isLB (u.ex z).left
    have e1 : u.ex (z + lat τ k n) = u.ex z := GlobalTheory.CubeValues.ex_add_period u z _ hl
    have e0 : u.ex ((m : ℤ) • (z + lat τ k n)) = u.ex ((m : ℤ) • z) := by
      rw [ex_nsmul_eq_pow, e1, ex_nsmul_eq_pow]
    have A1 := hv z ![i0, i1] h0 h1
    have A2 := hv (z + lat τ k n) ![i0, i1] (by rw [e0]; exact h0) (by rw [e1]; exact h1)
    rw [e1, A1] at A2
    have n0 := u.fr_ne i0 ((m : ℤ) • (z + lat τ k n)) (by rw [e0]; exact h0)
    have n1 := u.fr_ne i1 (z + lat τ k n) (by rw [e1]; exact h1)
    have f0 := GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul g x h u τ a b hab hW ((m : ℤ) • k) ((m : ℤ) • n) i0 _ h0
    have f1 := GlobalTheory.T.thetaUniformisation_frame_eq_automorphy_mul g x h u τ a b hab hW k n i1 _ h1
    rw [lat_zsmul, ← smul_add, (GlobalTheory.SimilTheta.aut_similitude_and_mul g m τ a b al hab hW.1 hm hal).2] at f0
    change T z * (u.fr i0 _ * u.fr i1 _ ^ _) = T _ * (u.fr i0 _ * u.fr i1 _ ^ _) at A2
    rw [f0, f1] at A2
    have na := aut_ne_zero τ a b k n z
    have hp : (-(m : ℤ) ^ 2) = -((m ^ 2 : ℕ) : ℤ) := by push_cast; ring
    rw [hp, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_pow] at A2
    field_simp at A2
    exact A2.symm
  refine ⟨T 0, hT0 0, fun z j h0 h1 => ?_⟩
  rw [hv z j h0 h1, GlobalTheory.entire_apply_eq_of_periodic_of_span_real hT u.full hper z 0]

end GlobalTheory.SimilTheta
end

