import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedResEta
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0106
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedResEtaStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_resEta_alt : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → (∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k) → (∀ a : Fˣ, (∏ᶠ v : HeightOneSpectrum (𝓞 F), etaFin (L := L) F v a) * ∏ w : InfinitePlace F, etaInf F w a = 1) → ∀ (n : I → ℤ), (∀ i, Odd (n i)) → (∀ ζ : L, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) → ∃ δ : Lˣ, (δ : L) = ζ * c (δ : L) ∧ (∀ P : HeightOneSpectrum (𝓞 L), (aboveF (L := L) F (P.under (𝓞 F))).card = 1 → Even (ordF P δ)) ∧ ∏ i, (φ i (δ : L) / ((‖φ i (δ : L)‖ : ℝ) : ℂ)) ^ n i = 1) → ∃ χ : HChar L, χ.IsUnitary ∧ (∀ v, χ.UnrAt v) ∧ χ.ResEta F ∧ χ.HasInf φ n := by
  first | exact @GlobalTheory.Mem.EtaExt.exists_unramified_resEta | exact GlobalTheory.Mem.EtaExt.exists_unramified_resEta | (intros; apply GlobalTheory.Mem.EtaExt.exists_unramified_resEta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GmSqPullG
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqLevel

open TopologicalSpace

variable {X : Scheme.{0}}

abbrev sqLB (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)

theorem mem_sq {L : LB X} {x : X} {J : Fin 1 → L.ι} : x ∈ (sqLB L).U J ↔ x ∈ L.U (J 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem mem_sq_pull {Y : Scheme.{0}} {L : LB X} {F : Y ⟶ X} {y : Y} {J : PUnit → Fin 1 → L.ι} :
    y ∈ ((sqLB L).pull F).U J ↔ F y ∈ L.U (J PUnit.unit 0) :=
  mem_pull.trans mem_sq

theorem gm_sq_g {Y : Scheme.{0}} (L : LB X) (r : Y ⟶ X) (y : Y) (J J' : Fin 1 → L.ι) (hJ : r y ∈ L.U (J 0))
    (hJ' : r y ∈ L.U (J' 0)) :
    gm r y ((sqLB L).U J ⊓ (sqLB L).U J') ((sqLB L).g J J') = gm r y _ (L.g (J 0) (J' 0)) ^ 2 := by
  refine (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => 2) r y J J' (mem_sq.2 hJ) (mem_sq.2 hJ')).trans ?_
  rw [Fin.prod_univ_one, Category.comp_id]
  exact zpow_two _ |>.trans (pow_two _).symm

theorem gm_sq_pull_g {Y Z : Scheme.{0}} (L : LB X) (F : Y ⟶ X) (r : Z ⟶ Y) (z : Z) (J J' : PUnit → Fin 1 → L.ι)
    (hJ : F (r z) ∈ L.U (J PUnit.unit 0)) (hJ' : F (r z) ∈ L.U (J' PUnit.unit 0)) :
    gm r z (((sqLB L).pull F).U J ⊓ ((sqLB L).pull F).U J') (((sqLB L).pull F).g J J') =
      gm (r ≫ F) z _ (L.g (J PUnit.unit 0) (J' PUnit.unit 0)) ^ 2 :=
  (gm_pull_g (sqLB L) F r z J J' (mem_sq_pull.2 hJ) (mem_sq_pull.2 hJ')).trans
    (gm_sq_g L (r ≫ F) z _ _ hJ hJ')

variable {B G E : Scheme.{0}} {M : LB B} {L : LB G} {p : E ⟶ B} {f : E ⟶ G}

theorem sqIso_le (q : (PUnit → Fin 1 → M.ι) × (PUnit → Fin 1 → L.ι)) :
    ((sqLB M).pull p).U q.1 ⊓ ((sqLB L).pull f).U q.2 ≤
      (M.pull p).U (fun _ => q.1 PUnit.unit 0) ⊓ (L.pull f).U (fun _ => q.2 PUnit.unit 0) :=
  fun _ h => ⟨mem_pull.2 (mem_sq_pull.1 h.1), mem_pull.2 (mem_sq_pull.1 h.2)⟩

def sqIso (w : LB.Iso (L.pull f) (M.pull p)) : LB.Iso ((sqLB L).pull f) ((sqLB M).pull p) :=
  ⟨fun q => res (sqIso_le q) (w.s (fun _ => q.1 PUnit.unit 0, fun _ => q.2 PUnit.unit 0)) ^ 2⟩

theorem gw_sqIso (w : LB.Iso (L.pull f) (M.pull p)) {Z : Scheme.{0}} (r : Z ⟶ E) (z : Z) (J : Fin 1 → M.ι)
    (K : PUnit → Fin 1 → L.ι) (hJ : p (r z) ∈ M.U (J 0)) (hK : f (r z) ∈ L.U (K PUnit.unit 0)) :
    gw (sqIso w) r z J K = gw w r z (J 0) (fun _ => K PUnit.unit 0) ^ 2 := by
  have hm : r z ∈ ((sqLB M).pull p).U (fun _ => J) ⊓ ((sqLB L).pull f).U K :=
    ⟨mem_sq_pull.2 hJ, mem_sq_pull.2 hK⟩
  exact (map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ hm _))

theorem sqIso_isGen {w : LB.Iso (L.pull f) (M.pull p)} (hw : w.IsGen) : (sqIso w).IsGen := by
  rw [isGen_iff] at hw ⊢
  intro Y r y j j' k k' hj hj' hk hk'
  have hj₀ := mem_sq.1 hj
  have hj₀' := mem_sq.1 hj'
  have hk₀ := mem_sq_pull.1 hk
  have hk₀' := mem_sq_pull.1 hk'
  rw [gw_sqIso w r y j k hj₀ hk₀, gw_sqIso w r y j' k' hj₀' hk₀', gm_sq_g M (r ≫ p) y j j' hj₀ hj₀',
    gm_sq_pull_g L f r y k k' hk₀ hk₀']
  have e := hw Y r y (j 0) (j' 0) (fun _ => k PUnit.unit 0) (fun _ => k' PUnit.unit 0) hj₀ hj₀'
    (mem_pull.2 hk₀) (mem_pull.2 hk₀')
  rw [gm_pull_g L f r y _ _ (mem_pull.2 hk₀) (mem_pull.2 hk₀')] at e
  rw [e, mul_pow, mul_pow, inv_pow]

end GlobalTheory.SqLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinityStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_finiteOrder_of_trivial_at_infinity : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), (∀ k, χ.inf k = 1) → ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n := by
  first | exact @GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one | exact GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one | (intros; apply GlobalTheory.Mem.FinOrder.finite_order_of_inf_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharTrivialOnCongruenceUnitIdelesStatement
section
open IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_trivial_on_congruenceUnitIdeles : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : Formalism.L2.Host.HChar L), (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) → ∀ a ∈ GlobalTheory.LevelChars.levSub L S N, ψ.1 a = 1 := by
  first | exact @GlobalTheory.LevelChars.LevTriv.levSub_triv | exact GlobalTheory.LevelChars.LevTriv.levSub_triv | (intros; apply GlobalTheory.LevelChars.LevTriv.levSub_triv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralOfDivisibleCharactersStatement
section
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_of_divisible_characters : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] (B₀ B₁ : Type) [CommRing B₀] [Algebra ↥(intO C) B₀] [Module.Finite ↥(intO C) B₀] [CommRing B₁] [Algebra C B₁] [Algebra ↥(intO C) B₁] [IsScalarTower ↥(intO C) C B₁] (j : B₀ →ₐ[↥(intO C)] B₁) (x : B₀) (q : ↥(intO C)), q ≠ 0 → (∀ χ : B₀ →ₐ[↥(intO C)] ↥(intO C), q ∣ χ x) → IsIntegral ↥(intO C) (((q : C)⁻¹) • j x) := by
  first | exact @GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul | exact GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul | (intros; apply GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaOfOfIsCharLab
section
noncomputable section

namespace GlobalTheory.Mem.TypePl

open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.MemN GlobalTheory.GLq GlobalTheory.GLp NumberField IsDedekindDomain
open scoped Pointwise

section Places

variable {R : Ranks} {H : Host R}

theorem isConjPl_iff_conjPl (w w' : PlE H) : IsConjPl H w w' ↔ Chr.ConjPl H.conj.toRingEquiv w w' :=
  (HalfPlaces.isConjPl_iff H w w').trans (Chr.conjPl_iff_smul H.conj w w').symm

theorem under_eq_iff (w w' : PlE H) : w'.under (𝓞 H.F) = w.under (𝓞 H.F) ↔ w' = w ∨ IsConjPl H w w' := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  rw [Chr.under_eq_iff_conjPl c hcm.rank hcm.ne, isConjPl_iff_conjPl]
  have e : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  rw [e]

theorem under_mem {p : ℕ} {w : PlE H} : w.under (𝓞 H.F) ∈ placesOver H.F p ↔ w ∈ placesOver H.E p := by
  show algebraMap (𝓞 H.F) (𝓞 H.E) ((p : ℕ) : 𝓞 H.F) ∈ w.asIdeal ↔ _
  rw [map_natCast]
  rfl

theorem exists_under (v : HeightOneSpectrum (𝓞 H.F)) : ∃ w : PlE H, w.under (𝓞 H.F) = v := by
  have := v.isPrime
  obtain ⟨⟨W, hW, hWv⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 H.E)))
  exact ⟨⟨W, hW, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot W⟩, HeightOneSpectrum.ext hWv.over.symm⟩

theorem div_over (P : PiBar H) {k : Fin 2} {w : PlE H} (h : P.Div k w) : w ∈ placesOver H.E (H.g k) := by
  have h1 := P.pb_over k
  rw [← (show w.under (𝓞 H.K) = P.pb k from h)] at h1
  have h2 : algebraMap (𝓞 H.K) (𝓞 H.E) ((H.g k : ℕ) : 𝓞 H.K) ∈ w.asIdeal := h1
  rwa [map_natCast] at h2

theorem div_iff_not_div (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    {w w' : PlE H} (hw : w ∈ placesOver H.E (H.g k)) (h : IsConjPl H w w') : P.Div k w ↔ ¬ P.Div k w' :=
  ((Chr.splitsC_main R H (H.g k) (H.g_prime k) hs w hw).2.2.2 (P.pb k) (P.pb_over k) w'
    ((isConjPl_iff_conjPl w w').1 h)).2

theorem not_isConjPl (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    {w w' : PlE H} (hw : P.Div k w) (hw' : P.Div k w') : ¬ IsConjPl H w w' :=
  fun h => (div_iff_not_div P hs (div_over P hw) h).1 hw hw'

def below {p : ℕ} {I : Type} (pl : I → PlE H) (h : ∀ i, pl i ∈ placesOver H.E p) (i : I) : placesOver H.F p :=
  ⟨(pl i).under (𝓞 H.F), under_mem.2 (h i)⟩

theorem below_injective {p : ℕ} {I : Type} (pl : I → PlE H) (h : ∀ i, pl i ∈ placesOver H.E p)
    (h1 : Function.Injective pl) (h2 : ∀ i j, ¬ IsConjPl H (pl i) (pl j)) : Function.Injective (below pl h) :=
  fun i j e => ((under_eq_iff (pl j) (pl i)).1 (congrArg Subtype.val e)).elim (fun e => h1 e) fun e => absurd e (h2 j i)

theorem card_placesOver {p : ℕ} (hp : p.Prime) (hs : (placesOver H.E p).ncard = Module.finrank ℚ H.E) :
    Nat.card (placesOver H.F p) = R.f := by
  obtain ⟨e, h, h1, h2, h3⟩ := HalfPlaces.exists_places_cover H hp hs
  have hb : Function.Bijective (below e h) := by
    refine ⟨below_injective e h h1 h2, fun v => ?_⟩
    obtain ⟨w, hw⟩ := exists_under v.1
    obtain ⟨i, hi⟩ := h3 w (under_mem.1 (hw ▸ v.2))
    exact ⟨i, Subtype.ext (((under_eq_iff (e i) w).2 hi).symm.trans hw)⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem below_bijective {p : ℕ} (hp : p.Prime) (hs : (placesOver H.E p).ncard = Module.finrank ℚ H.E)
    {I : Type} [Fintype I] (hI : Fintype.card I = R.f) (pl : I → PlE H) (h : ∀ i, pl i ∈ placesOver H.E p)
    (h1 : Function.Injective pl) (h2 : ∀ i j, ¬ IsConjPl H (pl i) (pl j)) : Function.Bijective (below pl h) := by
  have hc := card_placesOver hp hs
  haveI : Finite (placesOver H.F p) := Nat.finite_of_card_ne_zero (hc ▸ (GaloisStage.f_pos R).ne')
  exact (Nat.bijective_iff_injective_and_card _).2
    ⟨below_injective pl h h1 h2, by rw [hc, Nat.card_eq_fintype_card, hI]⟩

theorem existsUnique_div (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : ∃! w : PlE H, P.Div k w ∧ w.under (𝓞 H.F) = v := by
  obtain ⟨w, hw⟩ := exists_under v.1
  have hex : ∃ w : PlE H, P.Div k w ∧ w.under (𝓞 H.F) = v := by
    by_cases h : P.Div k w
    · exact ⟨w, h, hw⟩
    · obtain ⟨w', hw', -⟩ := Chr.existsUnique_conjPl H.conj.toRingEquiv w
      have hc := (isConjPl_iff_conjPl w w').2 hw'
      refine ⟨w', ?_, ((under_eq_iff w w').2 (Or.inr hc)).trans hw⟩
      by_contra h'
      exact h ((div_iff_not_div P hs (under_mem.1 (hw ▸ v.2)) hc).2 h')
  obtain ⟨a, ha⟩ := hex
  refine ⟨a, ha, fun b hb => ?_⟩
  exact ((under_eq_iff a b).1 (hb.2.trans ha.2.symm)).elim id fun e => absurd e (not_isConjPl P hs ha.1 hb.1)

def above (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : PlE H := (existsUnique_div P hs v).choose

theorem above_div (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : P.Div k (above P hs v) := (existsUnique_div P hs v).choose_spec.1.1

theorem above_under (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E)
    (v : placesOver H.F (H.g k)) : (above P hs v).under (𝓞 H.F) = v := (existsUnique_div P hs v).choose_spec.1.2

theorem above_injective (P : PiBar H) {k : Fin 2} (hs : (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    Function.Injective (above P hs) :=
  fun v v' e => Subtype.ext (by rw [← above_under P hs v, e, above_under])

end Places

section Labels

def labDat (g : ℕ) [Fact g.Prime] : LabelDatum g := (LabelModel.inhab g).some

variable {g : ℕ} [Fact g.Prime]

def charLab (L : LabelDatum g) (ω : (ZMod g)ˣ →* ℂˣ) : (ZMod g)ˣ :=
  Units.mk0 (GLp.Model.isCharLab_exists L ω).choose (GLp.Model.isCharLab_exists L ω).choose_spec.1

theorem isCharLab_charLab (L : LabelDatum g) (ω : (ZMod g)ˣ →* ℂˣ) : IsCharLab L ω (charLab L ω) :=
  (GLp.Model.isCharLab_exists L ω).choose_spec

theorem isCharLab_pow (L : LabelDatum g) (ω : (ZMod g)ˣ →* ℂˣ) (n : ℕ) :
    IsCharLab L (ω ^ n) ((charLab L ω ^ n : (ZMod g)ˣ) : ZMod g) := by
  refine ⟨Units.ne_zero _, fun u hu => ?_⟩
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, map_pow,
    (isCharLab_charLab L ω).2 u hu]

theorem orderOf_charLab (L : LabelDatum g) {ω : (ZMod g)ˣ →* ℂˣ} (h : Function.Injective ω) :
    orderOf (charLab L ω) = g - 1 := by
  obtain ⟨u, hu, ho⟩ := GLp.Model.exists_gen L
  let T : (ZMod g)ˣ →* ℂ := L.teich.comp ((algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).toMonoidHom.comp (Units.coeHom _))
  have hT : Function.Injective T := fun a b e => Units.ext <| (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)).injective
    (L.teich_inj _ _ (by simp) (by simp) e)
  have e : T (charLab L ω) = (ω u : ℂ) := ((isCharLab_charLab L ω).2 u hu).symm
  rw [← orderOf_injective T hT, e, orderOf_units, orderOf_injective ω h, ho]

theorem thetaOf_of_isCharLab (L : LabelDatum g) {χ : (ZMod g)ˣ →* ℂˣ} {c : ZMod g} (hc : IsCharLab L χ c)
    (a : (ZMod g)ˣ) : thetaOf L 1 (algebraMap (ZMod g) _ c) (algebraMap (ZMod g) _ (a : ZMod g)) = ((χ a : ℂˣ) : ℂ) := by
  obtain ⟨u, hu, ho⟩ := GLp.Model.exists_gen L
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, ho, Nat.card_eq_fintype_card, ZMod.card_units]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, u ^ m = a := mem_powers_iff_mem_zpowers.2 (htop ▸ Subgroup.mem_top a)
  have hcp : (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c) ^ (g ^ 1 - 1) = 1 := by
    rw [← map_pow, pow_one, ZMod.pow_card_sub_one_eq_one hc.1, map_one]
  rw [Units.val_pow_eq_pow_val, map_pow, hu, LabelModel.thetaOf_pow g L one_pos hcp, map_pow,
    Units.val_pow_eq_pow_val, hc.2 u hu]

end Labels

end GlobalTheory.Mem.TypePl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDeterminantKernelOpenAndFactorStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDeterminantKernel_open_and_factor : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), IsOpen (KD H : Set (Ideles H.E)) ∧ (∀ w y, infIdele H.E w y ∈ KD H) ∧ (∀ k : (H.F)ˣ, diagUnits H.E (upF H.F k) ∈ KD H) ∧ ∀ χ : HChar H.E, χ.TrivOn H.F → (∀ v, χ.TameAt v) → (∀ v, (∀ k, ¬ OverP H (H.g k) v) → χ.UnrAt v) → KD H ≤ (χ.1.comp (finPartI H.E)).ker := by
  first | exact @GlobalTheory.Mem.KerDet.kernel_open_and_factor | exact GlobalTheory.Mem.KerDet.kernel_open_and_factor | (intros; apply GlobalTheory.Mem.KerDet.kernel_open_and_factor <;> assumption)
end

