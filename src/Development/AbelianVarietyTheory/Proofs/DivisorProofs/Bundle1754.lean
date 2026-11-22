import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1727
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1721
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1722
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridConductorIdealCMIsCoprimeHalfDifferentStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridConductorIdealCM_isCoprime_halfDifferent : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L), Nat.Coprime D.host.pde (D.host.QS * D.host.q) → Nat.Coprime D.host.pde' (D.host.QS * D.host.q) → IsCoprime (condE P) D.host.𝔟 := by
  first | exact @GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_bb | exact GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_bb | (intros; apply GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_bb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridLocalTensorPlaces_over_split_places : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (w : HeightOneSpectrum (𝓞 D.host.E)), w ∈ locPl G t →
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F (w.under (𝓞 D.host.F))) := by
  first | exact @GlobalTheory.LocPlSplit.locPl_split | exact GlobalTheory.LocPlSplit.locPl_split | (intros; apply GlobalTheory.LocPlSplit.locPl_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridMovedTensorBoundedSupportLocallyConstant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

namespace GlobalTheory.MovedBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_le_inv_pow {ϖ : kˣ} (hϖ : IsUnif ϖ) (x : k) :
    ∃ n : ℕ, valuation k x ≤ (valuation k (ϖ : k) ^ n)⁻¹ := by
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hv : (valuation k x)⁻¹ ≠ 0 := by simp [hx]
  obtain ⟨m, hm⟩ := exists_pow_lt₀ h1 (Units.mk0 _ hv)
  have hu : 0 < valuation k (ϖ : k) ^ m := by
    rw [pos_iff_ne_zero]; simp
  refine ⟨m, ?_⟩
  have hx0 : 0 < valuation k x := by rw [pos_iff_ne_zero]; simp [hx]
  exact (le_inv_comm₀ hu hx0).1 (by simpa using hm.le)

theorem inv_pow_mono {ϖ : kˣ} (hϖ : IsUnif ϖ) {n N : ℕ} (h : n ≤ N) :
    (valuation k (ϖ : k) ^ n)⁻¹ ≤ (valuation k (ϖ : k) ^ N)⁻¹ := by
  have h1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hu : 0 < valuation k (ϖ : k) ^ N := by rw [pos_iff_ne_zero]; simp
  exact inv_anti₀ hu (pow_le_pow_right_of_le_one' h1.le h)

theorem exists_uniform {α : Type*} (s : Finset α) (P : α → ℕ → Prop)
    (hP : ∀ a n N, n ≤ N → P a n → P a N) (h : ∀ a ∈ s, ∃ n, P a n) : ∃ n, ∀ a ∈ s, P a n := by
  classical
  choose f hf using h
  exact ⟨s.attach.sup fun a => f a.1 a.2, fun a ha =>
    hP _ _ _ (Finset.le_sup (f := fun a : s => f a.1 a.2) (Finset.mem_attach s ⟨a, ha⟩)) (hf a ha)⟩

theorem exists_matrix_bound {ϖ : kˣ} (hϖ : IsUnif ϖ) {m n : Type*} [Fintype m] [Fintype n] (P : Matrix m n k) :
    ∃ N : ℕ, ∀ r s, valuation k (P r s) ≤ (valuation k (ϖ : k) ^ N)⁻¹ := by
  obtain ⟨N, hN⟩ := exists_uniform (Finset.univ : Finset (m × n))
    (fun rs N => valuation k (P rs.1 rs.2) ≤ (valuation k (ϖ : k) ^ N)⁻¹)
    (fun _ _ _ h h' => h'.trans (inv_pow_mono hϖ h)) (fun rs _ => exists_le_inv_pow hϖ _)
  exact ⟨N, fun r s => hN (r, s) (Finset.mem_univ _)⟩

theorem val_mul_mul_le {a b c d : Type*} [Fintype b] [Fintype c] (P : Matrix a b k) (X : Matrix b c k)
    (Q : Matrix c d k) (p x q : ValueGroupWithZero k) (hP : ∀ r s, valuation k (P r s) ≤ p)
    (hX : ∀ r s, valuation k (X r s) ≤ x) (hQ : ∀ r s, valuation k (Q r s) ≤ q) (r : a) (s : d) :
    valuation k ((P * X * Q) r s) ≤ p * x * q := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, Matrix.mul_apply]
  refine mul_le_mul' (Valuation.map_sum_le _ fun i _ => ?_) (hQ _ _)
  rw [map_mul]
  exact mul_le_mul' (hP _ _) (hX _ _)

end GlobalTheory.MovedBound

namespace GlobalTheory.MovedBound

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_unitsPow_inv (ϖ : kˣ) (n : ℕ) :
    valuation k (((ϖ ^ n)⁻¹ : kˣ) : k) = (valuation k (ϖ : k) ^ n)⁻¹ := by
  simp [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]

theorem val_unitsPow (ϖ : kˣ) (n : ℕ) :
    valuation k ((ϖ ^ n : kˣ) : k) = valuation k (ϖ : k) ^ n := by
  simp [Units.val_pow_eq_pow_val, map_pow]

end GlobalTheory.MovedBound

open GlobalTheory.MovedBound in

theorem GlobalTheory.MovedBound.moved_bounded_locConst : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup), IsUnif ϖ → G.IsTensor ϖ e (oppositePath G.m) T → ∃ n : ℕ, (∀ z : G.Args, moved G keep g T z ≠ 0 → ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (z b r s) ≤ valuation k (((ϖ ^ n)⁻¹ : kˣ) : k)) ∧ ∀ z δ : G.Args, (∀ b ∈ oppositePath G.m, ∀ r s, valuation k (δ b r s) ≤ valuation k ((ϖ ^ n : kˣ) : k)) → moved G keep g T (z + δ) = moved G keep g T z := by
  intro k _ _ _ _ G ϖ e T keep g hϖ hT
  classical
  set u := valuation k (ϖ : k) with hu_def
  have hu0 : u ≠ 0 := by simp [u]
  have hu1 : u ≤ 1 := (hϖ ▸ uniformizer_lt_one).le
  let A : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.tgt)) k := fun b => ((Assignment.one.read (g b.tgt))⁻¹).val
  let Ai : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.tgt)) k := fun b => (Assignment.one.read (g b.tgt)).val
  let B : ∀ b : Edge, Matrix (Fin (G.rank b.src)) (Fin (G.rank b.src)) k := fun b => (Assignment.one.read (g b.src)).val
  let Bi : ∀ b : Edge, Matrix (Fin (G.rank b.src)) (Fin (G.rank b.src)) k := fun b => ((Assignment.one.read (g b.src))⁻¹).val
  obtain ⟨n0, hn0⟩ := exists_uniform (oppositePath G.m).toFinset
    (fun b N => (∀ r s, valuation k (A b r s) ≤ (u ^ N)⁻¹) ∧ (∀ r s, valuation k (Ai b r s) ≤ (u ^ N)⁻¹) ∧
      (∀ r s, valuation k (B b r s) ≤ (u ^ N)⁻¹) ∧ (∀ r s, valuation k (Bi b r s) ≤ (u ^ N)⁻¹))
    (fun _ _ _ h ⟨h1, h2, h3, h4⟩ => ⟨fun r s => (h1 r s).trans (inv_pow_mono hϖ h),
      fun r s => (h2 r s).trans (inv_pow_mono hϖ h), fun r s => (h3 r s).trans (inv_pow_mono hϖ h),
      fun r s => (h4 r s).trans (inv_pow_mono hϖ h)⟩)
    (fun b _ => by
      obtain ⟨n1, h1⟩ := exists_matrix_bound hϖ (A b)
      obtain ⟨n2, h2⟩ := exists_matrix_bound hϖ (Ai b)
      obtain ⟨n3, h3⟩ := exists_matrix_bound hϖ (B b)
      obtain ⟨n4, h4⟩ := exists_matrix_bound hϖ (Bi b)
      refine ⟨n1 + n2 + n3 + n4, fun r s => (h1 r s).trans (inv_pow_mono hϖ (by omega)),
        fun r s => (h2 r s).trans (inv_pow_mono hϖ (by omega)), fun r s => (h3 r s).trans (inv_pow_mono hϖ (by omega)),
        fun r s => (h4 r s).trans (inv_pow_mono hϖ (by omega))⟩)
  have hmv : ∀ x : G.Args, ∀ b, G.moveArgs .one g x b = A b * x b * B b := fun _ _ => rfl
  refine ⟨2 * n0 + e, ?_, ?_⟩
  · intro z hz b hb r s
    have hT0 : T (G.moveArgs .one g z) ≠ 0 := by
      intro h0; apply hz; simp [moved, Grid.pathAct, h0]
    have hint : G.moveArgs .one g z b ∈ matLat _ (stdLat k _) := by
      by_contra hc; exact hT0 (hT.2.1 _ b hb hc)
    have hint' := mem_matLat_stdLat.1 hint
    have hz' : z b = Ai b * G.moveArgs .one g z b * Bi b := by
      simp [hmv, A, Ai, B, Bi, ← Matrix.mul_assoc]
    obtain ⟨-, h2, -, h4⟩ := hn0 b (List.mem_toFinset.2 hb)
    rw [hz', val_unitsPow_inv]
    refine (val_mul_mul_le _ _ _ _ 1 _ h2 (fun r s => (hint' r s)) h4 r s).trans ?_
    rw [mul_one, ← mul_inv, ← pow_add]
    exact inv_pow_mono hϖ (by omega)
  · intro z δ hδ
    let δ' : G.Args := fun b => if b ∈ oppositePath G.m then G.moveArgs .one g δ b else 0
    have h1 : T (G.moveArgs .one g (z + δ)) = T (G.moveArgs .one g z + δ') := by
      refine hT.1 fun b hb => ?_
      simp only [Set.mem_setOf_eq] at hb
      simp [δ', hb, hmv, Matrix.mul_add, Matrix.add_mul]
    have h2 : T (G.moveArgs .one g z + δ') = T (G.moveArgs .one g z) := by
      refine hT.2.2 _ _ fun b => ?_
      by_cases hb : b ∈ oppositePath G.m
      · simp only [δ', hb, if_true]
        obtain ⟨h1, -, h3, -⟩ := hn0 b (List.mem_toFinset.2 hb)
        have hd : ∀ r s, valuation k (δ b r s) ≤ u ^ (2 * n0 + e) := fun r s => by
          rw [← val_unitsPow]; exact hδ b hb r s
        have hbd : ∀ r s, valuation k (G.moveArgs .one g δ b r s) ≤ u ^ e := fun r s => by
          rw [hmv]
          refine (val_mul_mul_le _ _ _ _ _ _ h1 hd h3 r s).trans (le_of_eq ?_)
          rw [show 2 * n0 + e = n0 + (n0 + e) by ring, pow_add, pow_add]
          field_simp
        rw [mem_matLat]
        intro i
        rw [mem_smul_lat, mem_stdLat]
        intro j
        rw [Valuation.mem_integer_iff]
        simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, Matrix.row_apply]
        rw [map_mul, val_unitsPow_inv]
        calc (u ^ e)⁻¹ * valuation k (G.moveArgs .one g δ b i j) ≤ (u ^ e)⁻¹ * u ^ e := mul_le_mul' le_rfl (hbd i j)
          _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ hu0)
      · simp only [δ', hb, if_false]
        exact zero_mem _
    simp only [moved, Grid.pathAct, h1, h2]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeSquaringCotangentEqTwo
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

private theorem eta_comp_mul_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : η[G] ≫ (𝟙 G * 𝟙 G) = η[G] := by
  rw [Hom.mul_def, ← Category.assoc, comp_lift, Category.comp_id]
  simpa using lift_comp_one_left (𝟙 _) η[G]

private theorem unitSec_comp_sqr {S : Scheme.{0}} (G : Over S) [GrpObj G] : unitSec G ≫ sqr G = unitSec G :=
  congrArg (·.left) (eta_comp_mul_self G)

theorem sqr_sub_two_mem : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiSeparated G.hom → ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2 := by
  intro S G _ hqs s π ε m hd f hf
  haveI := hqs
  obtain ⟨hπ, hε, hm⟩ := GlobalTheory.T.groupSchemeUnitStalkData_germ S G s π ε m hd
  have he : unitSec G ≫ G.hom = 𝟙 S := sec_hom η[G]
  obtain ⟨U₀, hU₀, g, rfl⟩ := G.left.presheaf.germ_exist f
  have hsq : sqr G (unitSec G s) = unitSec G s := by rw [← Scheme.Hom.comp_apply, unitSec_comp_sqr]
  have hb : G.hom (unitSec G s) = s := by rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨U₁, hU₁, hs₁, -⟩ := QCoh.exists_affine_mem_le (U := (⊤ : S.Opens)) s trivial
  obtain ⟨W₁, hW₁, hx₁, k₁⟩ := QCoh.exists_affine_mem_le
    (U := U₀ ⊓ sqr G ⁻¹ᵁ U₀ ⊓ G.hom ⁻¹ᵁ U₁) (unitSec G s)
    ⟨⟨hU₀, show sqr G (unitSec G s) ∈ U₀ by rw [hsq]; exact hU₀⟩,
      show G.hom (unitSec G s) ∈ U₁ by rw [hb]; exact hs₁⟩
  obtain ⟨U, hsU, -, -, c⟩ := GlobalTheory.Conormal.exists_isChart_inf he hU₁ hW₁ (k₁.trans inf_le_right) hx₁
    (show s ∈ (⊤ : S.Opens) from trivial)
  have kW : W₁ ⊓ G.hom ⁻¹ᵁ U ≤ U₀ := inf_le_left.trans (k₁.trans (inf_le_left.trans inf_le_left))
  have kS : W₁ ⊓ G.hom ⁻¹ᵁ U ≤ sqr G ⁻¹ᵁ U₀ :=
    inf_le_left.trans (k₁.trans (inf_le_left.trans inf_le_right))
  have hxW : unitSec G s ∈ W₁ ⊓ G.hom ⁻¹ᵁ U := c.le hsU
  have hU0 : U ≤ unitSec G ⁻¹ᵁ U₀ := c.le.trans ((unitSec G).preimage_mono kW)

  have a1 := cotMap_d (𝟙 G * 𝟙 G) (eta_comp_mul_self G) hU0 c.le kS g
  have a2 := cotMap_d (𝟙 G) (Category.comp_id _) hU0 c.le kW g
  have hmul := cotMap_mul (x := 𝟙 G) (y := 𝟙 G) (Category.comp_id η[G]) (Category.comp_id η[G]) (eta_comp_mul_self G)
  have key : GlobalTheory.Conormal.d he c.le ((sqr G).appLE U₀ _ kS g) =
      GlobalTheory.Conormal.d he c.le (resG G.left kW g) + GlobalTheory.Conormal.d he c.le (resG G.left kW g) := by
    have := congrArg (fun φ => φ.app U (GlobalTheory.Conormal.d he hU0 g)) hmul
    simp only at this
    exact (a1.symm.trans this).trans (congrArg₂ (· + ·) a2 a2)
  letI := c.algebra
  let h : Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) := (sqr G).appLE U₀ _ kS g - (resG G.left kW g + resG G.left kW g)
  have hz : AugCot.d (c.aug he) h = 0 := (c.augCotEquiv he).injective (by
    rw [c.augCotEquiv_d he, map_zero, map_sub, map_add, key, sub_self])
  rw [AugCot.d_eq_zero_iff] at hz
  let gW := G.left.presheaf.germ (W₁ ⊓ G.hom ⁻¹ᵁ U) (unitSec G s) hxW
  have g1 : gW ((sqr G).appLE U₀ _ kS g) = m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) :=
    (hm U₀ hU₀ _ hxW kS g).symm
  have g2 : gW (resG G.left kW g) = G.left.presheaf.germ U₀ (unitSec G s) hU₀ g :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gh : gW h = m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) -
      2 * G.left.presheaf.germ U₀ (unitSec G s) hU₀ g := by
    simp only [h, map_sub, map_add, g1, g2, two_mul]
  have hf0 : ε (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) = 0 := hf
  have hker : ∀ x, c.aug he x = 0 → ε (gW x) = 0 := by
    intro x hx
    have hx' : (unitSec G).appLE _ U c.le x = 0 := hx
    rw [hε _ hxW U hsU c.le x, hx', map_zero]
  have hmap : ∀ y ∈ RingHom.ker (c.aug he) ^ 2, gW y ∈ RingHom.ker ε ^ 2 := by
    intro y hy
    have := Ideal.mem_map_of_mem (ConcreteCategory.hom gW) hy
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (RingHom.mem_ker.2 (hker x (RingHom.mem_ker.1 hx)))) 2 this
  have hεm : ε (m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g)) = 0 := by
    rw [← g1, hε _ hxW U hsU c.le, GlobalTheory.Conormal.appLE_appLE (unitSec_comp_sqr G) kS c.le hU0,
      ← hε U₀ hU₀ U hsU hU0 g, hf0]
  have hεh : ε (gW h) = 0 := by rw [gh, map_sub, map_mul, hεm, hf0, mul_zero, sub_zero]
  have halg : gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) = 0 := by
    have e1 : gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) =
        π (S.presheaf.germ U s hsU (c.aug he h)) := (hπ U hsU _ hxW c.le_base _).symm
    have e2 : S.presheaf.germ U s hsU (c.aug he h) = ε (gW h) := (hε _ hxW U hsU c.le h).symm
    rw [e1, e2, hεh, map_zero]
  rw [← gh, show gW h = gW (h - algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) +
      gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) by rw [← map_add, sub_add_cancel],
    halg, add_zero]
  exact hmap _ hz
end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundDomainLeCardMulOfTranslateCoverStatement
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_fundDomain_le_card_mul_of_translateCover : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N Λ : Subgroup G) [Countable Λ] (ν : Measure N) (DN : Set N) (b : G) (κ : ℝ≥0∞) (V : Set G) (Y : Finset G), ν.IsHaarMeasure → IsFundamentalDomain (Λ.subgroupOf N) DN ν → IsCompact V → (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ u : N, f (b * u * b⁻¹) ∂ν = κ * ∫⁻ u : N, f u ∂ν) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * b⁻¹ * w * b) → ν DN ≤ Y.card * (κ * ν {u | (u : G) ∈ V}) := by
  first | exact @GlobalTheory.SphEis.measure_fund_le_card_mul_of_cover | exact GlobalTheory.SphEis.measure_fund_le_card_mul_of_cover | (intros; apply GlobalTheory.SphEis.measure_fund_le_card_mul_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraCapelliUniformDiagonalBlocksStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandra_capelli_uniform_diagonalBlocks : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (a r : ℕ) (hr : r ≤ a) (X : Fin a → Fin a → Module.End ℂ M), Formalism.REAL.GlRel X → ∀ M' K : Submodule ℂ M, (∀ i j, ∀ x ∈ M', X i j x ∈ M') → (∀ i j : Fin a, (i : ℕ) < r → r ≤ (j : ℕ) → ∀ x ∈ M', X i j x ∈ K) → (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) → ∀ x ∈ K, X i j x ∈ K) → ∀ Q : ℂ → Polynomial ℂ, (∀ u, Q u ≠ 0) → ∃ q : ℂ → Polynomial ℂ, (∀ u, q u ≠ 0) ∧ ∀ v ∈ M', (∀ u, Polynomial.aeval (Formalism.REAL.qdet X u) (Q u) v = 0) → ∀ u, Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin r => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inl p'))) u) (q u) v ∈ K ∧ Polynomial.aeval (Formalism.REAL.qdet (fun p p' : Fin (a - r) => X (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p)) (GlobalTheory.LeviGA.blkEquiv hr (Sum.inr p'))) u) (q u) v ∈ K := by
  first | exact @GlobalTheory.LeviHC.CapAlg.capalg | exact GlobalTheory.LeviHC.CapAlg.capalg | (intros; apply GlobalTheory.LeviHC.CapAlg.capalg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExpStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasArchimedeanCharExponents_conj_of_hasInfExp : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (a : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D c τ (a τ)) →
    ∀ (τf : InfinitePlace D.host.F → D.what₂.Tau)
    (hτf : ∀ w, ((starRingEnd ℂ).comp (tauE D (τf w))).comp (algebraMap D.host.F D.host.E) = w.embedding),
    ∃ m : InfinitePlace D.host.F → ℤ,
      HasExp (fun w => ⟨(starRingEnd ℂ).comp (tauE D (τf w)), hτf w⟩) c m ∧ ∀ w, (m w : ℚ) = -2 * a (τf w) := by
  first | exact @GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp | exact GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp | (intros; apply GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasCompactSupport_finprod_schwartzBruhat_finiteAdeles : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    HasCompactSupport (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) := by
  first | exact @GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod | exact GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod | (intros; apply GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureComplementHyperbolicPlaneStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasHermitianSignature_complement_hyperbolicPlane : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (r s : ℕ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    HasSig M r s → HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) := by
  first | exact @GlobalTheory.PlaneSig.hasSig_complement_plane | exact GlobalTheory.PlaneSig.hasSig_complement_plane | (intros; apply GlobalTheory.PlaneSig.hasSig_complement_plane <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureHyperbolicPlaneOrthCompleme
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section

namespace GlobalTheory.PlaneSkewSig

open Matrix

theorem conjTranspose_eq_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : Mᴴ = M := by
  obtain ⟨hn, A, hA⟩ := h
  set D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have hDD : D * D = 1 := by
    simp [hD, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hDh : Dᴴ = D := by
    simp [hD, Matrix.fromBlocks_conjTranspose]
  have hAh : Aᵀ * Mᴴ * A.map star = D := by
    have a1 : (A.map star)ᴴ = Aᵀ := by ext; simp [conjTranspose_apply]
    have a2 : (Aᵀ)ᴴ = A.map star := by ext; simp [conjTranspose_apply]
    have : (Aᵀ * M * A.map star)ᴴ = Aᵀ * Mᴴ * A.map star := by
      rw [conjTranspose_mul, conjTranspose_mul, a1, a2, Matrix.mul_assoc]
    rw [← this, hA, hDh]
  have e : Fin r ⊕ Fin s ≃ Fin n := (finSumFinEquiv).trans (finCongr hn)
  have k1 : M * (A.map star * D * Aᵀ) = 1 := by
    have : Aᵀ * (M * A.map star * D) = 1 := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hDD]
    have := (Matrix.mul_eq_one_comm_of_equiv e).1 this
    simpa [Matrix.mul_assoc] using this
  have k2 : Mᴴ * (A.map star * D * Aᵀ) = 1 := by
    have : Aᵀ * (Mᴴ * A.map star * D) = 1 := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAh, hDD]
    have := (Matrix.mul_eq_one_comm_of_equiv e).1 this
    simpa [Matrix.mul_assoc] using this
  have k3 : (A.map star * D * Aᵀ) * M = 1 := mul_eq_one_comm.1 k1
  calc Mᴴ = Mᴴ * ((A.map star * D * Aᵀ) * M) := by rw [k3, Matrix.mul_one]
    _ = M := by rw [← Matrix.mul_assoc, k2, Matrix.one_mul]

theorem exists_left_inverse {m k : ℕ} (ι : Matrix (Fin m) (Fin k) ℂ) (h : Function.Injective ι.mulVec) :
    ∃ P : Matrix (Fin k) (Fin m) ℂ, P * ι = 1 := by
  have hker : LinearMap.ker (Matrix.mulVecLin ι) = ⊥ := LinearMap.ker_eq_bot.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] at this
  have e : LinearMap.toMatrix' ι.mulVecLin = ι := LinearMap.toMatrix'_toLin' ι
  rwa [e] at this

theorem transpose_mulVec_eq_zero {m k : ℕ} (ι : Matrix (Fin m) (Fin k) ℂ) (v : Fin m → ℂ)
    (h : ∀ u, (ι *ᵥ u) ⬝ᵥ v = 0) : ιᵀ *ᵥ v = 0 := by
  ext j
  have := h (Pi.single j 1)
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, single_dotProduct] at this
  simpa using this

theorem hasSig_complement : ∀ (n₁ : ℕ) (M : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ) (X Y : Fin (n₁ + 2) → ℂ)
    (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) ℂ) (r s : ℕ), HasSig M r s → 1 ≤ r → 1 ≤ s →
    X ⬝ᵥ M *ᵥ star X = 0 → Y ⬝ᵥ M *ᵥ star Y = 0 → X ⬝ᵥ M *ᵥ star Y ≠ 0 →
    (∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star Y = 0) → Function.Injective ι.mulVec →
    HasSig (ιᵀ * M * ι.map star) (r - 1) (s - 1) := by
  intro n₁ M X Y ι r s hs _ _ hXX hYY hXY horth hinj
  set c := X ⬝ᵥ M *ᵥ star Y with hc
  set Y' : Fin (n₁ + 2) → ℂ := (star c)⁻¹ • Y with hY'
  have hsY : star Y' = c⁻¹ • star Y := by
    rw [hY', star_smul, star_inv₀, star_star]
  have hXY' : X ⬝ᵥ M *ᵥ star Y' = 1 := by
    rw [hsY, mulVec_smul, dotProduct_smul, smul_eq_mul, ← hc, inv_mul_cancel₀ hXY]
  have hYY' : Y' ⬝ᵥ M *ᵥ star Y' = 0 := by
    rw [hsY, mulVec_smul, dotProduct_smul, hY', smul_dotProduct, hYY]; simp
  have hιX : ιᵀ *ᵥ (M *ᵥ star X) = 0 := transpose_mulVec_eq_zero ι _ fun u => (horth u).1
  have hιY : ιᵀ *ᵥ (M *ᵥ star Y') = 0 := by
    rw [hsY, mulVec_smul, mulVec_smul, transpose_mulVec_eq_zero ι _ fun u => (horth u).2, smul_zero]
  obtain ⟨P, hP⟩ := exists_left_inverse ι hinj
  exact GlobalTheory.PlaneSig.hasSig_complement_plane (n₁ + 2) n₁ M X Y' ι P r s rfl (conjTranspose_eq_of_hasSig hs)
    hXX hYY' hXY' hιX hιY hP hs

end GlobalTheory.PlaneSkewSig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignaturePosSmulBlockDiagonalReindexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasHermitianSignature_pos_smul_blockDiagonalReindexed : ∀ {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) (GA : Matrix (Fin a) (Fin a) ℂ) (GB : Matrix (Fin b) (Fin b) ℂ) {pa qa pb qb : ℕ} {κ : ℝ},
    0 < κ → Formalism.UG.HasSignature GA pa qa → Formalism.UG.HasSignature GB pb qb →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig ((κ : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e GA GB) (pa + pb) (qa + qb) := by
  first | exact @GlobalTheory.SigBlockSum.hasSig_smul_blk | exact GlobalTheory.SigBlockSum.hasSig_smul_blk | (intros; apply GlobalTheory.SigBlockSum.hasSig_smul_blk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPotentialGoodReductionOfFiniteImageInertiaStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasPotentialGoodReduction_of_finite_image_inertia_alt : NeronOggShafarevichSt → ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite → HasPotentialGoodReduction R K A := by
  first | exact @GlobalTheory.hasPotentialGoodReduction_of_finite_image_inertia | exact GlobalTheory.hasPotentialGoodReduction_of_finite_image_inertia | (intros; apply GlobalTheory.hasPotentialGoodReduction_of_finite_image_inertia <;> assumption)
end

