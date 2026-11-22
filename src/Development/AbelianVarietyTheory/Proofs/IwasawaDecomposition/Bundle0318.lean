import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0294
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakCompatibilityOfRealRowSideAdelicChain
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipMulMemCell
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.IwaCell

variable {k : Type} [Field k] {m : ℕ}

def tD (ϖ : kˣ) (a : Fin m → ℤ) : GL (Fin m) k := diagT k (Fin m) fun i => ϖ ^ a i

variable [ValuativeRel k]

def cell (ϖ : kˣ) (a : Fin m → ℤ) : Set (GL (Fin m) k) :=
  {g | ∃ u ∈ unipB k (Fin m), ∃ κ ∈ KO k (Fin m), g = u * tD ϖ a * κ}

variable (m) in

def wt (a : Fin m → ℤ) : ℤ := ∑ i : Fin m, ((m : ℤ) - 1 - 2 * (i : ℕ)) * a i

theorem val_tD (ϖ : kˣ) (a : Fin m → ℤ) : (tD ϖ a).val = Matrix.diagonal fun i => ((ϖ ^ a i : kˣ) : k) :=
  val_diagT k _

theorem tD_add (ϖ : kˣ) (a b : Fin m → ℤ) : tD ϖ (a + b) = tD ϖ a * tD ϖ b := by
  rw [tD, tD, tD, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

theorem mul_mem_cell {ϖ : kˣ} {a : Fin m → ℤ} {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) {κ : GL (Fin m) k}
    (hκ : κ ∈ KO k (Fin m)) : u * tD ϖ a * κ ∈ cell ϖ a := ⟨u, hu, κ, hκ, rfl⟩

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem tD_zero (ϖ : kˣ) : tD ϖ (0 : Fin m → ℤ) = 1 := by
  rw [tD, ← map_one (diagT k (Fin m))]
  congr 1
  funext i
  simp

theorem tD_neg (ϖ : kˣ) (a : Fin m → ℤ) : tD ϖ (-a) = (tD ϖ a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← tD_add, neg_add_cancel, tD_zero])

theorem diag_entry (ϖ : kˣ) (s t : Fin m → ℤ) {w : GL (Fin m) k} (hw : w ∈ unipB k (Fin m)) (i : Fin m) :
    (tD ϖ s * w * tD ϖ t).val i i = ((ϖ ^ (s i + t i) : kˣ) : k) := by
  rw [Units.val_mul, Units.val_mul, val_tD, val_tD, Matrix.mul_diagonal, Matrix.diagonal_mul, ((mem_unipB k).1 hw).2 i,
    mul_one, _root_.zpow_add, Units.val_mul]

theorem ord_zpow (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o x n
  have h2 : Multiplicative.toAdd (o (x ^ n)) = Multiplicative.toAdd (o x ^ n) := congrArg _ h
  simpa [o, mul_comm] using h2

theorem eq_of_mem_cell {ϖ : kˣ} (hϖ : ord k ϖ = 1) {a b : Fin m → ℤ} {g : GL (Fin m) k} (ha : g ∈ cell ϖ a)
    (hb : g ∈ cell ϖ b) : a = b := by
  obtain ⟨u, hu, κ, hκ, rfl⟩ := ha
  obtain ⟨u', hu', κ', hκ', e⟩ := hb
  have hw : u'⁻¹ * u ∈ unipB k (Fin m) := mul_mem (inv_mem hu') hu
  have hx : tD ϖ (-b) * (u'⁻¹ * u) * tD ϖ a = κ' * κ⁻¹ := by
    rw [tD_neg]
    calc (tD ϖ b)⁻¹ * (u'⁻¹ * u) * tD ϖ a = (u' * tD ϖ b)⁻¹ * (u * tD ϖ a * κ) * κ⁻¹ := by group
      _ = (u' * tD ϖ b)⁻¹ * (u' * tD ϖ b * κ') * κ⁻¹ := by rw [e]
      _ = κ' * κ⁻¹ := by group
  have hxi : (tD ϖ (-b) * (u'⁻¹ * u) * tD ϖ a)⁻¹ = tD ϖ (-a) * (u'⁻¹ * u)⁻¹ * tD ϖ b := by
    simp only [tD_neg, _root_.mul_inv_rev, inv_inv]; group
  have hK := (GlobalTheory.SplitFlip.mem_KO_iff _).1 (hx ▸ mul_mem hκ' (inv_mem hκ))
  funext i
  have h1 := hK.1 i i
  have h2 := hK.2 i i
  rw [diag_entry ϖ _ _ hw] at h1
  rw [hxi, diag_entry ϖ _ _ (inv_mem hw)] at h2
  simp only [Pi.neg_apply] at h1 h2
  set y : kˣ := ϖ ^ (-b i + a i)
  have h2' : ((y⁻¹ : kˣ) : k) ∈ 𝒪[k] := by
    have : (ϖ ^ (-a i + b i) : kˣ) = y⁻¹ := by rw [← _root_.zpow_neg]; congr 1; ring
    rwa [this] at h2
  have v1 : valuation k (y : k) ≤ 1 := h1
  have v2 : valuation k ((y⁻¹ : kˣ) : k) ≤ 1 := h2'
  have hv : valuation k (y : k) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀] at v2
    have hpos : 0 < valuation k (y : k) := zero_lt_iff.2 (by simp)
    exact le_antisymm v1 ((inv_le_one₀ hpos).1 v2)
  have h3 := ord_eq_zero hv
  rw [ord_zpow, hϖ, mul_one] at h3
  omega

end GlobalTheory.IwaCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipRadStdBlocksTwoNeBot
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

open GlobalTheory.SmGL in

theorem unipRad_stdBlocks_two_ne_bot : ∀ (R : Type) [CommRing R] [Nontrivial R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n), 0 < a → 0 < b → unipRad R (stdBlocks ![a, b] h) ≠ ⊥ := by
  intro R _ _ n a b h ha hb
  set e := stdBlocks ![a, b] h with he
  let i : Fin n := e ⟨0, ⟨0, by simpa using ha⟩⟩
  let j : Fin n := e ⟨1, ⟨0, by simpa using hb⟩⟩
  have hij : i ≠ j := by
    intro hh
    have := congrArg Sigma.fst (e.injective hh)
    simp at this
  let g : GL (Fin n) R :=
    ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
      by
        show Matrix.transvection i j (1 : R) * Matrix.transvection i j (-1) = 1
        rw [Matrix.transvection_mul_transvection_same i j hij]; simp,
      by
        show Matrix.transvection i j (-1 : R) * Matrix.transvection i j 1 = 1
        rw [Matrix.transvection_mul_transvection_same i j hij]; simp⟩
  have hg : (g : Matrix (Fin n) (Fin n) R) = 1 + Matrix.single i j 1 := rfl
  have hmem : g ∈ unipRad R e := by
    rw [mem_unipRad]
    refine ⟨?_, ?_⟩
    · rw [mem_parab]
      intro p q hpq
      have hne : p ≠ q := by rintro rfl; exact lt_irrefl _ hpq
      rw [hg, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
      by_cases hp : p = i
      · by_cases hq : q = j
        · subst hp; subst hq
          rw [blk_apply, blk_apply] at hpq
          exact absurd hpq (by decide)
        · rw [Matrix.single_apply, if_neg]
          rintro ⟨_, h'⟩; exact hq h'.symm
      · rw [Matrix.single_apply, if_neg]
        rintro ⟨h', _⟩; exact hp h'.symm
    · intro c x y
      rw [hg, Matrix.add_apply]
      have h1 : (1 : Matrix (Fin n) (Fin n) R) (e ⟨c, x⟩) (e ⟨c, y⟩) = (1 : Matrix _ _ R) x y := by
        by_cases hxy : x = y
        · subst hxy; simp
        · rw [Matrix.one_apply_ne, Matrix.one_apply_ne hxy]
          intro hh
          have := e.injective hh
          simp at this
          exact hxy this
      rw [h1]
      have h2 : Matrix.single i j (1 : R) (e ⟨c, x⟩) (e ⟨c, y⟩) = 0 := by
        rw [Matrix.single_apply]
        split_ifs with hh
        · obtain ⟨h3, h4⟩ := hh
          have e3 := congrArg Sigma.fst (e.injective h3)
          have e4 := congrArg Sigma.fst (e.injective h4)
          simp only at e3 e4
          rw [← e3] at e4
          exact absurd e4 (by decide)
        · rfl
      rw [h2, add_zero]
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  have := congrArg (fun u : GL (Fin n) R => (u : Matrix (Fin n) (Fin n) R) i j) hmem
  simp [hg, Matrix.one_apply_ne hij] at this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRootExchangeMirrorIdentityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRootExchange_mirror_identity : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (ε : AE D), IsSplitIdem D ε → ∀ (j : Fin d.ρ) (t₀ t : Fin A.rank → AE D) (b₀ k : GA D B), ε • t₀ = t₀ → cA D ε • t = t → IsK B (vecA B (dual d j.succ)) (iA ι t₀) b₀ → IsK B (vecA B (d.e j)) (iA ι t) k → SuppAt ε B k ∧ ∀ b ∈ ExGe d ε (j.1 + 2), b * (b₀ * k * b₀⁻¹) * b⁻¹ ∈ d.N ∧ SuppAt ε B (b * (b₀ * k * b₀⁻¹) * b⁻¹) ∧ d.psiN ψ (b * (b₀ * k * b₀⁻¹) * b⁻¹) = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D d.θ * hA A t₀ t)) := by
  first | exact @GlobalTheory.RootExch.Mirror.mirror | exact GlobalTheory.RootExch.Mirror.mirror | (intros; apply GlobalTheory.RootExch.Mirror.mirror <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.OfModel

section Values

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h]
  exact congrArg _ (IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec)

theorem valAt_mul {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem valAt_fnOf {U : Z.Opens} (hU : below y ∈ U) (h : ⊤ ≤ y ⁻¹ᵁ U) (a : Γ(Z, U)) :
    valAt y (fnOf U (gen_mem hU) a) =
      (y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom a := by
  have e : Z.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of K) y =
      y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [← algebraMap_germ hU, valAt_algebraMap, ← e]
  rfl

end Values

theorem ext_unique {K R : Type} [Field K] [CommRing R] (O : ValuationSubring K) {X : Scheme.{0}} (p : X ⟶ Sp R)
    [IsSeparated p] {b b' : Sp O ⟶ X} (h : spMap O.subtype ≫ b = spMap O.subtype ≫ b') : b = b' := by
  have : IsDominant (spMap O.subtype) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective).le.trans bot_le)⟩
  refine ext_of_isDominant_of_isSeparated p (ext_of_isDominant (spMap O.subtype) ?_) _ h
  rw [← Category.assoc, h, Category.assoc]

theorem eval_pull {K O : Type} [CommRing K] [CommRing O] (φ : O →+* K) {X Z : Scheme.{0}} (j : Z ⟶ X)
    (y : Sp K ⟶ Z) (yt : Sp O ⟶ X) (e : spMap φ ≫ yt = y ≫ j) {U : X.Opens} {W : Z.Opens}
    (hW : W ≤ j ⁻¹ᵁ U) (h : ⊤ ≤ y ⁻¹ᵁ W) (ht : ⊤ ≤ yt ⁻¹ᵁ U) (a : Γ(X, U)) :
    (y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom ((j.appLE U W hW).hom a) =
      φ ((yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom).hom a) := by
  have e1 : j.appLE U W hW ≫ y.appLE W ⊤ h = yt.appLE U ⊤ ht ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    simp only [e]
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e3 : j.appLE U W hW ≫ y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
      (yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom) ≫ CommRingCat.ofHom φ := by
    rw [← Category.assoc, e1, Category.assoc, e2, Category.assoc]
  exact congrArg (fun ψ => ψ.hom a) e3

variable {F : Type} [Field F] [NumberField F]

theorem w_unit {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) {x : e.O} (hx : IsUnit x) : e.w x = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h₁ := (e.mem_O _).1 (u : e.O).2
  have h₂ := (e.mem_O _).1 ((u⁻¹ : e.Oˣ) : e.O).2
  have h₃ : e.w ((u : e.O) : AlgebraicClosure F) * e.w (((u⁻¹ : e.Oˣ) : e.O) : AlgebraicClosure F) = 1 := by
    rw [← map_mul, ← MulMemClass.coe_mul, Units.mul_inv]
    simp
  have h₄ := e.w.nonneg ((u : e.O) : AlgebraicClosure F)
  nlinarith

variable {Y : Var F} (M : TrueGeo.Model Y) (B : LB M.X)

theorem le_chart {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X)
    (h : spMap e.O.subtype ≫ yt = y.1 ≫ M.j) {i : (B.pull M.j).ι} (hi : ⊤ ≤ yt ⁻¹ᵁ B.U (i PUnit.unit)) :
    ⊤ ≤ y.1 ⁻¹ᵁ (B.pull M.j).U i := fun x _ => Set.mem_iInter.2 fun _ => by
  change (y.1 ≫ M.j) x ∈ B.U (i PUnit.unit)
  rw [← h]
  exact hi (x := spMap e.O.subtype x) trivial

theorem w_indep {Δ : Y.Dv} {r : (B.pull M.j).ι → Y.Fnˣ} (hr : Presents Δ (B.pull M.j) r)
    {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X)
    (h : spMap e.O.subtype ≫ yt = y.1 ≫ M.j) {i i' : (B.pull M.j).ι} (hi : ⊤ ≤ yt ⁻¹ᵁ B.U (i PUnit.unit))
    (hi' : ⊤ ≤ yt ⁻¹ᵁ B.U (i' PUnit.unit)) :
    e.w (valAt y.1 (((eqn Δ (below y.1))⁻¹ * r i : Y.Fnˣ) : Y.Fn)) =
      e.w (valAt y.1 (((eqn Δ (below y.1))⁻¹ * r i' : Y.Fnˣ) : Y.Fn)) := by
  have h₁ : ⊤ ≤ y.1 ⁻¹ᵁ ((B.pull M.j).U i ⊓ (B.pull M.j).U i') :=
    fun x hx => ⟨le_chart M B e y yt h hi hx, le_chart M B e y yt h hi' hx⟩
  have h₂ : below y.1 ∈ (B.pull M.j).U i ⊓ (B.pull M.j).U i' := h₁ trivial
  have h₃ : ⊤ ≤ yt ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit)) := fun x hx => ⟨hi hx, hi' hx⟩
  have l : (B.pull M.j).U i ⊓ (B.pull M.j).U i' ≤ M.j ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have hg : ((B.pull M.j).g i i').val =
      (M.j.appLE _ _ l).hom (B.g (i PUnit.unit) (i' PUnit.unit)).val := by
    have : (B.pull M.j).g i i' = res l (pullU M.j _ (B.g (i PUnit.unit) (i' PUnit.unit))) := by
      change ∏ _k : PUnit, _ = _
      exact (Fintype.prod_unique _).trans (zpow_one _)
    rw [this]
    rfl
  have hu : RegAt (below y.1) (((eqn Δ (below y.1))⁻¹ * r i' : Y.Fnˣ) : Y.Fn) := by
    have := ((Δ.exists_isEqn (below y.1)).choose_spec.iff_unitAt.1 (hr.isEqn i' _ h₂.2)).regAt
    rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul] at this
  have e₁ : (((eqn Δ (below y.1))⁻¹ * r i : Y.Fnˣ) : Y.Fn) =
      fnOf _ (gen_mem h₂) ((B.pull M.j).g i i').val * (((eqn Δ (below y.1))⁻¹ * r i' : Y.Fnˣ) : Y.Fn) := by
    rw [Units.val_mul, Units.val_mul, hr.isRatSec i i' (gen_mem h₂), mul_left_comm]
  rw [e₁, valAt_mul _ (regAt_fnOf h₂ _ _) hu, valAt_fnOf _ h₂ h₁, hg, eval_pull _ _ _ yt h l h₁ h₃, map_mul]
  exact (congrArg (· * _) (w_unit e ((Units.isUnit _).map _))).trans (one_mul _)

theorem pn_mPow_one (C : CxSt F) (σ : F →+* ℂ) {Δ : Y.Dv} {L : LB Y.X} {r : L.ι → Y.Fnˣ} (hr : Presents Δ L r)
    (φ : Weight Y.str σ L) (y : Pts Y σ) {i : L.ι} (hi : under y ∈ L.U i) {f : Y.Fn}
    (hf : (1 • Δ).RegularAt (under y) f) :
    C.pn Y σ _ (C.mPow Y σ Δ 1 (C.ofWeight Y σ Δ L r hr φ)) (C.cx Y σ f) y =
      ‖ratVal (f * (r i : Y.Fn)) y‖ ^ 2 * Real.exp (-φ.φ i y) := by
  have h₁ := hr.isEqn i _ hi
  have h₂ := CartierDiv.isEqn_iff_generatesAt_inv.1 h₁
  have h₃ : (1 • Δ).RegularAt (under y) (r i : Y.Fn)⁻¹ := by rw [one_nsmul]; exact h₂.regularAt
  have h₄ : RegAt (under y) (f * (r i : Y.Fn)) := h₁.regularAt_iff.1 (by rwa [one_nsmul] at hf)
  have h₅ := C.pn_mul Y σ _ (C.mPow Y σ Δ 1 (C.ofWeight Y σ Δ L r hr φ)) _ _ y h₄ h₃
  have h₆ := C.pn_mPow Y σ Δ 1 (C.ofWeight Y σ Δ L r hr φ) _ y h₂
  have h₇ := C.pn_ofWeight Y σ Δ L r hr φ _ y i hi h₂.regularAt
  have h₈ : ratVal (1 : Y.Fn) y = 1 := by
    have e := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
    rwa [map_one, CxPts.ev_one CxPts.mem_ptsIn_top] at e
  rw [mul_inv_cancel_right₀ (r i).ne_zero] at h₅
  rw [pow_one, pow_one] at h₆
  rw [inv_mul_cancel₀ (r i).ne_zero, h₈] at h₇
  rw [h₅, h₆, h₇]
  simp

def ptMap (σ : F →+* ℂ) (y : Pts Y σ) : CxPts M.p (σ.comp (algebraMap (𝓞 F) F)) :=
  ⟨y.1 ≫ M.j, by rw [Category.assoc, M.pb.w, ← Category.assoc, y.2, ← Spec.map_comp]; rfl⟩

theorem exists_induced : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (M : TrueGeo.Model Y)
    (L : HermLB M.p) (Δ : Y.Dv) (r : (L.B.pull M.j).ι → Y.Fnˣ), Presents Δ (L.B.pull M.j) r →
    ∃ A : Adl C Y, A.D = Δ ∧ A.n = 1 ∧ A.ci = 0 ∧ A.Induced M L 1 0 := by
  intro F _ _ C Y M L Δ r hr
  classical
  have : IsSeparated M.p := by
    obtain ⟨N, c, hc, h⟩ := M.ar.isProjOver
    have := isProper_str (𝓞 F) N
    rw [← h]
    infer_instance
  let φ (σ : F →+* ℂ) : Weight Y.str σ (L.B.pull M.j) :=
    (L.φ (σ.comp (algebraMap (𝓞 F) F))).linComb _ _ (fun _ => ptMap M σ) fun _ _ => rfl
  let P (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (i : (L.B.pull M.j).ι) : Prop :=
    ∃ yt : Sp e.O ⟶ M.X, spMap e.O.subtype ≫ yt = y.1 ≫ M.j ∧ ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit)
  refine ⟨⟨Δ, 1, fun σ => C.ofWeight Y σ Δ _ r hr (φ σ), 0, fun v e y => if h : ∃ i, P v e y i then
    Real.log (e.w (valAt y.1 (((eqn Δ (below y.1))⁻¹ * r h.choose : Y.Fnˣ) : Y.Fn))) else 0⟩,
    rfl, rfl, rfl, by simp, r, ?_, ?_, ?_⟩
  · change Presents (1 • Δ) _ _
    rwa [one_nsmul]
  · intro σ y y' i f hy hi hf
    obtain rfl : y' = ptMap M σ y := Subtype.ext hy
    have e : (φ σ).φ i y = (L.φ _).φ (i PUnit.unit) (ptMap M σ y) :=
      (Fintype.sum_unique fun a : PUnit.{1} =>
        ((1 : ℤ) : ℝ) * (L.φ _).φ (i a) (ptMap M σ y)).trans (by simp)
    rw [← e, ← pn_mPow_one C σ hr (φ σ) y hi hf]
    simp only [Pi.zero_apply, mul_zero, neg_zero, Real.exp_zero, one_mul]
    rfl
  · intro v e y yt i h hi
    have hP : ∃ i, P v e y i := ⟨i, yt, h, hi⟩
    obtain ⟨yt', h', hi'⟩ := hP.choose_spec
    obtain rfl : yt = yt' := ext_unique e.O M.p (h.trans h'.symm)
    simp only [dif_pos hP, PNat.val_ofNat, Nat.cast_one, one_mul, pow_one, Pi.zero_apply, sub_zero]
    rw [w_indep M L.B hr e y yt h hi' hi]

end GlobalTheory.TrueGeo.OfModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationPowOfIsPlaceOver
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LyingOver

theorem valuation_pow_of_isPlaceOver : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)), IsPlaceOver A v → IsPlaceOver A v' → ∃ e : ℕ, 0 < e ∧ ∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e := by
  intro K L Ω _ _ _ _ _ _ _ _ _ A v v' hv hv'
  have hcomap : v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
    ext x
    rw [Ideal.mem_comap, ← hv x, ← hv' (algebraMap (𝓞 K) (𝓞 L) x)]
    have : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
    rw [this, ← IsScalarTower.algebraMap_apply]
  haveI : v'.asIdeal.LiesOver v.asIdeal := ⟨hcomap.symm⟩
  refine ⟨v.asIdeal.ramificationIdx' v'.asIdeal,
    Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver v'.asIdeal v.ne_bot), ?_⟩
  intro x
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L v v' x).symm

end GlobalTheory.LyingOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakCompatibilityOfRealRowSideAdelicChainStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.RecTie
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakCompatibility_of_realRowSide_adelicChain : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (I : RowIds (RowSide.sharp D) (toChainReal R F tupT hm hTop) true) (n : ℕ) (bs : OrthonormalBasis (Fin n) ℂ D.what₂.EE) (ty : Fin n → D.what₂.FT), R.IsModels → R.IsChain → RowSideReal (RowSide.sharp D) (toChainReal R F tupT hm hTop) true I bs ty → ∀ μ, Used0 D μ → (∃ (e : ∀ j, D.what₂.Mult μ j →ₗ[ℂ] R.CC (tupT μ) j) (eX : D.what₂.Mult μ D.R.m →ₗ[ℂ] LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e)) (ν : ∀ j, Measure (GA D (Yc D j))) (𝓕 : ∀ j, Set (GA D (Yc D j))) (c : ℕ → ℝ) (cX : ℝ), (∀ j, j < D.R.m → IsQuot (Yc D j) (ν j) (𝓕 j) ∧ 0 < c j ∧ ∀ x y, ⟪x, y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (e j y).1 (e j x).1) ∧ (∃ J χ, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX (tupT μ)).e) ≤ MultT R.θ R.MX J χ) ∧ 0 < cX ∧ (∀ x y, ⟪x, y⟫_ℂ = (cX : ℂ) * ipT R.MX (R.νX (tupT μ)) (R.fdX (tupT μ)) (eX y).1 (eX x).1) ∧ (∀ j, j + 1 < D.R.m → ∀ x y, ⟪x, D.what₂.io μ j y⟫_ℂ = (c j : ℂ) * ipT (R.MY j) (ν j) (𝓕 j) (R.ioY (tupT μ) j (e (j + 1) y)).1 (e j x).1) ∧ ∀ x (y : D.what₂.Mult μ (D.R.m - 1 + 1)) (y' : D.what₂.Mult μ D.R.m), HEq y y' → ⟪x, D.what₂.io μ (D.R.m - 1) y⟫_ℂ = (c (D.R.m - 1) : ℂ) * ipT (R.MY (D.R.m - 1)) (ν (D.R.m - 1)) (𝓕 (D.R.m - 1)) (R.ioX (tupT μ) (eX y')).1 (e (D.R.m - 1) x).1) := by
  first | exact @GlobalTheory.RowTieRead.weak_tie | exact GlobalTheory.RowTieRead.weak_tie | (intros; apply GlobalTheory.RowTieRead.weak_tie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneRelUnique
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjWD

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem actsAs_conj {A : ValuationSubring Ω} {q : ℕ} {g σ : G E Ω} (hg : g ∈ Dec (F := E) A)
    {a b : ℕ} (hσ : ActsAs A q σ a b) : ActsAs A q (g * σ * g⁻¹) a b := by
  refine ⟨(Dec (F := E) A).mul_mem ((Dec (F := E) A).mul_mem hg hσ.1) ((Dec (F := E) A).inv_mem hg),
    fun x hx => ?_⟩
  have hy : A.valuation ((g⁻¹ : G E Ω) x) ≤ 1 := val_apply_le_one ((Dec (F := E) A).inv_mem hg) hx
  have h1 := hσ.2 _ hy
  rw [← valuation_apply_lt_one_iff hg, map_sub, map_pow, map_pow, mul_inv_apply] at h1
  exact h1

end

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def conjW (g : G E Ω) (hg : g ∈ Dec (F := E) A) (σ : Weil h) : Weil h :=
  ⟨g * σ * g⁻¹, by obtain ⟨a, b, hab⟩ := σ.2; exact ⟨a, b, actsAs_conj hg hab⟩⟩

@[simp] theorem coe_conjW (g : G E Ω) (hg : g ∈ Dec (F := E) A) (σ : Weil h) :
    (conjW g hg σ : G E Ω) = g * σ * g⁻¹ := rfl

end GlobalTheory.ConjWD

namespace GlobalTheory.ConjWD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_weil_eq_on {g : G E Ω} (hg : g ∈ Dec (F := E) A) (L : IntermediateField E Ω)
    [FiniteDimensional E L] : ∃ τ : Weil h, ∀ x ∈ L, (τ : G E Ω) x = g x := by
  obtain ⟨k, hk⟩ := GlobalTheory.T.decomposition_element_frobenius_power E Ω A w h L inferInstance g hg
  set φ : Weil h := frob h ^ k
  have hφ : ActsAs A (normV w) (φ : G E Ω) k 0 := actsAs_of_deg (by simp [φ])
  have hψ : ((φ : G E Ω) * g) ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem hφ.1 hg
  obtain ⟨ι, hι, hιL⟩ := GlobalTheory.T.inertia_lift_of_residual_trivial E Ω A w h L _ hψ fun x hx hxi => by
    have hx1 : A.valuation x ≤ 1 := (A.valuation_le_one_iff x).mpr (mem_of_isIntegral_int A hxi)
    have hgx : A.valuation (g x) ≤ 1 := val_apply_le_one hg hx1
    have h1 := hφ.2 _ hgx
    simp only [pow_zero, pow_one] at h1
    exact cong_trans h1 (hk x hx hxi)
  refine ⟨φ⁻¹ * ineIncl h ⟨ι, hι⟩, fun x hx => ?_⟩
  show (φ : G E Ω)⁻¹ (ι x) = g x
  rw [hιL x hx, AlgEquiv.mul_apply]
  show ((φ : G E Ω)⁻¹ * (φ : G E Ω)) (g x) = g x
  simp

end GlobalTheory.ConjWD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilFockVectorEigenOfFiniteStepEigen
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.DTheta.StepLevFock

theorem om_ptY_of_finite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (t : T) (k : ℕ), k + 1 < D.R.m → ∀ κ ∈ GfC (Yc D k), ∀ κ' ∈ GfC (Yc D (k + 1)), ∀ c : ℂ, R.ωY t k (κ, κ') (R.vY t k) = c • R.vY t k → ∀ φ, R.ωY t k (κ, κ') (R.toRealDat.ptY t k φ) = c • R.toRealDat.ptY t k φ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH t k hk κ hκ κ' hκ' c hc φ
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hP.char.base.chain hH.aux.ex
  exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite _ _ _ _ _ _ (R.ωY t k) hP.char.base.models.inf (hch.ωY t k hk)
    _ _ _ _ (R.vY t k) (hch.ptY t k hk) κ hκ κ' hκ' c hc φ

end GlobalTheory.Mem.R3.DTheta.StepLevFock
end

