import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0050
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
import ReciprocityTheory.ReductiveGroups.SymplecticTraces.WeylCharacters.Weyl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.LieVB
open GlobalTheory.LB (resG_resG resG_self)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open GlobalTheory.VB GlobalTheory.Conormal
open GlobalTheory.KS.DerMorK (deformHom hom_ext_appLE)

namespace GlobalTheory.LieVB.TangentSurj

section General

variable {S X T : Scheme.{0}} {π : X ⟶ S} {e : S ⟶ X} (p : T ⟶ S) (ε : Γ(T, ⊤)) (hε : ε * ε = 0)
  (D : Der π e (structureModule S))

def val {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) : Γ(X, W) →+ Γ(S, V) := D.app h

theorem val_mul {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (f g : Γ(X, W)) :
    val D h (f * g) = e.appLE W V h f * val D h g + e.appLE W V h g * val D h f :=
  D.app_mul h f g

theorem val_base {W : X.Opens} {V U : S.Opens} (h : V ≤ e ⁻¹ᵁ W) (k : W ≤ π ⁻¹ᵁ U) (a : Γ(S, U)) :
    val D h (π.appLE U W k a) = 0 := D.app_base h k a

theorem val_one {W : X.Opens} {V : S.Opens} (h : V ≤ e ⁻¹ᵁ W) : val D h 1 = 0 := by
  simpa using val_base D (U := ⊤) h le_top 1

theorem val_res {W W' : X.Opens} (k : W' ≤ W) (f : Γ(X, W)) :
    val D (le_refl (e ⁻¹ᵁ W')) (resG X k f) = resG S (e.preimage_mono k) (val D le_rfl f) :=
  (D.app_res _ k f).trans (D.res_app le_rfl (e.preimage_mono k) f).symm

include hε in

theorem res_sq (U : T.Opens) : resG T (le_top : U ≤ ⊤) ε * resG T (le_top : U ≤ ⊤) ε = 0 := by
  rw [← map_mul, hε, map_zero]

def psi (W : X.Opens) : Γ(X, W) →+* Γ(T, p ⁻¹ᵁ e ⁻¹ᵁ W) where
  toFun f := p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) +
    p.appLE _ _ le_rfl (val D le_rfl f) * resG T le_top ε
  map_one' := by simp only [val_one, map_one, map_zero, zero_mul, add_zero]
  map_mul' f g := by
    simp only [val_mul, map_mul, map_add]
    linear_combination -(p.appLE _ _ le_rfl (val D le_rfl f) * p.appLE _ _ le_rfl (val D le_rfl g)) *
      res_sq ε hε (p ⁻¹ᵁ e ⁻¹ᵁ W)
  map_zero' := by simp only [map_zero, zero_mul, add_zero]
  map_add' f g := by
    simp only [map_add]
    ring

theorem psi_apply (W : X.Opens) (f : Γ(X, W)) : psi p ε hε D W f =
    p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) +
      p.appLE _ _ le_rfl (val D le_rfl f) * resG T le_top ε := rfl

theorem psi_nat (W W' : X.Opens) (h : W' ≤ W) (f : Γ(X, W)) :
    psi p ε hε D W' (resG X h f) =
      resG T (p.preimage_mono (e.preimage_mono h)) (psi p ε hε D W f) := by
  rw [psi_apply, psi_apply, val_res, map_add, map_mul, resG_resG, resG_appLE, resG_appLE,
    appLE_resG e, appLE_resG p, ← resG_appLE e (e.preimage_mono h) le_rfl, appLE_resG p]

theorem psi_nil (W : X.Opens) (f : Γ(X, W)) :
    IsNilpotent (psi p ε hε D W f - p.appLE _ _ le_rfl (e.appLE W _ le_rfl f)) := by
  refine ⟨2, ?_⟩
  rw [psi_apply]
  linear_combination (p.appLE _ _ le_rfl (val D le_rfl f)) ^ 2 * res_sq ε hε (p ⁻¹ᵁ e ⁻¹ᵁ W)

def deform : T ⟶ X :=
  deformHom (p ≫ e) (psi p ε hε D) (psi_nat p ε hε D) fun W f => by
    have h : ((p ≫ e).app W).hom f = p.appLE _ _ le_rfl (e.appLE W _ le_rfl f) := by
      rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app]; rfl
    rw [h]
    exact psi_nil p ε hε D W f

theorem deform_appLE (W : X.Opens) {U : T.Opens} (k : U ≤ p ⁻¹ᵁ e ⁻¹ᵁ W) (f : Γ(X, W)) :
    (deform p ε hε D).appLE W U k f = resG T k (psi p ε hε D W f) := rfl

theorem deform_comp (he : e ≫ π = 𝟙 S) : deform p ε hε D ≫ π = p := by
  have h₀ : p ≫ e ≫ π = p := by rw [he, Category.comp_id]
  refine hom_ext_appLE (congr(($h₀).base)) fun U k => ?_
  ext a
  have k' : p ⁻¹ᵁ U ≤ p ⁻¹ᵁ e ⁻¹ᵁ π ⁻¹ᵁ U := k
  refine (appLE_appLE (f := deform p ε hε D) rfl le_rfl k' k a).symm.trans ?_
  rw [deform_appLE, psi_apply, val_base, map_zero, zero_mul, add_zero,
    appLE_base he _ _ ((le_preimage_iff he).1 le_rfl), appLE_resG, resG_appLE,
    Scheme.Hom.appLE_eq_app]

theorem comp_deform {z : S ⟶ T} (hz : z ≫ p = 𝟙 S) (h0 : z.appLE ⊤ ⊤ le_top ε = 0) :
    z ≫ deform p ε hε D = e := by
  have h₀ : z ≫ p ≫ e = e := by rw [reassoc_of% hz]
  refine hom_ext_appLE (congr(($h₀).base)) fun W k => ?_
  ext f
  have k' : e ⁻¹ᵁ W ≤ z ⁻¹ᵁ p ⁻¹ᵁ e ⁻¹ᵁ W := k
  refine (appLE_appLE (f := z) (g := deform p ε hε D) (V := p ⁻¹ᵁ e ⁻¹ᵁ W)
    rfl le_rfl k' k f).symm.trans ?_
  rw [deform_appLE, resG_self, psi_apply, map_add, map_mul, appLE_resG,
    ← resG_appLE z le_top le_top ε, h0, map_zero, mul_zero, add_zero,
    appLE_base hz _ _ le_rfl, resG_self, Scheme.Hom.appLE_eq_app]

end General

variable (O : Type) [CommRing O]

theorem epsFn_sq : epsFn O * epsFn O = 0 := by
  have h := map_mul (Scheme.ΓSpecIso (.of (DualNumber O))).inv.hom DualNumber.eps DualNumber.eps
  rw [DualNumber.eps_mul_eps, map_zero] at h
  exact h.symm

theorem epsZero_epsFn : (sec (epsZero O)).appLE ⊤ ⊤ le_top (epsFn O) = 0 := by
  refine congr($(Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom O O O).toRingHom)) DualNumber.eps).symm.trans ?_
  exact (congrArg (Scheme.ΓSpecIso (.of O)).inv.hom (DualNumber.fst_eps (R := O))).trans
    (map_zero _)

theorem tangent_surjective (O : Type) [CommRing O] (G : Over (Sp O)) [GrpObj G] :
    Function.Surjective (tangent : LieG G → Γ(Lie G, ⊤)) := by
  intro l
  let D := lieEquivDer G l
  let x : specO O (DualNumber O) ⟶ G :=
    Over.homMk (deform (specO O (DualNumber O)).hom (epsFn O) (epsFn_sq O) D)
      (deform_comp _ _ _ D (sec_hom η[G]))
  have hx : ptMap (TrivSqZeroExt.fstHom O O O) ≫ x = toUnit (specO O O) ≫ η[G] := by
    have h : (toUnit (specO O O)).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]
      exact Spec.map_id _
    ext1
    simp only [Over.comp_left, h]
    exact (comp_deform _ _ (epsFn_sq O) D (sec_hom (epsZero O)) (epsZero_epsFn O)).trans
      (Category.id_comp _).symm
  refine ⟨⟨x, hx⟩, (homGlobalEquiv _ _).injective (omega_hom_ext fun W f => ?_)⟩
  refine dualApp_tangent_dUnit ⟨x, hx⟩ le_rfl f
    ((le_preimage_iff (sec_hom (epsZero O))).2 le_rfl) le_rfl le_rfl
    ((unitSec G).appLE W _ le_rfl f) (val D le_rfl f) ?_
  exact (deform_appLE _ _ (epsFn_sq O) D W le_rfl f).trans (resG_self _ _)

end GlobalTheory.LieVB.TangentSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusConjugationWeylCell
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory

namespace WeylCell

section DiagConj

variable {L : Type} [Field L] {n : ℕ}

theorem gl_eq_diagonal_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) :
    (D : Matrix (Fin n) (Fin n) L) = Matrix.diagonal fun i => (D : Matrix (Fin n) (Fin n) L) i i := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.diagonal_apply_ne _ h, hD i j h]

theorem gl_diag_ne_zero_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) (i : Fin n) :
    (D : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  intro h0
  have h := congrFun (congrFun (Units.mul_inv D) i) i
  rw [gl_eq_diagonal_of_offdiag hD, Matrix.diagonal_mul, h0, zero_mul, Matrix.one_apply_eq] at h
  exact zero_ne_one h

theorem gl_inv_eq_diagonal_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) :
    ((D⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      Matrix.diagonal fun i => ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹ := by
  have hne := gl_diag_ne_zero_of_offdiag hD
  rw [Matrix.coe_units_inv]
  apply Matrix.inv_eq_left_inv
  calc Matrix.diagonal (fun i => ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹) * (D : Matrix (Fin n) (Fin n) L)
      = Matrix.diagonal (fun i => ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹) *
          Matrix.diagonal (fun i => (D : Matrix (Fin n) (Fin n) L) i i) :=
        congrArg _ (gl_eq_diagonal_of_offdiag hD)
    _ = 1 := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        exact inv_mul_cancel₀ (hne i)

theorem gl_conj_apply_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) (g : GL (Fin n) L) (i j : Fin n) :
    ((D⁻¹ * g * D : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((D : Matrix (Fin n) (Fin n) L) i i)⁻¹ * (g : Matrix (Fin n) (Fin n) L) i j *
        (D : Matrix (Fin n) (Fin n) L) j j := by
  rw [Units.val_mul, Units.val_mul, gl_inv_eq_diagonal_of_offdiag hD]
  conv_lhs => rw [gl_eq_diagonal_of_offdiag hD]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]

theorem conj_mem_unipB_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) {g : GL (Fin n) L}
    (hg : g ∈ unipB L (Fin n)) : D⁻¹ * g * D ∈ unipB L (Fin n) := by
  rw [mem_unipB] at hg ⊢
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [gl_conj_apply_of_offdiag hD, hg.1 i j hij, mul_zero, zero_mul]
  · rw [gl_conj_apply_of_offdiag hD, hg.2 i, mul_one, inv_mul_cancel₀ (gl_diag_ne_zero_of_offdiag hD i)]

theorem conj_mem_unipBLower_of_offdiag {D : GL (Fin n) L}
    (hD : ∀ i j, i ≠ j → (D : Matrix (Fin n) (Fin n) L) i j = 0) {g : GL (Fin n) L}
    (hg : g ∈ unipBLower L (Fin n)) : D⁻¹ * g * D ∈ unipBLower L (Fin n) := by
  rw [mem_unipBLower] at hg ⊢
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [gl_conj_apply_of_offdiag hD, hg.1 i j hij, mul_zero, zero_mul]
  · rw [gl_conj_apply_of_offdiag hD, hg.2 i, mul_one, inv_mul_cancel₀ (gl_diag_ne_zero_of_offdiag hD i)]

theorem weylRep_conj_offdiag {w : Equiv.Perm (Fin n)} {y t : GL (Fin n) L} (hy : IsWeylRep w y)
    (ht : ∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) L) i j = 0) :
    ∀ i j, i ≠ j → ((y⁻¹ * t * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  intro i j hij
  have hyi := hy.inv
  rw [Units.val_mul, Units.val_mul, gl_eq_diagonal_of_offdiag ht, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = w j
  · subst hl
    rw [Matrix.mul_diagonal, hyi i (w j) (by simpa using hij), zero_mul, zero_mul]
  · rw [hy l j hl, mul_zero]

end DiagConj

end WeylCell

end GlobalTheory

end

theorem GlobalTheory.WeylCell.diagConjU : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (y : GU σ n) (w : Equiv.Perm (Fin n)), IsWeylRep w (y : GL (Fin n) L) → ∀ (t : GU σ n),
    (∀ i j, i ≠ j → ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0) →
    IsBorelU (y⁻¹ * t * y) ∧ ∀ u ∈ cellU y, t⁻¹ * u * t ∈ cellU y := by
  intro L _ _ σ n y w hy t ht
  have hD := weylRep_conj_offdiag hy ht
  refine ⟨fun i j hij => ?_, fun u hu => ?_⟩
  · exact hD i j (ne_of_gt hij)
  · rw [cellU, Subgroup.mem_subgroupOf, mem_cell] at hu ⊢
    have e1 : (((t⁻¹ * u * t : GU σ n)) : GL (Fin n) L) =
        ((t : GL (Fin n) L))⁻¹ * (u : GL (Fin n) L) * (t : GL (Fin n) L) := rfl
    rw [e1]
    refine ⟨conj_mem_unipB_of_offdiag ht hu.1, ?_⟩
    have e2 : ((y : GL (Fin n) L))⁻¹ * (((t : GL (Fin n) L))⁻¹ * (u : GL (Fin n) L) * (t : GL (Fin n) L)) *
        (y : GL (Fin n) L) =
        ((y : GL (Fin n) L)⁻¹ * t * y)⁻¹ * ((y : GL (Fin n) L)⁻¹ * u * y) * ((y : GL (Fin n) L)⁻¹ * t * y) := by
      group
    rw [e2]
    exact conj_mem_unipBLower_of_offdiag hD hu.2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqOfMem
section
noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.TRGap GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open GlobalTheory.PsCo.Pc1 (Mat Poly ev dMode blockAlg topP detbP OmP)
open GlobalTheory.HCChar (dsChar torusPt)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.PcEF

open GlobalTheory.PsCo.PcEG

theorem trace_eq_of_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (B : H →L[ℂ] H)
    (L : Submodule ℂ H) [FiniteDimensional ℂ L] (hB : ∀ x, (B : H →ₗ[ℂ] H) x ∈ L) {c : ℂ} (hc : HasTrace B c) :
    c = LinearMap.trace ℂ L ((B : H →ₗ[ℂ] H).restrict fun x _ => hB x) := by
  have hle : LinearMap.range (B : H →ₗ[ℂ] H) ≤ L := by rintro _ ⟨x, rfl⟩; exact hB x
  have := Submodule.finiteDimensional_of_le hle
  rw [← hc.2, (hasTrace_of_finiteRank B).2, finRankTrace_eq _ L hB]

theorem equiv_of_index (hR : RangeFD) (hY : BuildY) (hS : StrKer) (hI : StrIdx) (hA : AvgMap) (hH : HWVec)
    (hC : CoordFD) (hCas : CasCoord) (hAlg : AlgDatum) (hE : DatumEquiv) (hCS : CompanionTheory.D.gk.HC.CasScal)
    {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hstd : StdGap ε lam) (h3 : Gap3 ε lam)
    {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {T : Mat n → (W →L[ℂ] W)}
    (hT : IsKIrr ε (gaW ε lam) T) {P : Poly n} (hP : ∀ k ∈ Formalism.REAL.Kset ε, conj (trK T k) = ev k P)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat n → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ) (B : H →L[ℂ] H)
    (hB : ∀ w, B w = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • σ (toMK k) w ∂(muK ε)) {c : ℂ}
    (hc : HasTrace B c) (hc0 : c ≠ 0)
    {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {D : Mat n → (X →L[ℂ] X)} (hD : Formalism.MainNotions.S.IsDS ε lam D) :
    ∃ U : H ≃ₗᵢ[ℂ] X, ∀ g ∈ UJset ε, ∀ x, U (σ g x) = D g (U x) := by
  have hDer := isDerivedOn_smE hσ
  obtain ⟨d, hd⟩ := hI n ε P
  obtain ⟨L, hLf, hLK, hLr⟩ := hR n ε H σ hσ hirr d
  obtain ⟨cas, hcas⟩ := hCS n ε H σ hσ hirr
  obtain ⟨Y, hYf, hle, hYP, hYD, hG, hK⟩ := hY n ε H σ _ _ hσ hDer cas hcas L hLf hLK
  obtain ⟨hBL, htr⟩ := hd H σ _ _ hσ hDer L hLK hLr Y hle hYP hG hK B hB
  obtain ⟨Z, hZf, hZK, Γ, hZY, hZD, hZtr⟩ := hS n ε H σ _ _ hσ hDer Y hYD hG hK
  have hLH : FiniteDimensional ℂ (L.map (smD ε σ).subtype) := Module.Finite.map _ _
  have h1 := (trace_eq_of_mem B _ hBL hc).trans htr
  obtain ⟨Φ, hΦ0, hΦ⟩ := hA n ε W T (TSub Z) (tOp hDer hZK) Γ hT.2.1 (tOp_isURepOn hDer hZK hσ) (by
    intro h0
    apply hc0
    rw [h1, ← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [hZtr (toMK k) k.2, hP (toMK k) k.2])
  obtain ⟨z, hzZ, hz0, hz⟩ := hH n ε H σ _ _ hσ hDer Z hZK _ W T hT Φ hΦ0 hΦ
  obtain ⟨hSf, hSk⟩ := hC n ε _ (smE ε σ) Z hZf fun a b hab y hy => diagE_mem_of_wK hσ hDer Z hZf hZK hab hy
  obtain ⟨V, hV, hV0, hVc⟩ := hAlg n ε lam h3 _ (smE ε σ) hDer.glRep (isInfUnitary_of_isDerivedOn hσ hDer) z hz0
    (hYP (hZY hzZ)) hz (hCas n ε lam _ _ hDer.glRep z hz (hZD z hzZ)) _ hSf hSk
    fun s => Submodule.subset_span ⟨s, z, hzZ, rfl⟩
  exact hE n ε lam hstd H σ hσ hirr V hV hV0 hVc X D hD

theorem exists_type (hCp : CptCase) (hSch : SchurOne)
    {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hHC : Formalism.QuantumDeterminants.IsHCParam lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hthr : thrStar ε < h) {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    {D : Mat n → (X →L[ℂ] X)} (hD : Formalism.MainNotions.S.IsDS ε lam D) :
    ∃ (W : Type) (_ : NormedAddCommGroup W) (_ : InnerProductSpace ℂ W) (_ : FiniteDimensional ℂ W)
      (T : Mat n → (W →L[ℂ] W)), IsKIrr ε (gaW ε lam) T ∧ ∀ P : Poly n,
      (∀ k ∈ Formalism.REAL.Kset ε, conj (trK T k) = ev k P) → ∀ (B : X →L[ℂ] X) (c : ℂ),
      (∀ w, B w = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • D (toMK k) w ∂(muK ε)) → HasTrace B c →
      c = (-1) ^ sDeg ε := by
  by_cases hpq : pOf ε = 0 ∨ qOf ε = 0
  · obtain ⟨hpd, hs, hX⟩ := hCp n ε lam hpq
    obtain ⟨hfd, hT⟩ := hX X D hD
    refine ⟨X, inferInstance, inferInstance, hfd, D, hT, fun P hP B c hB hc => ?_⟩
    have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
      (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
      inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
    have : SecondCountableTopology (KG ε) := hemb.isInducing.secondCountableTopology
    have hcont : Continuous fun k : KG ε => ev (toMK k) P * physDet ε (toMK k) := by
      simp only [hpd, mul_one]
      refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun p => ?_)
      rcases p with p | p
      · exact (continuous_apply p.2).comp ((continuous_apply p.1).comp hemb.continuous)
      · exact continuous_star.comp ((continuous_apply p.2).comp ((continuous_apply p.1).comp hemb.continuous))
    have h1 := trace_integral_restrict (μ := muK ε) (⊤ : Submodule ℂ X) hcont (fun k => D (toMK k))
      (fun v => (hT.2.1.2.2 v).comp_continuous hemb.continuous fun k => k.2) (fun _ _ _ => trivial) B hB
      (fun _ _ => trivial)
    rw [trace_eq_of_mem B ⊤ (fun _ => trivial) hc, h1, hs, pow_zero, ← hSch n ε _ X D hT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [hpd, mul_one, hP (toMK k) k.2, trK]
    congr 1
    exact LinearMap.trace_restrict_eq_of_forall_mem ⊤ _ fun _ => trivial
  · obtain ⟨W, i1, i2, i3, T, h1, h2, h3, h4⟩ := supTrace n ε lam h X D hD hHC hh hthr (by omega) (by omega)
    refine ⟨W, i1, i2, i3, T, ⟨h1, h2, h3⟩, fun P hP B c hB hc => ?_⟩
    obtain ⟨hf, htr⟩ := h4 P B hB
    rw [trace_eq_of_mem B _ (fun x => LinearMap.mem_range_self _ x) hc, htr]
    have h5 := hSch n ε _ W T ⟨h1, h2, h3⟩
    rw [← mul_one ((-1 : ℂ) ^ sDeg ε), mul_assoc, one_mul, ← h5]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [hP (toMK k) k.2]
    rfl

theorem stKData_of (hBF : BlockForm) (hOm : OmDet) (hCP : CoefPoly) (hTP : TrPoly) (hCl : ClassFn) (hGa : GaInt)
    (hTK : ToKType) (hPT : PhysTor) (hTor : TorusId) (hA : AvgMap) (hSch : SchurOne) (hR : RangeFD) (hY : BuildY)
    (hS : StrKer) (hI : StrIdx) (hH : HWVec) (hC : CoordFD) (hCas : CasCoord) (hAlg : AlgDatum) (hE : DatumEquiv)
    (hCp : CptCase) (hGap : GapNum) (hM : MatRep) (hCS : CompanionTheory.D.gk.HC.CasScal) : GlobalTheory.PsCo.Pc1.StKData := by
  intro r hr ε lam hg X _ _ D hD
  have := hD.1
  obtain ⟨hHC, hstd, h3, h, hh, hthr⟩ := hGap r hr ε lam hg
  obtain ⟨W, _, _, _, T, hT, hidx⟩ := exists_type hCp hSch hHC hh hthr hD
  have hcoef := hCP r ε W T hT.2.1
  obtain ⟨P, hP⟩ := hTP r ε W T hcoef
  replace hP : ∀ k ∈ Formalism.REAL.Kset ε, conj (trK T k) = ev k P := hP
  obtain ⟨Q, hQ⟩ := hOm r ε
  obtain ⟨M, R, hRb, hRe⟩ := hBF r ε (MvPolynomial.C ((-1 : ℂ) ^ sDeg ε) * P * Q)
  have hsq : ((-1 : ℂ) ^ sDeg ε) * (-1) ^ sDeg ε = 1 := by rw [← mul_pow]; simp
  have htop : ∀ k ∈ Formalism.REAL.Kset ε, ev k (topP ε M R) = (-1) ^ sDeg ε * (ev k P * physDet ε k) := by
    intro k hk
    rw [topP, map_mul, ← hRe k hk, ← hQ k hk, map_mul, map_mul, show ev k (MvPolynomial.C _) = _ from MvPolynomial.eval_C _]
    ring
  have hscale : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (A : KG ε → (H →L[ℂ] H)) (B : H →L[ℂ] H) (c : ℂ),
      (∀ v, B v = ∫ k : KG ε, ev (toMK k) (topP ε M R) • A k v ∂(muK ε)) → HasTrace B c →
      (∀ v, (((-1 : ℂ) ^ sDeg ε) • B) v = ∫ k : KG ε, (ev (toMK k) P * physDet ε (toMK k)) • A k v ∂(muK ε)) ∧
        HasTrace (((-1 : ℂ) ^ sDeg ε) • B) ((-1) ^ sDeg ε * c) := by
    intro H _ _ _ A B c hB hc
    refine ⟨fun v => ?_, ⟨hc.1.smul _, by rw [trace_smul, hc.2]⟩⟩
    rw [_root_.smul_apply, hB, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [htop (toMK k) k.2, smul_smul, ← mul_assoc, hsq, one_mul]
  refine ⟨M, R, hRb, fun k k' => ?_, fun θ hθ => ?_, fun B c hB hc => ?_, fun U _ _ _ π hπ hi hne B c hB hc => ?_⟩
  · rw [htop _ (k'⁻¹ * k * k').2, htop _ k.2, ← hP _ (k'⁻¹ * k * k').2, ← hP _ k.2, (hCl r ε k k').1,
      (hCl r ε k k').2 W T hT.2.1]
  · obtain ⟨Λ, m, hΛ, hdom, hm, hsh⟩ := hGa r ε _ hHC
    have hk : Matrix.diagonal (tor θ) ∈ Kset ε := diag_mem_Kset' ε θ
    rw [hΛ] at hT
    obtain ⟨T₀, hT₀⟩ := hTK r ε _ W T hT hcoef
    have hw := ReciprocityTheory.ChartRestriction.TR.Weyl.weyl r ε Λ hdom T₀ (HW.torepK ε hk) (tor θ) rfl
    rw [hT₀] at hw
    have h1 := hTor r ε _ Λ m hm hsh θ hθ _ hw
    change (-1) ^ sDeg ε * trK T (Matrix.diagonal (tor θ)) = _ at h1
    change ev (Matrix.diagonal (tor θ)) _ = _
    have h2 := congrArg conj h1
    rw [map_mul, map_mul, map_pow, map_neg, map_one] at h2
    rw [htop _ hk, ← hP _ hk, ← (hPT r ε θ).2, ← mul_assoc, h2]
    ring
  · obtain ⟨h1, h2⟩ := hscale X (fun k => D (toMK k)) B c hB hc
    have h4 := hidx P hP _ _ h1 h2
    have h5 := congrArg (fun x => (-1 : ℂ) ^ sDeg ε * x) h4
    simpa only [← mul_assoc, hsq, one_mul] using h5
  · by_contra hc0
    obtain ⟨σ, hσ, hirr, hσπ⟩ := hM r ε U π hπ hi
    obtain ⟨h1, h2⟩ := hscale U (fun k => π k) B c hB hc
    obtain ⟨A, hAe⟩ := equiv_of_index hR hY hS hI hA hH hC hCas hAlg hE hCS hstd h3 hT hP hσ hirr _
      (fun w => by rw [h1 w]; simp only [toMK, hσπ]) h2
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) hc0) hD
    exact hne ⟨A, fun g v => by rw [← hσπ g]; exact hAe _ g.2 v⟩

end GlobalTheory.PsCo.PcEF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsum
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

def twSum {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (g : G) : ℂ :=
  (((twCent θ δ ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) *
    avg fun k : K => f ((g * k)⁻¹ * δ * θ (g * k))

def pairTw {G₁ G₂ : Type} [Group G₁] [Group G₂] (θ₁ : G₂ →* G₁) (θ₂ : G₁ →* G₂) : G₁ × G₂ →* G₁ × G₂ :=
  (θ₁.comp (MonoidHom.snd G₁ G₂)).prod (θ₂.comp (MonoidHom.fst G₁ G₂))

@[simp] theorem pairTw_apply {G₁ G₂ : Type} [Group G₁] [Group G₂] (θ₁ : G₂ →* G₁) (θ₂ : G₁ →* G₂) (y : G₁ × G₂) :
    pairTw θ₁ θ₂ y = (θ₁ y.2, θ₂ y.1) := rfl

variable (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)

def rho (u : Pl E) : Gam E n u →* GLw n u × GLw n (cPl E u) :=
  ((GeneralLinearGroup.map (pLoc E u)).comp (Gam E n u).subtype).prod
    ((GeneralLinearGroup.map (pLoc E (cPl E u))).comp (Gam E n u).subtype)

end GlobalTheory.EulerTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwOrbEqFinsumTwTerm
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerAbs

variable {G : Type} [Group G] [TopologicalSpace G]

def twTerm (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G) : ℂ :=
  (((twCent θ δ ⊓ K.map (MulAut.conj y).toMonoidHom).relIndex (cptPart (twCent θ δ)) : ℕ) : ℂ) *
    avg fun k : K => f ((y * k)⁻¹ * δ * θ (y * k))

theorem twOrb_eq_finsum_twTerm (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) :
    twOrb θ K δ f = ∑ᶠ q : DoubleCoset.Quotient (twCent θ δ : Set G) (K : Set G), twTerm θ K δ f (Quotient.out q) :=
  rfl

end GlobalTheory.EulerAbs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerLocalUnitaryCommOfSeparableStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCentralizer_localUnitary_comm_of_separable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a := by
  first | exact @GlobalTheory.BCT.centComm | exact GlobalTheory.BCT.centComm | (intros; apply GlobalTheory.BCT.centComm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerMassEqOfTopEquivStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedCentralizerMass_eq_of_topEquiv : ∀ (G G' : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] (θ : G →* G) (θ' : G' →* G') (Γ : Subgroup G) (Γ' : Subgroup G') (δ : G) (δ' : G'), IsClosed (twCent θ δ : Set G) → IsClosed (twCent θ' δ' : Set G') → ∀ (e : twCent θ δ ≃ₜ* twCent θ' δ'), (∀ t : twCent θ δ, (t : G) ∈ Γ ↔ ((e t : twCent θ' δ') : G') ∈ Γ') → mass θ Γ δ = mass θ' Γ' δ' := by
  first | exact @GlobalTheory.MassTor.mass_eq_of_equiv | exact GlobalTheory.MassTor.mass_eq_of_equiv | (intros; apply GlobalTheory.MassTor.mass_eq_of_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicatorStatement
section
open Filter GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedOrbitalIntegralSummand_goodPlace_indicator : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (KH : Subgroup H) (δ : H), δ ∈ KH → cptPart (twCent (MonoidHom.id H) δ) ≤ KH → (∀ g : H, g⁻¹ * δ * g ∈ KH → ∃ t ∈ twCent (MonoidHom.id H) δ, t⁻¹ * g ∈ KH) → ∀ x : H, GlobalTheory.TwOrbConj.summand (MonoidHom.id H) KH δ ((KH : Set H).indicator 1) x = if ∃ t ∈ twCent (MonoidHom.id H) δ, ∃ k ∈ KH, x = t * k then 1 else 0 := by
  first | exact @GlobalTheory.TwOrbGood.summand_goodplace | exact GlobalTheory.TwOrbGood.summand_goodplace | (intros; apply GlobalTheory.TwOrbGood.summand_goodplace <;> assumption)
end

