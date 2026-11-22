import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0022
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0100
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0031
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0079
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0085
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.DeltaDatumCombinedCoefficient
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0034
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AgreementOfOrders
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteSupportAdmissible
import ReciprocityTheory.SemistableReduction.Bundle0023

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsComponentLatticeMarkingAdelic
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.Occ

open GlobalTheory.AdLat GlobalTheory.AdLat.Half
open scoped nonZeroDivisors

theorem form_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (J : FractionalIdeal (𝓞 E)⁰ E) (g : Matrix (Fin n) (Fin n) (RA F E))
    (hL : ∀ x ∈ L, ∀ y ∈ L, (∑ a, ∑ b, x a * G a b * c (y b)) ∈ J)
    (hg : ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = hermA c G x y) {N : ℕ} (hN : 0 < N)
    {x y x' y' : Fin n → E} (hx : x ∈ L) (hy : y ∈ L) {w w' : Fin n → RA F E}
    (hw : w ∈ hat F (L : Set (Fin n → E))) (hw' : w' ∈ hat F (L : Set (Fin n → E)))
    (ex : fv F x' = g *ᵥ (fv F x + N • w)) (ey : fv F y' = g *ᵥ (fv F y + N • w')) :
    ∃ z ∈ J, (∑ a, ∑ b, x' a * G a b * c (y' b)) - (∑ a, ∑ b, x a * G a b * c (y b)) = N * z := by
  have back : ∀ w ∈ hat F (L : Set (Fin n → E)), ∀ y ∈ L,
      hermA c G w (fv F y) ∈ hat1 F (J : Set E) := by
    intro w hw y hy
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨t, ht, x, hx, rfl⟩ := hw
      rw [hermA_tmul_fv]
      exact AddSubgroup.subset_closure ⟨t, ht, _, hL x hx y hy, rfl⟩
    | zero =>
      have : hermA c G 0 (fv F y) = 0 := by simp [hermA]
      rw [this]; exact zero_mem _
    | add w w' _ _ h h' => rw [hermA_add_left]; exact add_mem h h'
    | neg w _ h => rw [hermA_neg_left]; exact neg_mem h
  have both : ∀ u ∈ hat F (L : Set (Fin n → E)), ∀ v ∈ hat F (L : Set (Fin n → E)),
      hermA c G u v ∈ hat1 F (J : Set E) := fun u hu v hv => herm_mem_of_fv c G _ _ _ (back u hu) v hv
  have hMs : ∀ x : Fin n → RA F E, N • x = (N : RA F E) • x := fun x =>
    (Nat.cast_smul_eq_nsmul _ _ _).symm
  have hsM : sg (FiniteAdeleRing (𝓞 F) F) c (N : RA F E) = N := map_natCast _ N
  have hfx := fv_mem_hat' (F := F) (L : Set (Fin n → E)) x hx
  have hfy := fv_mem_hat' (F := F) (L : Set (Fin n → E)) y hy
  have hu : hermA c G w (fv F y + N • w') + hermA c G (fv F x) w' ∈ hat1 F (J : Set E) :=
    add_mem (both _ hw _ (add_mem hfy (nsmul_mem hw' N))) (both _ hfx _ hw')
  have e1 : hermA c G (fv F x') (fv F y') - hermA c G (fv F x) (fv F y) =
      (N : RA F E) * (hermA c G w (fv F y + N • w') + hermA c G (fv F x) w') := by
    rw [ex, ey, hg, Half.herm_add_left, hMs w, Half.herm_smul_left, Half.herm_add_right c G (fv F x), hMs w',
      Half.herm_smul_right, hsM]
    ring
  have e2 : ∀ x y : Fin n → E, hermA c G (fv F x) (fv F y) =
      (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (∑ a, ∑ b, x a * G a b * c (y b)) :=
    fun x y => hermA_tmul_fv c G 1 x y
  rw [e2, e2, ← TensorProduct.tmul_sub] at e1
  set d := (∑ a, ∑ b, x' a * G a b * c (y' b)) - (∑ a, ∑ b, x a * G a b * c (y b)) with hd
  have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N : RA F E) = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E) :=
    (map_natCast (Algebra.TensorProduct.includeRight :
      E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E) N).symm
  refine ⟨(N : E)⁻¹ * d, ((adelicCompletion_fractionalIdeal_properties F E).2.1 J _).1 ?_, by rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]⟩
  have e3 : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((N : E)⁻¹ * d) : RA F E) =
      ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (N : E)⁻¹) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] d) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [e3, e1, hNt, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hN',
    ← Algebra.TensorProduct.one_def, one_mul]
  exact hu

theorem herm_neg' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : herm (-G) x y = -∑ a, ∑ b, x a * G a b * cc (y b) := by
  simp [herm]

theorem trace_swap {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (G : Matrix (Fin n) (Fin n) E)
    (hG : ∀ a b, cc (G a b) = G b a) (ξ : E) (hξ : cc ξ = -ξ) (x y : Fin n → E) :
    Algebra.trace ℚ E (ξ * -herm G y x) = Algebra.trace ℚ E (ξ * herm G x y) := by
  have h1 : cc (herm G x y) = herm G y x := by
    unfold herm
    unfold cc at *
    rw [Finset.sum_comm]
    simp only [map_sum, map_mul, hG, IsCMField.complexConj_apply_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have h2 := Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) (ξ * herm G x y)
  rw [← h2, ← h1]
  congr 1
  unfold cc at *
  change _ = IsCMField.complexConj E _
  rw [map_mul, hξ]
  ring

theorem mark_congr {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) (RA F E)) {N : ℕ} {x x' t w : Fin n → E} {w' : Fin n → RA F E}
    (e : A *ᵥ fv F x' = fv F (t + N • w)) (e' : fv F x' = B *ᵥ (fv F x + N • w')) :
    fv F t - (A * B) *ᵥ fv F x = N • ((A * B) *ᵥ w' - fv F w) := by
  rw [e', Matrix.mulVec_mulVec, Tower.fv_add, Tower.fv_nsmul, Matrix.mulVec_add, Tower.mulVec_nsmul] at e
  rw [smul_sub, sub_eq_sub_iff_add_eq_add, ← e, add_comm]

end GlobalTheory.Member.Occ

open GlobalTheory.Member.Occ GlobalTheory.AdLat in

theorem GlobalTheory.Member.exists_mark : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h : GA D V, ∃ k γ, C.Mark h k γ := by
  intro D H Dw l Xo c σ V r C hC h
  obtain ⟨hr, g, e, F, M, ι, θ, x₀⟩ := C
  subst hr
  obtain ⟨⟨-, -, ⟨hinj, hrange⟩, hisom⟩, -, hA, hgood, hbase, hW, -, -⟩ := hC
  dsimp only at hinj hrange hisom hbase hW
  obtain ⟨-, hfv, -, -, -, hcc, -, hGc, hGdet, hT, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨hfg1, hsp1, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  obtain ⟨hfg, hsp, hlat, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V h
  obtain ⟨hJ, hsd1, -⟩ := GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V 1 _ rfl
  obtain ⟨-, -, hsd⟩ := GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm D V h _ rfl
  obtain ⟨f, hf1, hf2, hf3⟩ := GlobalTheory.AdLat.exists_linear_approx_tower D.host.F D.host.E V.rank (latG V 1)
    (finHom V h) (latG V h) hfg1 hsp1 hlat
  let ε : Dw.La ≃ₗ[𝓞 D.host.E] latG V 1 :=
    (LinearEquiv.ofInjective ι hinj).trans (LinearEquiv.ofEq _ _ hrange)
  have hε : ∀ a, (ε a : Fin V.rank → D.host.E) = ι a := fun a => rfl
  have hk : ∀ k, (M.X k).Gm = -V.gramᵀ ∧ (M.X k).ξ0 = -D.host.xi0 := fun k => by
    obtain ⟨h1, h2⟩ := hW k
    exact ⟨by rw [h1]; rfl, h2⟩
  have hξ : cc D.host.xi0 = -D.host.xi0 := by
    have h := (M.X ⟨0, F.n_pos⟩).ξ0_im
    rw [(hk _).2] at h
    unfold cc at h ⊢
    rw [map_neg] at h
    exact neg_injective h
  have hG' : ∀ a b, cc ((-V.gramᵀ) a b) = (-V.gramᵀ) b a := fun a b => by
    rw [← hcc, Matrix.neg_apply, Matrix.neg_apply, map_neg, hGc]
  have hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) (ι x) (ι y)) := fun x y => by
    rw [hisom, hT, trace_swap _ hG' _ hξ, neg_neg]
  obtain ⟨k, γ', hu, hl, hm⟩ := GlobalTheory.selfDual_lattice_occurs GlobalTheory.QNorm.hasseNormSt D.host.E H Dw l Xo _ g _ F V.rank M
    (-D.host.xi0) (-V.gramᵀ) ι (latG V h) (fun N => f N ∘ₗ ε.toLinearMap) hA hgood
    ((GlobalTheory.Relab.relab_good D.host.E H l c σ hgood).2.2.2 Dw g e) hbase hk
    ⟨hinj, by rw [← LinearMap.coe_range, hrange]; exact hsp1, hG', by
      rw [Matrix.det_neg]; exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hGdet, hEF⟩ hfg hsp hsd
    (fun n m hn hm a => hf2 n m hn hm (ε a))
    (fun n hn => ⟨fun a => ((hf3 n hn).1 (ε a)).trans
      ⟨fun ⟨v, hv⟩ => ⟨ε.symm v, ε.injective (by rw [hv, map_nsmul, ε.apply_symm_apply])⟩,
        fun ⟨v, hv⟩ => ⟨ε v, by rw [hv, map_nsmul]⟩⟩, fun a' => by
      obtain ⟨a, v, hv⟩ := (hf3 n hn).2 a'
      exact ⟨ε.symm a, v, by simpa using hv⟩⟩)
    (fun n hn a a' => by
      obtain ⟨w, hw, ew⟩ := hf1 n hn (ε a)
      obtain ⟨w', hw', ew'⟩ := hf1 n hn (ε a')
      obtain ⟨z, hz, ez⟩ := form_congr (latG V 1) (cF D) V.gramᵀ _ _
        (fun x hx => (hsd1 x).2 hx) (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V h).1 hn (ε a).2 (ε a').2 hw hw' ew ew'
      obtain ⟨t, ht⟩ := (hJ z).1 hz 1
      refine ⟨-t, ?_⟩
      simp only [hcc, hε] at ez
      rw [hEF, ← map_sub, ← mul_sub, herm_neg', herm_neg', neg_sub_neg, ← neg_sub]
      erw [ez]
      have : -(-D.host.xi0) * -((n : D.host.E) * z) =
          (-(n : ℚ)) • (D.host.xi0 * (((1 : 𝓞 D.host.E) : D.host.E) * z)) := by
        simp [Algebra.smul_def]; ring
      rw [this, map_smul, ht]
      simp)
  obtain ⟨hQ, -, hex, -, hfin⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨γ, hγ⟩ := hex γ' hu
  obtain ⟨hmv, -⟩ := (GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V).1 γ γ' h hγ
  obtain ⟨-, -, -, hhat1, hhat2, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V (γ * h)
  have hΛ : ∀ v, v ∈ (M.X k).Λ ↔ v ∈ latG V (γ * h) := fun v => by
    have e : v = γ'.val *ᵥ ((γ'⁻¹).val *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [e, ← hl, ← hmv]
  refine ⟨k, γ, (hQ γ).2 ⟨γ', hγ⟩, ?_, fun a ha => ?_⟩
  · ext v
    constructor
    · intro hv
      exact ⟨v, (hΛ v).1 hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact (hΛ v).2 hv
  · obtain ⟨w, hw, ew⟩ := hm a ha
    obtain ⟨w', hw', ew'⟩ := hf1 l.M (lt_of_lt_of_le (by norm_num) l.three_le) (ε a)
    have m1 : (finHom V (γ * h)).1 *ᵥ w' ∈ latGHat V (γ * h) := by
      rw [← SetLike.mem_coe, hhat1]
      exact ⟨w', hw', rfl⟩
    have m2 : fv D.host.F w ∈ latGHat V (γ * h) := by
      rw [hhat2]
      exact Half.fv_mem_hat' _ _ ((hΛ w).1 hw)
    refine ⟨_, sub_mem m1 m2, ?_⟩
    have e1 := (hfin γ γ' hγ).1 (f l.M (ε a))
    have ew2 : γ'.val *ᵥ (f l.M (ε a) : Fin V.rank → D.host.E) =
        (M.φ k (F.t k a) : Fin V.rank → D.host.E) + l.M • w := ew
    rw [ew2] at e1
    have e2 := mark_congr (finHom V γ).1 (finHom V h).1 e1 ew'
    rw [← Units.val_mul, ← map_mul] at e2
    exact e2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HomExtOfGeometric
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient

namespace GlobalTheory.FrameFreeRule

theorem fnAt_comp {X Y : Scheme.{0}} {S : Type} [CommRing S] (y : Sp S ⟶ X) (g : X ⟶ Y) (f : Γ(Y, ⊤)) :
    fnAt (y ≫ g) f = fnAt y (g.appTop.hom f) := by
  simp only [fnAt, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]

theorem fnAt_spMap_comp {X : Scheme.{0}} {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T) (y : Sp S ⟶ X)
    (f : Γ(X, ⊤)) : fnAt (spMap φ ≫ y) f = φ (fnAt y f) := by
  rw [fnAt_comp]
  exact congrArg (fun q => q.hom (y.appTop.hom f)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

theorem fnAt_id {S : Type} [CommRing S] (a : S) :
    fnAt (𝟙 (Sp S)) ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom a) = a := by
  simp [fnAt]

theorem eq_zero_of_geometric {P : Scheme.{0}} [IsReduced P] (s : Γ(P, ⊤))
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ P), fnAt y s = 0) : s = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  let K := AlgebraicClosure (P.residueField x)
  let y : Sp K ⟶ P := spMap (algebraMap (P.residueField x) K) ≫ P.fromSpecResidueField x
  have h0 : y.appTop.hom s = 0 := by
    have := h K y
    unfold fnAt at this
    exact (map_eq_zero_iff _ (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective).1 this
  have h1 : y ⁻¹ᵁ P.basicOpen s = ⊥ := by
    rw [Scheme.preimage_basicOpen_top]
    erw [h0]
    exact Scheme.basicOpen_zero _ _
  have h2 : (default : Sp K) ∈ y ⁻¹ᵁ P.basicOpen s := by
    change y default ∈ P.basicOpen s
    have : y default = x := by
      simp only [y, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply _ _
    rwa [this]
  rw [h1] at h2
  exact h2

theorem hom_ext_of_geometric {P Y : Scheme.{0}} [IsReduced P] [IsAffine Y] (u v : P ⟶ Y)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ P), y ≫ u = y ≫ v) : u = v := by
  refine ext_of_isAffine ?_
  ext r
  rw [← sub_eq_zero]
  refine eq_zero_of_geometric _ fun K _ _ y => ?_
  have := congrArg (fun q => fnAt q r) (h K y)
  simp only [fnAt_comp] at this
  unfold fnAt at this ⊢
  rw [map_sub, map_sub, sub_eq_zero]
  exact this

theorem exists_glue {X : Scheme.{0}} [IsReduced X] {ι : Type} (A : ι → Type) [∀ i, CommRing (A i)]
    (j : ∀ i, Sp (A i) ⟶ X) [∀ i, IsOpenImmersion (j i)] (hcov : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (a : ∀ i, A i)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (i i' : ι) (χ : A i →+* K) (χ' : A i' →+* K),
      spMap χ ≫ j i = spMap χ' ≫ j i' → χ (a i) = χ' (a i')) :
    ∃ f : Γ(X, ⊤), ∀ i, fnAt (j i) f = a i := by
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers ι (fun i => Sp (A i)) j
    (fun x => by obtain ⟨i, y, hy⟩ := hcov x; exact ⟨i, y, hy⟩)
  let ev : ∀ i, Polynomial ℤ →+* A i := fun i => Polynomial.eval₂RingHom (Int.castRingHom _) (a i)
  let g : ∀ i, Sp (A i) ⟶ Sp (Polynomial ℤ) := fun i => spMap (ev i)
  have hg : ∀ i i', pullback.fst (j i) (j i') ≫ g i = pullback.snd (j i) (j i') ≫ g i' := by
    intro i i'
    have : IsReduced (pullback (j i) (j i')) :=
      isReduced_of_isOpenImmersion (pullback.fst (j i) (j i') ≫ j i)
    refine hom_ext_of_geometric _ _ fun K _ _ y => ?_
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (y ≫ pullback.fst (j i) (j i'))
    obtain ⟨χ', hχ'⟩ := Spec.map_surjective (y ≫ pullback.snd (j i) (j i'))
    have e := h K i i' χ.hom χ'.hom (by
      change Spec.map χ ≫ _ = Spec.map χ' ≫ _
      rw [hχ, hχ', Category.assoc, Category.assoc, pullback.condition])
    rw [← Category.assoc, ← Category.assoc, ← hχ, ← hχ']
    change spMap χ.hom ≫ spMap (ev i) = spMap χ'.hom ≫ spMap (ev i')
    rw [GlobalTheory.LocalFrame.spMap_spMap, GlobalTheory.LocalFrame.spMap_spMap]
    congr 1
    refine Polynomial.ringHom_ext (fun n => by simp) ?_
    simpa [ev] using e
  let G : X ⟶ Sp (Polynomial ℤ) := 𝒰.glueMorphisms g hg
  refine ⟨G.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv.hom Polynomial.X), fun i => ?_⟩
  have hi : j i ≫ G = g i := 𝒰.ι_glueMorphisms g hg i
  rw [← fnAt_comp, hi, ← Category.comp_id (g i), fnAt_spMap_comp, fnAt_id]
  simp [ev]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem evR_eq_of_chart (s : Rul Xo c) (hs : s ∈ sec Xo c 0 0)
    (hfree : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K),
      y'.x = y.x → evR Xo c s y' = evR Xo c s y)
    {A : Type} [CommRing A] [IsDomain A] [Algebra c.F A] (u : FrPt Xo c A)
    {K : Type} [Field K] [IsAlgClosed K] [Algebra c.F K] (χ : A →ₐ[c.F] K) (y : FrPt Xo c K)
    (hy : y.x = spMap χ.toRingHom ≫ u.x) : evR Xo c s y = χ (evR Xo c s u) := by
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c A K χ u
  rw [hfree K z y (hy.trans hz.1.symm)]
  have hT1 := GlobalTheory.TransferCompare.allTest_framed Xo c A u
  have hT2 := GlobalTheory.TransferCompare.allTest_framed Xo c K z
  unfold evR evalAt
  rw [dif_pos hT2, dif_pos hT1]
  exact GlobalTheory.TransferCompare.evalWD_framed Xo c s hs.1 K _ _ _ _ _ _ z hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ χ _ u z hT1.choose_spec.choose_spec.choose_spec hz)

theorem exists_fn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (s : Rul Xo c), s ∈ sec Xo c 0 0 → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y y' : FrPt Xo c K), y'.x = y.x → evR Xo c s y' = evR Xo c s y) → ∃ f : Γ(Xo.XF c, ⊤), ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K), evR Xo c s y = GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient.fnAt (GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient.basePt y) f := by
  intro E _ _ _ H D l Xo c s hs hfree
  choose A iA dA aA j u hj hp hsn _ hu using
    GlobalTheory.LocalFrame.exists_integral_chart_frame GlobalTheory.abelianSchemeLaws_all.2.secTwist E H D l Xo c
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsReduced (Xo.XF c) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd _ _)
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K) (p : Xo.XF c) (χ : A p →+* K),
      spMap χ ≫ j p = basePt y → evR Xo c s y = χ (evR Xo c s (u p)) := by
    intro K _ _ _ y p χ hχ
    have h1 : χ.comp (algebraMap c.F (A p)) = algebraMap c.F K := by
      have h2 : spMap (χ.comp (algebraMap c.F (A p))) = spMap (algebraMap c.F K) := by
        rw [← GlobalTheory.LocalFrame.spMap_spMap, ← hsn, ← Category.assoc, hχ]
        exact pullback.lift_snd _ _ _
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
    refine evR_eq_of_chart s hs hfree (u p) ⟨χ, fun r => RingHom.congr_fun h1 r⟩ y ?_
    change y.x = spMap χ ≫ _
    rw [hu, ← Category.assoc, hχ]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨f, hf⟩ := exists_glue A j (fun x => ⟨x, hp x⟩) (fun p => evR Xo c s (u p)) (by
    intro K _ _ p p' χ χ' hχ
    letI : Algebra c.F K := (χ.comp (algebraMap c.F (A p))).toAlgebra
    have hsn' : (spMap χ ≫ j p) ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := by
      rw [Category.assoc, hsn, GlobalTheory.LocalFrame.spMap_spMap]
    obtain ⟨y, hy⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed (c := c) ((spMap χ ≫ j p) ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hsn', sOf, GlobalTheory.LocalFrame.spMap_spMap])
    have hb : spMap χ ≫ j p = basePt y := by
      refine pullback.hom_ext ?_ ?_
      · rw [← hy]; exact (pullback.lift_fst _ _ _).symm
      · rw [hsn']; exact (pullback.lift_snd _ _ _).symm
    exact (key K y p χ hb).symm.trans (key K y p' χ' (hχ.symm.trans hb)))
  refine ⟨f, fun K _ _ _ y => ?_⟩
  let p : Xo.XF c := basePt y default
  have hr : Set.range (basePt y) ⊆ Set.range (j p) := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q default]
    exact hp p
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (IsOpenImmersion.lift (j p) (basePt y) hr)
  have hb : spMap χ.hom ≫ j p = basePt y := by
    change Spec.map χ ≫ _ = _
    rw [hχ, IsOpenImmersion.lift_fac]
  rw [key K y p χ.hom hb, ← hb, fnAt_spMap_comp, hf]

end GlobalTheory.FrameFreeRule
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LeastOrderBoundOfOrdTieTriv
section
noncomputable section

namespace GlobalTheory.TrivOrderTieCompare

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
  Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AgreementOfOrders

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem isClopen_comp (Z : Comp Xo c) : IsClopen (Z : Set (Xo.XF c)) := by
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have hZ : IsIrreducible (Z : Set (Xo.XF c)) := Z.2.1
  obtain ⟨z, hz⟩ := hZ.nonempty
  have h1 : (Z : Set (Xo.XF c)) ⊆ connectedComponent z :=
    hZ.isConnected.isPreconnected.subset_connectedComponent hz
  have h2 : IsIrreducible (connectedComponent z) :=
    ⟨⟨z, mem_connectedComponent⟩, GlobalTheory.KeyFam.isPreirreducible_connectedComponent_of_smooth (strK (Xo := Xo) (c := c)) z⟩
  rw [Set.Subset.antisymm h1 (Z.2.2 h2 h1)]
  exact ⟨isClosed_connectedComponent, isOpen_connectedComponent_of_noetherianSpace z⟩

def ReadsOrders (h : GenFrEx Xo c) (Z : Comp Xo c) (ord : WTZ E → AC Z → ℤ) (q : QPt Xo c) : Prop :=
  (∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f ≠ 0 →
    (((ord (wtZ a n) (valC h a n f Z) : ℤ) : ℝ) : EReal) = ordQ Xo c q f) ∧
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → evC h Z f = 0 → ordQ Xo c q f = ⊤

def TieOver (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (P : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Prop) : Prop :=
  ∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), P Z v → IsTrivOn c.F v →
    ∃ q : QPt Xo c, ReadsOrders h Z (ordC (δ Z v) v) q

variable [Fintype (Comp Xo c)]

abbrev CompData (Xo : Moduli Dw l) (c : Coeff l) [Fintype (Comp Xo c)] : Type :=
  Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)

def HasOrders (d : CompData Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) : Prop :=
  ∀ Z v, d.ord Z v = ordC (δ Z v) v

def dataWith (ord : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → WTZ E → AC Z → ℤ) (D N : ℕ)
    (w : Fin (N + 1) → ∀ Z : Comp Xo c, AC Z) : CompData Xo c where
  D := D
  N := N
  T := 0
  i := 0
  g0 := 0
  cc := 0
  wL := 0
  wF := 0
  wde := 0
  ord := ord
  nrm _ _ _ _ := 0
  M := ⊥
  WW := ⊥
  Thp := ⊥
  Th0 := ⊥
  Thk := ⊥
  w := w
  jc _ := 0
  np := 0
  thp := Fin.elim0
  n0 := 0
  th0 := Fin.elim0
  nk := 0
  thk := Fin.elim0
  et := 0
  ta1 := 0
  ta2 := 0
  nu _ := 0
  ip _ _ _ := 0
  wsize _ := 0
  DF := 0
  PN := 0
  PQ := 0
  tableDegreeThreeBase := 0
  PP0' := 0
  Pd := 0
  Gc := 0
  PI4 := 0
  Pet := 0
  tableLineDegreeFive := 0
  tableLineDegreeTwo := 0
  Prw := 0
  PO := 0
  f := 0
  r := 0

section Concrete

variable (h : GenFrEx Xo c)
    (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E)
    (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E)
    (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c)
    (nu : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) → ℝ)
    (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ)
    (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ)

end Concrete

end GlobalTheory.TrivOrderTieCompare
end
end

