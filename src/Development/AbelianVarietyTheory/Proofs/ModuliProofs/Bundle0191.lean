import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOfValFGeneric
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0062
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomogeneousVolumeVeryAmpleProducts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0003
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianVarietyCutOutBoundedDegreeTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_cut_out_bounded_degree_torsion : Out.Laws → Out.Laws2 → ∀ (g C : ℕ) (σ₀ : Type) [Finite σ₀] [Nonempty σ₀], ∃ d k₀ : ℕ, ∀ δ ≤ C ^ g, ∀ (σ : Type) [Finite σ] (r : σ → σ₀), Function.Surjective r → ∃ Q : Polynomial ℚ, ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), P.g = g → ∀ (Y : Scheme.{0}) (e : Y ≅ P.A.left) (M : LB Y) (th : σ → M.Sec) (k : ℕ) (Hh : Type) (y : Hh → (Out.baseOver (Sp K) ⟶ P.A)) (p : Hh → σ → K), M.IsLB → SymB (A := P.A) (M.pull e.inv) → VAmp (e.hom ≫ P.A.hom) M th → (∀ a a', r a = r a' → ∀ j, (th a).f j = (th a').f j) → (∀ n ≥ 1, SectionsHaveFiniteDimension (e.hom ≫ P.A.hom) (lbPow M n) (δ * n ^ g)) → k₀ ≤ k → (k : K) ≠ 0 → (∀ x : Out.baseOver (Sp K) ⟶ P.A, x ^ k = 1 → ∃ h, y h = x) → (∀ h, SecCoord M th ((y h).left ≫ e.inv) (p h)) → CutBy (idealOf (e.hom ≫ P.A.hom) M th (𝟙 Y)) Q d p := by
  first | exact @GlobalTheory.cutBy_idealOf_torsion | exact GlobalTheory.cutBy_idealOf_torsion | (intros; apply GlobalTheory.cutBy_idealOf_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeLineBundleAdjointIffHermFormAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (f f' : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)), u.IsAH Hm χ → IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → (LBIso (cubeLB P.A ![fst P.A P.A ≫ f, snd P.A P.A] P.L) (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ f'] P.L) ↔ ∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w)) := by
  first | exact @GlobalTheory.HermAdjoint.lbIso_cubeLB_iff_hermForm | exact GlobalTheory.HermAdjoint.lbIso_cubeLB_iff_hermForm | (intros; apply GlobalTheory.HermAdjoint.lbIso_cubeLB_iff_hermForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAmpFramesExponents
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem exists_ampFrames_of_cover (laws : Laws) {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens}
    {EE : M.Lat S.J} (Z : ZHOut ρ M U₀ EE) (hU₀ : (U₀ : Set M.Z).Nonempty) {I : Type} (U : I → M.Z.Opens) (x : I → S.Gam)
    (b : I → Matrix S.J S.J Ω) (r : ℤ) (u : I → Ω) (hu : ∀ i, u i = S.th (x i) ^ (r + Fintype.card S.J) / (b i).det)
    (hcov : ∀ z, ∃ i, z ∈ U i) (haff : ∀ i, IsAffineOpen (U i)) (hne : ∀ i, (U i : Set M.Z).Nonempty)
    (hb : ∀ i, (b i).det ≠ 0)
    (hx : ∀ i, ∀ z ∈ U i, x i ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range (b i)))
    (hreg : ∀ i j, ∀ z ∈ U i, u j / u i ∈ M.O z) (hconv : ∀ i j, ∀ z ∈ U i, u i / u j ∈ M.O z → z ∈ U j) :
    ∃ A : LN.AmpFrames Z.G Z.L.L S.N, A.r = r ∧ A.s = 1 := by
  have h0 : ∀ i, S.th (x i) ≠ 0 := fun i => (hx i _ (hne i).some_mem).1.1
  obtain ⟨g, hLB, hamp, hg⟩ := exists_ample M U u hcov haff hne
    (fun i => by rw [hu]; exact div_ne_zero (zpow_ne_zero _ (h0 i)) (hb i)) hreg hconv
  choose σ hσ gσ nσ using fun i => Z.theta (U i) (x i) fun z hz => (hx i z hz).1
  choose τ hτ nτ using fun i => Z.sections (U i) (x i) (b i) (hx i)
  let e : Fin (Fintype.card S.J) ≃ S.J := (Fintype.equivFin S.J).symm
  refine ⟨⟨LB.mk I U g, hLB, hamp, Fintype.card S.J, fun i => secOver Z.G 1 (hσ i) _ (fun t => t.2),
    fun i k => secOver Z.G S.N (hτ i (e k)).1 _ (fun t => t.2), r, 1, fun i j => ?_, fun i V _ _ _ hV χ hχ => ?_⟩, rfl, rfl⟩
  · have n₂ : ((U i ⊓ U j : M.Z.Opens) : Set M.Z).Nonempty := M.nonempty_inf (hne i) (hne j)
    obtain ⟨c, hc⟩ := exists_unit M n₂ (div_ne_zero (h0 j) (h0 i)) (fun z hz => (hx i z hz.1).1.2 _)
      (fun z hz => by rw [inv_div]; exact (hx j z hz.2).1.2 _)
    have reg : ∀ i j, ∀ z ∈ U i, z ∈ U j → ∀ k k',
        (((S.th (x j) / S.th (x i)) • (b i * (b j)⁻¹)).submatrix e e) k k' ∈ M.O z := fun i j z hi hj k k' =>
      (M.O z).mul_mem ((hx i z hi).1.2 _) ((mem_span_rows_iff (M.O z) (hb j) (b i (e k))).1
        ((hx j z hj).2 ▸ (hx i z hi).2 ▸ Submodule.subset_span ⟨e k, rfl⟩) (e k'))
    obtain ⟨m, hm⟩ := exists_GL M n₂ (A := ((S.th (x j) / S.th (x i)) • (b i * (b j)⁻¹)).submatrix e e)
      (A' := ((S.th (x i) / S.th (x j)) • (b j * (b i)⁻¹)).submatrix e e) (by
        rw [Matrix.submatrix_mul_equiv, smul_mul_smul_comm, div_mul_div_cancel₀ (h0 i), div_self (h0 j), one_smul,
          Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hb j).isUnit, Matrix.mul_nonsing_inv _ (hb i).isUnit,
          Matrix.submatrix_one_equiv])
      (fun z hz => reg i j z hz.1 hz.2) (fun z hz => reg j i z hz.2 hz.1)
    have one : valF M.pt (U i ⊓ U j) 1 = 1 := (M.res_apply _ n₂ 1).symm.trans (map_one _)
    refine ⟨Units.map (U i ⊓ U j).topIso.inv.hom.toMonoidHom c, Matrix.GeneralLinearGroup.map (U i ⊓ U j).topIso.inv.hom m,
      ⟨_, lin_secOver Z.G 1 (hσ i) (fun _ : Fin 1 => hσ i) inf_le_left inf_le_left (fun _ => 1)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_left (gσ i) (fun _ => gσ i) _ fun _ => by
            rw [Fin.sum_univ_one, one, _root_.one_mul]) _ _ (fun _ => (map_one _).symm),
        lin_secOver Z.G 1 (hσ i) (fun _ : Fin 1 => hσ j) inf_le_left inf_le_right (fun _ => c.val)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_right (gσ i) (fun _ => gσ j) _ fun _ => by
            rw [Fin.sum_univ_one, ← M.res_apply _ n₂, hc, div_mul_eq_mul_div, mul_inv_cancel₀ (h0 j), one_div])
          _ _ (fun _ => rfl)⟩,
      fun k => ⟨_, lin_secOver Z.G S.N (hτ i (e k)).1 (fun _ : Fin 1 => (hτ i (e k)).1) inf_le_left inf_le_left (fun _ => 1)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_left (hτ i (e k)).2 (fun _ => (hτ i (e k)).2) _ fun _ => by
            rw [Fin.sum_univ_one, one, _root_.one_mul]) _ _ (fun _ => (map_one _).symm),
        lin_secOver Z.G S.N (hτ i (e k)).1 (fun k' => (hτ j (e k')).1) inf_le_left inf_le_right (fun k' => m.val k k')
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_right (hτ i (e k)).2 (fun k' => (hτ j (e k')).2) _ fun l => ?_)
          _ _ (fun _ => rfl)⟩, ?_⟩
    · have v : ∀ k', valF M.pt (U i ⊓ U j) (m.val k k') = S.th (x j) / S.th (x i) * (b i * (b j)⁻¹) (e k) (e k') :=
        fun k' => (M.res_apply _ n₂ _).symm.trans (congrFun (congrFun hm k) k')
      have w : b i (e k) l = ∑ k', (b i * (b j)⁻¹) (e k) (e k') * b j (e k') l := by
        rw [e.sum_comp (fun a => (b i * (b j)⁻¹) (e k) a * b j a l), ← Matrix.mul_apply,
          Matrix.nonsing_inv_mul_cancel_right _ _ (hb j).isUnit]
      rw [w, Finset.sum_div]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [v]
      have := h0 i
      have := h0 j
      field_simp
    · have key : g i j = c ^ r * Matrix.GeneralLinearGroup.det m := by
        refine Units.ext (M.res_injective _ n₂ ((hg i j).trans (Eq.symm ?_)))
        have e₁ : M.res _ n₂ (c ^ r).val = (S.th (x j) / S.th (x i)) ^ r := by
          rw [← hc]
          exact (congrArg Units.val (map_zpow (Units.map (M.res _ n₂).toMonoidHom) c r)).trans (Units.val_zpow_eq_zpow_val _ _)
        rw [Units.val_mul, map_mul, e₁, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, hm,
          Matrix.det_submatrix_equiv_self, Matrix.det_smul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
          hu, hu, zpow_add₀ (h0 i), zpow_add₀ (h0 j), div_zpow, div_pow, zpow_natCast, zpow_natCast]
        have := h0 i
        have := h0 j
        have := hb i
        have := hb j
        field_simp
      show (U i ⊓ U j).topIso.inv.hom (g i j).val = _
      rw [key, zpow_one, Matrix.GeneralLinearGroup.map_det, ← map_zpow]
      exact map_mul _ _ _
  · let W₀ : M.Z.Opens := ⟨abLocus Z.G, by rw [Z.ab]; exact isOpen_TT_eq_bot S M⟩
    obtain ⟨ha, hk⟩ := Z.pol W₀ subset_rfl
    obtain ⟨A, φ, h₁, h₂, h₃⟩ := exists_polAV Z.G Z.semi S.g Z.dim Z.L Z.sym W₀ ha hk _ hχ
    have hr : ∀ {K : Type} [Field K] (y : Sp K ⟶ (U i).toScheme), Set.range (y ≫ (U i).ι) ⊆ U i := by
      rintro K _ y _ ⟨w, rfl⟩
      exact (y w).2
    refine ⟨GlobalTheory.basisAlong_of_independent_fibres laws M.Z Z.G Z.L.L 1 1 (Over.mk (U i).ι) _ Z.L.isLB Z.semi le_rfl (fun K _ _ y c H => ?_) V hV χ A φ
        h₁ h₂ (one_pow _).symm,
      GlobalTheory.basisAlong_of_independent_fibres laws M.Z Z.G Z.L.L S.N _ (Over.mk (U i).ι) _ Z.L.isLB Z.semi (one_le_two.trans S.N_ge)
        (fun K _ _ y c H => ?_) V hV χ A φ h₁ h₂ (ρ.card.trans (by rw [h₃]))⟩
    · obtain ⟨p, j, hp, hne⟩ := nσ i K _ (hr y)
      have := indep_secOver Z.G 1 (fun _ : Fin 1 => hσ i) y c H p j hp
      rw [Fin.sum_univ_one] at this
      exact funext fun a => by rw [Subsingleton.elim a 0]; exact (mul_eq_zero.1 this).resolve_right hne
    · have := (nτ i K _ (hr y)).2 (c ∘ e.symm) fun p j hp => by
        rw [← e.sum_comp]
        simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
          indep_secOver Z.G S.N (fun k => (hτ i (e k)).1) y c H p j hp
      exact funext fun a => by simpa using congrFun this (e a)

end GlobalTheory.AmpModel

namespace GlobalTheory

open AmpModel

theorem exists_ampFrames_exponents : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (n a : ℕ) (GG : Fin n → S.J → Ω) (Z : ZHOut ρ M U₀ EE), M.IsNm (fun q : S.Gam × (S.J → Fin n) => S.th q.1 * Matrix.det (Matrix.of fun i j => GG (q.2 i) j)) → S.Over₀ M U₀ → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω, w ∈ Submodule.span (M.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z) → ∃ r₀ : ℤ, ∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L S.N, A.r = r ∧ A.s = 1 := by
  intro laws o Ω _ _ _ _ S ρ M U₀ EE n a GG Z hN hO hdual
  let d : (S.J → Fin n) → Ω := fun k => Matrix.det (Matrix.of fun i j => GG (k i) j)
  let t : S.Gam × (S.J → Fin n) → Ω := fun q => S.th q.1 * d q.2
  refine ⟨1 + ((a : ℤ) - 1) * Fintype.card S.J, fun r hr => ?_⟩
  obtain ⟨e, rfl⟩ := Int.le.dest hr
  choose U haff hU _ using fun i : {q // t q ≠ 0} => hN.2 i.1 i.2
  have mem : ∀ i z, z ∈ U i ↔ M.Div t i.1 z := fun i z => Set.ext_iff.1 (hU i) z
  have h0 : ∀ i : {q // t q ≠ 0}, S.th i.1.1 ≠ 0 := fun i => left_ne_zero_of_mul i.2
  have hd : ∀ i : {q // t q ≠ 0}, d i.1.2 ≠ 0 := fun i => right_ne_zero_of_mul i.2
  have hth : ∀ i, ∀ z ∈ U i, i.1.1 ∈ S.supI M z := fun i z hz => ⟨h0 i, fun y => by
    have := ((mem i z).1 hz).2 (y, i.1.2)
    rwa [mul_div_mul_right _ _ (hd i)] at this⟩
  have hmin : ∀ i, ∀ z ∈ U i, ∀ k, d k / d i.1.2 ∈ M.O z := fun i z hz k => by
    have := ((mem i z).1 hz).2 (i.1.1, k)
    rwa [mul_div_mul_left _ _ (h0 i)] at this
  let B : {q // t q ≠ 0} → (S.J → Fin n) → Matrix S.J S.J Ω := fun i k => Matrix.of fun l j => GG (k l) j / S.th i.1.1 ^ a
  have hB : ∀ i k, (B i k).det = d k / (S.th i.1.1 ^ a) ^ Fintype.card S.J := fun i k => by
    have : B i k = (S.th i.1.1 ^ a)⁻¹ • Matrix.of fun l j => GG (k l) j := by
      ext l j
      simp [B, div_eq_inv_mul]
    rw [this, Matrix.det_smul, inv_pow, div_eq_inv_mul]
  have hB0 : ∀ i, (B i i.1.2).det ≠ 0 := fun i => by
    rw [hB]; exact div_ne_zero (hd i) (pow_ne_zero _ (pow_ne_zero _ (h0 i)))
  have hdet : ∀ i, ((B i i.1.2)⁻¹).transpose.det = (S.th i.1.1 ^ a) ^ Fintype.card S.J / d i.1.2 := fun i => by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hB, inv_div]
  have ratio : ∀ i j : {q // t q ≠ 0}, t j.1 * S.th j.1.1 ^ e / (t i.1 * S.th i.1.1 ^ e) =
      t j.1 / t i.1 * (S.th j.1.1 / S.th i.1.1) ^ e := fun i j => by rw [div_pow, div_mul_div_comm]
  refine exists_ampFrames_of_cover laws Z hO.ne U (fun i => i.1.1) (fun i => ((B i i.1.2)⁻¹).transpose) _
    (fun i => t i.1 * S.th i.1.1 ^ e) (fun i => ?_) (fun z => ?_) haff
    (fun i => ⟨_, (mem i _).2 (RatModel.div_genericPoint i.2)⟩) (fun i => ?_) (fun i z hz => ⟨hth i z hz, ?_⟩)
    (fun i j z hz => ?_) (fun i j z hz h => ?_)
  · have : 1 + ((a : ℤ) - 1) * Fintype.card S.J + e + Fintype.card S.J = ((1 + e + a * Fintype.card S.J : ℕ) : ℤ) := by
      push_cast; ring
    rw [hdet, this, zpow_natCast]
    have := h0 i
    have := hd i
    simp only [t]
    field_simp
    ring
  · obtain ⟨q, hq⟩ := hN.1 z
    exact ⟨⟨q, hq.1⟩, (mem _ z).2 hq⟩
  · rw [hdet]; exact div_ne_zero (pow_ne_zero _ (pow_ne_zero _ (h0 i))) (hd i)
  · obtain ⟨V, b, hzV, hb, hE⟩ := EE.loc z
    rw [hE z hzV]
    refine eq_span_dual (M.O z) hb (hB0 i) fun w => ?_
    rw [← hE z hzV, ← hdual z _ (hth i z hz) w]
    have dd : ∀ k, (Pi.basisFun Ω S.J).det ((fun k j => GG k j / S.th i.1.1 ^ a) ∘ k) = (B i k).det := fun k => by
      rw [Module.Basis.det_apply, ← Matrix.det_transpose]
      congr 1
    have := MaximalMinor.span_range_comp_eq (A := M.O z) (Pi.basisFun Ω S.J) (fun k j => GG k j / S.th i.1.1 ^ a)
      (σ := i.1.2) (mem_nonZeroDivisors_of_ne_zero (by rw [dd]; exact hB0 i)) fun k => by
        rw [dd, dd, hB, hB]
        refine Submodule.mem_span_singleton.2 ⟨⟨_, hmin i z hz k⟩, ?_⟩
        have := hd i
        show d k / d i.1.2 * _ = _
        field_simp
    exact SetLike.ext_iff.1 this w
  · rw [ratio]
    exact (M.O z).mul_mem (((mem i z).1 hz).2 _) (pow_mem ((hth i z hz).2 _) _)
  · rw [ratio] at h
    refine (mem j z).2 ⟨j.2, fun q => ?_⟩
    have := (M.O z).mul_mem ((M.O z).mul_mem (((mem i z).1 hz).2 q) h) (pow_mem ((hth i z hz).2 j.1.1) e)
    convert this using 1
    have := h0 i
    have := h0 j
    have := i.2
    have := j.2
    rw [div_pow, div_pow]
    field_simp

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEighthPowerPrincipalSiegelOfDense
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SharpFamily

theorem exists_isSharp_of_dense : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (em : o →+* ℂ) (S : Scheme.{0}) [IsLocallyNoetherian S] [IsReduced S] (s : S ⟶ Sp o) (t : TObj g k J b s), Odd k → Dense (fromSet em (SharpClass (b := b) W a bas em) t) → ∃ c : SiegPre h k (b.ζ : o) s, c.Principal ∧ IsSharp W a bas t c := by
  intro laws _ cube h g W J a bas hW hbas hunit k o _ b em S _ _ s t₀ hk hd₀
  obtain ⟨t, hd, back⟩ := GlobalTheory.T.dense_e8Sharp_after_adjoining_all_matrices h g W J a bas k o b em S s t₀ hunit hd₀
  obtain ⟨rmul, radd, rone, rpt⟩ := GlobalTheory.T.dense_fromSet_sharpClass h g W _ _ bas k o b em S s t hd
  obtain ⟨adj, diag⟩ := GlobalTheory.T.thetaLevel_adjoint_primitive_of_dense_eighth_powers laws.globalFns cube h g W _ _ bas k o b em S s t hd
  letI := t.ab.comm
  let ρ : Matrix (Fin 8) (Fin 8) ℤ → (t.A ⟶ t.A) := fun m => t.act (Sum.inr m)
  obtain ⟨A, _, pr, hA, hpr, hprod, hρ⟩ := GlobalTheory.T.abelianScheme_eighth_power_of_matrix_action S t.A ρ t.ab (fun m => t.hom _)
    (fun m m' => rmul (Sum.inr m) (Sum.inr m') (Sum.inr _) rfl) (fun m m' => radd (Sum.inr m) (Sum.inr m') (Sum.inr _) rfl)
    (rone (Sum.inr 1) rfl)
  letI := hA.comm
  obtain ⟨P, hP, r₁, r₂, hsym, hbi, hiso⟩ := GlobalTheory.T.exists_symmetric_biadditive_bundle_eighthPower W S t.A A pr t.L ρ hW hpr hprod t.isLB
    (cube S t.pol t.L t.isLB) hρ (fun m m' e => adj (Sum.inr m) (Sum.inr m') e) (fun m e => diag (Sum.inr m) e)
  let pt : Fin (2 * g) → (𝟙_ (Over S) ⟶ t.A) := fun i => Over.homMk (t.pt i).left (Over.w (t.pt i))
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A) := fun x =>
    (∏ i, pt i ^ bas.symm (Pi.single 0 x) i) ≫ pr 0
  have hadd : ∀ x y, lev (x + y) = lev x * lev y := fun x y => by
    have := hpr 0
    simp only [lev, Pi.single_add, map_add, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, MonObj.mul_comp]
  have hpt : ∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left := fun i u => by
    have e₁ : ρ (Matrix.single 0 u 1) ≫ pr 0 = pr u := by
      rw [hρ, List.prod_ofFn, Finset.prod_eq_single u] <;> simp +contextual [Matrix.single_apply, eq_comm]
    have e₂ := rpt (Sum.inr (Matrix.single 0 u 1)) i
    have e₃ : (fun u' => ∑ v, (Sum.elim a id (Sum.inr (Matrix.single 0 u 1)) : Matrix (Fin 8) (Fin 8) ℤ) u' v •
        bas (Pi.single i 1) v) = Pi.single 0 (bas (Pi.single i 1) u) := by
      funext u'
      by_cases hu : u' = 0
      · subst hu
        simp [Matrix.single_apply]
      · simp [Matrix.single_apply, hu, Ne.symm hu]
    rw [e₃, List.prod_ofFn] at e₂
    rw [← e₁, ← Category.assoc, e₂]
    rfl
  obtain ⟨htor, hgeo⟩ := GlobalTheory.T.level_on_factor_of_eighth_power_abelianScheme h g _ bas k o b S s t A pr lev hk.pos hpr hprod hadd hpt
  refine ⟨{ A := A, ab := hA, P := P, isLB := hP, rig₁ := r₁, rig₂ := r₂, symm := hsym, lev := lev, lev_add := hadd,
            lev_tors := htor, geom := fun K _ _ p β z hp hz => ⟨(hgeo K p).1, (hgeo K p).2, fun x y => ?_⟩ },
    ⟨GlobalTheory.T.relAmple_diagonal_biadditive_of_e8Form W S t.A A pr t.L P hW t.ab hA hpr hprod t.isLB hP hbi hiso t.ample,
      GlobalTheory.T.eq_one_of_biadditive_slice_trivial_eighthPower W S t.A A pr t.L P hpr hprod t.isLB hP hsym hbi hiso t.ktriv⟩,
    back _ ⟨pr, hpr, hprod, hiso, fun j u => ?_, hpt⟩⟩
  · have e : unitOn (z ^ (2 * omegaStd x y)) = unitOn z ^ (2 * omegaStd x y) := map_zpow (Units.map _) _ _
    rw [e]
    exact GlobalTheory.T.weilPairing_diagonal_bundle_of_eighthPower_form laws.globalFns h k W S t.A A pr t.L P K p (fun x => toUnit _ ≫ lev x) (unitOn z) hW t.ab hA
      hpr hprod t.isLB hP hsym hbi hiso (fun x y => by rw [hadd, MonObj.comp_mul])
      (fun x => by rw [← MonObj.comp_pow, htor, MonObj.comp_one])
      (GlobalTheory.T.commutatorPairing_e8Sharp_levelPoints laws h g W _ bas k o b S s t A pr lev hbas hpr hprod hadd hpt K p β z hp hz) x y
  · rw [rmul (Sum.inr (Sum.elim a id j)) (Sum.inr 1) j (_root_.mul_one _).symm, rone (Sum.inr 1) rfl, Category.id_comp]
    exact hρ _ u

end GlobalTheory.SharpFamily
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEmbeddingSectionsOverFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_embeddingSections_over_field : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (K : Type) [Field K] (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (m : ℕ) (w : Ix g (N' ^ 2) → K), m ^ 2 ∣ N' → 2 ≤ m → t.HasTh (𝟙 _) w → ∃ (σ : Ix g (N' ^ 2) → LB.Sec (Out.LPow t.A t.L ((m : ℤ) ^ 2) (Over.mk (𝟙 _)))), t.Emb m (Over.mk (𝟙 _)) σ ∧ ProjRep (idealOf (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ (𝟙 _)) (fst (Over.mk (𝟙 (Sp K))) t.A).left _ σ := by
  first | exact @GlobalTheory.ZM.EmbField.exists_emb_field | exact GlobalTheory.ZM.EmbField.exists_emb_field | (intros; apply GlobalTheory.ZM.EmbField.exists_emb_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHolomorphicThetaConstantsPolarisedLatticesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_thetaConstants_polarisedLattices : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (w w' : J) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (d : ℕ) (B : Set (Fin d → ℂ)) (Q : (Fin d → ℂ) → (La →+ (Fin g → ℂ))) (Hm : (Fin d → ℂ) → Matrix (Fin g) (Fin g) ℂ), Odd N' → Function.Bijective EF → IsOpen B → (∀ x, DifferentiableOn ℂ (fun bb => Q bb x) B) → (∀ bb ∈ B, (Function.Injective (Q bb) ∧ DiscreteTopology ((Q bb)).range ∧ Submodule.span ℝ (Set.range (Q bb)) = ⊤ ∧ ((Hm bb)).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (Hm bb) z z).re) ∧ ∀ x y, (hermForm (Hm bb) ((Q bb) x) ((Q bb) y)).im = EF x y) ∧ ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q bb x) = Q bb (ac w x)) → (∀ x, ac w x + ac w' x = x) → (∀ x y, EF (ac w x) y = EF x (ac w' y)) → ∃ θ : (Fin d → ℂ) → Ix g (N' ^ 2) → ℂ, (∀ a, DifferentiableOn ℂ (fun z => θ z a) B) ∧ ∀ bb ∈ B, ∀ t : TObj g (N' ^ 2) J b (spMap em), (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH (Hm bb) χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ ((Q bb)).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = (Q bb) x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((N' ^ 2 : ℕ) : ℂ)⁻¹ • (Q bb) (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F ((Q bb) x) = (Q bb) (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) → t.HasTh (𝟙 _) (θ bb) := by
  first | exact @GlobalTheory.exists_holomorphic_thetaConstants_of_family | exact GlobalTheory.exists_holomorphic_thetaConstants_of_family | (intros; apply GlobalTheory.exists_holomorphic_thetaConstants_of_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomogeneousVolumeVeryAmpleProductsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_volume_veryAmple_products : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (I : Type) [Fintype I] (φ : I → (P.A.left ⟶ P.A.left)) (r : ℕ) (ε : Fin r → I → ℤ), 1 ≤ r → (∀ k, ∃ (m : ℕ) (th : Fin (m + 1) → (LB.LinComb P.L φ (ε k)).Sec), VAmp P.A.hom _ th) → ∃ Φ : MvPolynomial (Fin r) ℚ, Φ.IsHomogeneous P.g ∧ ∀ n : Fin r → ℕ, (∀ k, 1 ≤ n k) → Vol P.A.hom (LB.LinComb P.L φ (fun i => ∑ k, (n k : ℤ) * ε k i)) P.g ((MvPolynomial.eval (fun k => (n k : ℚ)) Φ : ℚ) : ℝ) := by
  first | exact @GlobalTheory.VolPoly.exists_homogeneous_vol | exact GlobalTheory.VolPoly.exists_homogeneous_vol | (intros; apply GlobalTheory.VolPoly.exists_homogeneous_vol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfIsPeriod
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.Moduli

theorem exists_point_of_isPeriod : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)), (D'.p = D.p ∧ D'.q = D.q ∧ ∃ (f : ℕ → D.La →ₗ[𝓞 E] D'.La) (ν : ℕ → ℤ), (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - ν n * D.EF a a') ∧ σ (baseKA l).ζ = Complex.exp (-(2 * Real.pi * Complex.I) * (ν l.A : ℂ) / l.A) ∧ t = f l.M') → IsPeriod D' ty P → ∃ (y : Sp ℂ ⟶ Xo.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ Xo.univ.t.G)), (y ≫ Xo.s = spMap σ ∧ IsPeriod D' ty P ∧ ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ (∀ w, ∃! v : epsPt y ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt y ⟶ Xo.univ.t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧ (∀ z, e z = 1 ↔ z ∈ (P).range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ Xo.univ.t.act.act a) ∧ (∀ (k : ℕ) (a a₂ : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a a₂ : ℂ) / k) → Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (unitOn c)) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), toUnit _ ≫ Xo.univ.eta a = e ((l.M : ℂ)⁻¹ • P (t a))) ∧ ∀ a, toUnit _ ≫ Xo.univ.etaA a = e ((l.A : ℂ)⁻¹ • P (t a))) := by
  intro hT hL
  have hG : Out.GlobalFnsSt := hL.globalFns
  exact GlobalTheory.exists_point_of_period hT hL GlobalTheory.Moduli.cube_of_isLB GlobalTheory.principalTorus_algebraic
    (GlobalTheory.exists_isMonHom_of_map_lattice hT hL) (GlobalTheory.T.lambdaBundle_adjoint_of_weilPairing_adjoint hL)
    (GlobalTheory.PrimNorm.exists_primitive_normalisation hG) (GlobalTheory.kTriv_of_descent hL)
    GlobalTheory.relAmple_finite_pow_iso (GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel)

end GlobalTheory.Moduli
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPolFamOfGrpFam
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

theorem torsBasis_pow {G : Type} [CommGroup G] {r k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (y : Fin r → G)
    (hy : ∀ i, y i ^ (k * l) = 1)
    (h : ∀ z : G, z ^ (k * l) = 1 → ∃! c : Fin r → ZMod (k * l), ∏ i, y i ^ (c i).val = z)
    (z : G) (hz : z ^ k = 1) : ∃! c : Fin r → ZMod k, ∏ i, (y i ^ l) ^ (c i).val = z := by
  haveI : NeZero k := ⟨hk⟩
  have red : ∀ e : Fin r → ℕ, ∏ i, y i ^ ((e i : ZMod (k * l))).val = ∏ i, y i ^ e i := fun e =>
    Finset.prod_congr rfl fun i _ => by rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hy i)]
  have tor : ∀ e : Fin r → ℕ, (∏ i, y i ^ e i) ^ (k * l) = 1 := fun e => by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have inj : ∀ e e' : Fin r → ℕ, ∏ i, y i ^ e i = ∏ i, y i ^ e' i → ∀ i, e i ≡ e' i [MOD k * l] := by
    intro e e' he i
    have := (h _ (tor e)).unique (y₁ := fun i => (e i : ZMod (k * l))) (y₂ := fun i => (e' i : ZMod (k * l)))
      (red e) ((red e').trans he.symm)
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (congrFun this i)
  obtain ⟨c, hc, -⟩ := h z (by rw [pow_mul, hz, one_pow])
  have hd : ∀ i, l ∣ (c i).val := fun i => by
    have := inj (fun i => k * (c i).val) (fun _ => 0) (by
      simp only [pow_zero, Finset.prod_const_one]
      rw [← hz, ← hc, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]) i
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hk) ((Nat.modEq_zero_iff_dvd).1 this)
  choose d hd using hd
  refine ⟨fun i => (d i : ZMod k), ?_, fun c' hc' => funext fun i => ?_⟩
  · rw [← hc]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (by rw [← pow_mul, mul_comm, hy]), hd, pow_mul]
  · have := inj (fun i => l * (c' i).val) (fun i => l * d i) (by
      simp only [pow_mul, ← hd]
      rw [hc, ← hc']) i
    rw [mul_comm k l] at this
    have h2 := Nat.ModEq.mul_left_cancel' hl this
    rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]

variable {S : Scheme.{0}}

theorem torsBasis_pow_linComb {A T : Over S} [GrpObj A] [IsCommMonObj A] {r k l N : ℕ} (hN : N = k * l) (hN0 : N ≠ 0)
    (u : T ⟶ Out.baseOver S) (y : Fin r → (Out.baseOver S ⟶ A)) (hy : ∀ i, y i ^ N = 1)
    (h : ∀ z : T ⟶ A, z ^ N = 1 → ∃! c : Fin r → ZMod N, Out.linComb (fun i => u ≫ y i) (fun i => (c i).val) = z)
    (z : T ⟶ A) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ y i ^ l) (fun i => (c i).val) = z := by
  subst hN
  simp only [Out.linComb, List.prod_ofFn, MonObj.comp_pow] at h ⊢
  exact torsBasis_pow (left_ne_zero_of_mul hN0) (right_ne_zero_of_mul hN0) _
    (fun i => by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) h z hz

theorem exists_polFam_of_grpFam : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)), N' ≠ 0 → Odd m → m ∣ N' → DenseP (objPrimes b Mat κ β v) → GrpFam b Mat κ β v m A L act Q → ∃ L' : LB A.left, PolFam b Mat κ β v A L' act Q := by
  intro hL hL2 o _ g N' J b Mat κ R _ _ _ β v m A _ L act Q hN0 hodd ⟨l, hl⟩ hD ⟨hab, hsm, hlb, hamp, hlab, hfib⟩
  have hun : IsUnit (m : R) := by
    have := b.unit.map β
    rw [map_natCast, Nat.cast_pow, isUnit_pow_iff two_ne_zero, hl, Nat.cast_mul] at this
    exact isUnit_of_mul_isUnit_left this
  have := hab.comm
  obtain ⟨L', l1, l2, l3, l4, l5⟩ := GlobalTheory.OddDescent.exists_descended hL hL2 R A g m L
    (fun i => (Q i ^ l : Out.baseOver (Sp R) ⟶ A)) hab hsm hodd hun hlb hamp
    (fun i => by
      have e : l * m = N' := by rw [mul_comm, ← hl]
      have : (Q i ^ l) ^ m = 1 := by rw [← pow_mul, e, hlab.2.1]
      exact this)
    (fun K _ _ x => torsBasis_pow_linComb hl hN0 _ _ hlab.2.1 (hlab.2.2 K x))
    (fun r hr => hD r fun q hq hqp => hr q (by
      obtain ⟨K, _, _, x, s, t, hx, ht⟩ := mem_objPrimes.1 hq
      obtain ⟨ψ, hψ, hi⟩ := hfib K x s t ht
      exact ⟨K, inferInstance, inferInstance, x, t.pol, ψ, hx, hψ.1, hi⟩) hqp)
  refine ⟨L', hab, hsm, l1, l2, l3, l4, hlab, fun K _ _ x s t ht => ?_⟩
  obtain ⟨ψ, hψ, hi⟩ := hfib K x s t ht
  exact ⟨ψ, hψ, l5 K x t.pol ψ hψ.1 hi⟩

end GlobalTheory.ZM.NearBuild
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principallyPolarizedCM_extension_dvr : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp V)) [GrpObj A] (tK : SAB H (Sp K)) (φ : tK.G.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback tK.G A (spMap (algebraMap V K)) φ → Out.RelAmple tK.G tK.PP.L → Out.KTriv tK.G tK.PP.L → ∃ (t : SAB H (Sp V)) (ν : SABMap tK t (spMap (algebraMap V K))) (e : t.G ≅ A), ν.φ ≫ e.hom.left = φ ∧ IsMonHom e.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L := by
  first | exact @GlobalTheory.GoodPol.exists_sab_of_generic | exact GlobalTheory.GoodPol.exists_sab_of_generic | (intros; apply GlobalTheory.GoodPol.exists_sab_of_generic <;> assumption)
end

